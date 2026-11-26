module

public import LeanQbe.T.Amd64.VllFactorX645
public import LeanQbe.T.Main

/-!
# BedrockMach SysV x86-64 Lowering & `Fn.mid` Parity (`Amd64.VllFactorX646`)

Part 2b2 of the exact `asmX64List` lowering equality proof between `vllX64Isa` (`vllX64Target`)
and `x64Isa` (`x64Target`):
* Remaining `Rega` combinators (`abiTargets`, `abiSkips`, `jumpTargets`, `jumpLocOk`, `preEmpty`,
  `zeroMoveJump?`, `buildEntryBase`, `bindBlockParams`, `bindAbiParams`, `afterCallState`,
  `lowerStore`, `loadSextNext`, `lowerLoad`, `findJnzCond`, `jnzSetup`, `finishJnzBranch`,
  `lowerTail`, `deferJnzNext`, `deferLeaNext`, `blockTrampoline?`, `findGroupFwds`).
* Structural mutual parity (`lowerExpr_eq`, `lowerBlocks_eq`) under `hintsNoRsp` and
  `ExprNoSameExt` / `BlocksNoSameExt`.

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll
open Std Std.ExtHashMap

/-! ## 2b2. Remaining `Rega` Helpers, Entry/ABI Binders, Store/Load, and Jnz Lowering -/

private theorem list_all_congr' {α : Type} {p q : α → Bool} (hpq : ∀ a, p a = q a)
    (xs : List α) : xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.all_cons, hpq y, ih]

private theorem list_any_congr' {α : Type} {p q : α → Bool} (hpq : ∀ a, p a = q a)
    (xs : List α) : xs.any p = xs.any q := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.any_cons, hpq y, ih]

private theorem addrArg_beq_congr (a b : AddrArg Reg64) :
    @BEq.beq (AddrArg Reg64)
      (@instBEqOfDecidableEq (AddrArg Reg64) (@instDecidableEqAddrArg Reg64 vllX64IsaR.decEqReg))
      a b =
    @BEq.beq (AddrArg Reg64)
      (@instBEqOfDecidableEq (AddrArg Reg64) (@instDecidableEqAddrArg Reg64 x64Isa.decEqReg))
      a b := by
  by_cases h : a = b
  · exact (@decide_eq_true (a = b) (@instDecidableEqAddrArg Reg64 vllX64IsaR.decEqReg a b) h).trans
      (@decide_eq_true (a = b) (@instDecidableEqAddrArg Reg64 x64Isa.decEqReg a b) h).symm
  · exact (@decide_eq_false (a = b)
      (@instDecidableEqAddrArg Reg64 vllX64IsaR.decEqReg a b) h).trans
      (@decide_eq_false (a = b) (@instDecidableEqAddrArg Reg64 x64Isa.decEqReg a b) h).symm

private theorem mapOpt_or_congr {α β : Type} (f : α → β) {a₁ b₁ : Option α} {a₂ b₂ : Option β}
    (ha : a₁.map f = a₂) (hb : b₁.map f = b₂) : (a₁ <|> b₁).map f = (a₂ <|> b₂) := by
  cases a₁ with
  | none => subst ha; exact hb
  | some x => rw [← ha]; rfl

private theorem optLoc_beq_congr (d₁ d₂ : DecidableEq (Option (Loc Reg64 RegMm CondCode)))
    (a b : Option (Loc Reg64 RegMm CondCode)) :
    @BEq.beq (Option (Loc Reg64 RegMm CondCode)) (@instBEqOfDecidableEq _ d₁) a b =
    @BEq.beq (Option (Loc Reg64 RegMm CondCode)) (@instBEqOfDecidableEq _ d₂) a b :=
  decEq_beq_congr d₁ d₂ a b

private theorem optLoc_optionBeq_congr (d₁ d₂ : DecidableEq (Loc Reg64 RegMm CondCode))
    (a b : Option (Loc Reg64 RegMm CondCode)) :
    @BEq.beq (Option _) (@instBEqOption _ (@instBEqOfDecidableEq _ d₁)) a b =
    @BEq.beq (Option _) (@instBEqOption _ (@instBEqOfDecidableEq _ d₂)) a b := by
  cases a <;> cases b <;> first | rfl | exact decEq_beq_congr d₁ d₂ _ _

private theorem option_isSome_mapOptCl {α : Type} (o : Option (List (Instr x64Arch) × α)) :
    o.isSome = (mapOptCl o).isSome := by cases o <;> rfl

private theorem fun4_eq_none {α β γ δ ε : Type} (f : α → β → γ → δ → Option ε)
    (h : ∀ a b c d, f a b c d = none) : f = fun _ _ _ _ => none := by
  funext a b c d; exact h a b c d

private theorem entryScopeOk_eq (nv : Nat)
    (en : Entry x64Isa.Reg x64Isa.VReg x64Isa.Cond) :
    Rega.entryScopeOk (I := vllX64IsaR) nv en = Rega.entryScopeOk (I := x64Isa) nv en := rfl

private theorem regsNoRsp_nil : regsNoRsp [] = true := rfl

private theorem regsNoRsp_cons_loc {sa : SymArg} {r : Reg64} {R}
    (hr : locNoRsp (.gpr r) = true) (hR : regsNoRsp R = true) :
    regsNoRsp ((sa, .gpr r) :: R) = true :=
  Bool.and_eq_true_iff.mpr ⟨hr, hR⟩

private theorem regsNoRsp_cons_gprZ_loc {sa : SymArg} {r : Reg64} {R}
    (hr : (r != .rsp) = true) (hR : regsNoRsp R = true) :
    regsNoRsp ((sa, .gprZ r) :: R) = true :=
  Bool.and_eq_true_iff.mpr ⟨hr, hR⟩

private theorem locNoRsp_ne_rsp {r : Reg64} (h : locNoRsp (.gpr r) = true) : r ≠ .rsp := by
  intro e; subst e; cases h

private theorem trieAll_find_entry {h : x64Isa.Hints} (hh : hintsNoRsp h = true)
    {lid : Nat} {en : Entry Reg64 RegMm CondCode} (hf : h.entry.find? lid = some en) :
    entryNoRsp en = true :=
  trieAll_find? hh hf

theorem abiTargets_eq :
    ∀ {ts : List Ty} (args : Tup (Arg Rega.VNat) ts) (locs : Tup (AbiReg Reg64 RegMm) ts),
      Rega.abiTargets vllX64IsaR args locs = Rega.abiTargets x64Isa args locs
  | [], (), () => rfl
  | t :: _, (a, as), (loc, locs) => by
    dsimp only [Rega.abiTargets]
    rw [vllR_toSymArg_eq, abiTargets_eq as locs]
    cases Rega.toSymArg x64Isa t a with
    | none => rfl
    | some sa =>
      cases Rega.abiTargets x64Isa as locs with
      | none => rfl
      | some rest => cases loc <;> rfl

private theorem hasVarGpr_eq (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    (x : Nat) (r : Reg64) :
    Rega.hasVarGpr vllX64IsaR R x r = Rega.hasVarGpr x64Isa R x r := by
  dsimp only [Rega.hasVarGpr]
  exact list_any_congr' (fun p => congrArg (_ && ·) (regLocMatchesGpr_eq p.2 r)) R

private theorem abiHeld_eq (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode))
    (z : List Reg64) (t : Ty) (r : Reg64) (sa : SymArg) :
    Rega.abiHeld vllX64IsaR R z t r sa = Rega.abiHeld x64Isa R z t r sa := by
  cases sa with
  | var x =>
    dsimp only [Rega.abiHeld]
    rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg z r, hasVarGpr_eq,
      list_any_congr' (fun p => congrArg (_ && ·) (regLocEq_eq p.2 (.gprZ r))) R]
  | immBits _ c =>
    dsimp only [Rega.abiHeld]
    exact list_any_congr' (fun p => congrArg (_ && ·) (regLocMatchesGpr_eq p.2 r)) R
  | immBool b =>
    dsimp only [Rega.abiHeld]
    exact list_any_congr' (fun p => congrArg (_ && ·) (regLocMatchesGpr_eq p.2 r)) R
  | immVec _ _ => rfl

theorem abiSkips_eq (R : List (SymArg × Rega.RegLoc Reg64 RegMm CondCode)) (z : List Reg64) :
    ∀ {ts : List Ty} (args : Tup (Arg Rega.VNat) ts) (locs : Tup (AbiReg Reg64 RegMm) ts),
      Rega.abiSkips vllX64IsaR R z args locs = Rega.abiSkips x64Isa R z args locs
  | [], (), () => rfl
  | t :: _, (a, as), (loc, locs) => by
    dsimp only [Rega.abiSkips]
    rw [vllR_toSymArg_eq]
    cases loc with
    | vec _ => exact congrArg (false :: ·) (abiSkips_eq R z as locs)
    | gpr r =>
      cases Rega.toSymArg x64Isa t a with
      | none => exact congrArg (false :: ·) (abiSkips_eq R z as locs)
      | some sa =>
        dsimp only
        rw [abiHeld_eq, abiSkips_eq R z as locs]

theorem jumpTargets_eq :
    ∀ {ts : List Ty} (args : Tup (Arg Rega.VNat) ts) (locs : List (Loc Reg64 RegMm CondCode)),
      Rega.jumpTargets vllX64IsaR args locs = Rega.jumpTargets x64Isa args locs
  | [], (), [] => rfl
  | [], (), _ :: _ => rfl
  | _ :: _, _, [] => rfl
  | t :: _, (a, as), _ :: locs => by
    dsimp only [Rega.jumpTargets]
    rw [vllR_toSymArg_eq, jumpTargets_eq as locs]
    cases Rega.toSymArg x64Isa t a with
    | none => rfl
    | some sa => cases Rega.jumpTargets x64Isa as locs <;> rfl

theorem jumpLocOk_eq (nslots : Nat) (loc : Loc Reg64 RegMm CondCode) :
    Rega.jumpLocOk vllX64IsaR nslots loc = Rega.jumpLocOk x64Isa nslots loc := by
  cases loc with
  | gpr r =>
    dsimp only [Rega.jumpLocOk]
    rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg, vllR_scratch_eq]
  | vec v =>
    dsimp only [Rega.jumpLocOk]
    rw [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg, vllR_vecScratch_eq]
  | flag _ | slot _ _ => rfl

theorem zeroMoveJump?_eq {rs : List Ty} (h : x64Isa.Hints) (ip : Nat)
    (st : Rega.SymState vllX64IsaR) (e : Expr Rega.VNat Rega.LNat rs) :
    Rega.zeroMoveJump? vllX64IsaR h ip st e =
      Rega.zeroMoveJump? x64Isa h ip (symStToX64 st) e := by
  cases e with
  | jump j args =>
    dsimp only [Rega.zeroMoveJump?]
    have hpre : Rega.preEmpty (I := vllX64IsaR) h ip = Rega.preEmpty (I := x64Isa) h ip := by
      dsimp only [Rega.preEmpty]
      cases h.pre.find? ip <;> rfl
    rw [hpre]
    split
    · rfl
    · cases h.entry.find? j with
      | none => rfl
      | some en =>
        dsimp only [Option.bind]
        rw [jumpTargets_eq]
        cases Rega.jumpTargets x64Isa args en.ploc with
        | none => rfl
        | some argTgts =>
          dsimp only
          rw [list_all_congr' (fun p => by
            rw [jumpLocOk_eq, holdsLoc_eq]) (en.live ++ argTgts)]
  | _ => rfl

@[expose] def mapOptSymSt :
    Option (Rega.SymState vllX64IsaR) → Option (Rega.SymState x64Isa) :=
  Option.map symStToX64

theorem buildEntryBase_eq_and_noRsp (nslots : Nat) (vw : Trie SlotWidth) :
    ∀ (entries : List (SymArg × Loc Reg64 RegMm CondCode)) (st : Rega.SymState vllX64IsaR),
      entries.all (fun p => locNoRsp p.2) = true → regsNoRsp st.regs = true →
      mapOptSymSt (Rega.buildEntryBase vllX64IsaR nslots vw entries st) =
        Rega.buildEntryBase x64Isa nslots vw entries (symStToX64 st) ∧
      (∀ st', Rega.buildEntryBase vllX64IsaR nslots vw entries st = some st' →
        regsNoRsp st'.regs = true)
  | [], st, _, hno => ⟨rfl, fun _ h => by cases h; exact hno⟩
  | (sa, loc) :: rest, st, hent, hno => by
    simp only [List.all_cons, Bool.and_eq_true] at hent
    cases loc with
    | gpr r =>
      dsimp only [Rega.buildEntryBase]
      rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg, vllR_scratch_eq]
      split
      · exact buildEntryBase_eq_and_noRsp nslots vw rest _ hent.2
          (by exact regsNoRsp_cons_loc hent.1 hno)
      · exact ⟨rfl, fun _ h => by cases h⟩
    | vec v =>
      dsimp only [Rega.buildEntryBase]
      rw [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg, vllR_vecScratch_eq]
      split
      · exact buildEntryBase_eq_and_noRsp nslots vw rest _ hent.2
          (regsNoRsp_cons_vec hno)
      · exact ⟨rfl, fun _ h => by cases h⟩
    | flag _ =>
      exact buildEntryBase_eq_and_noRsp nslots vw rest _ hent.2 (regsNoRsp_cons_flag hno)
    | slot i w =>
      dsimp only [Rega.buildEntryBase]
      split
      · exact ⟨rfl, fun _ h => by cases h⟩
      · cases ha : Rega.addSlotEntry vw sa i w st.slots with
        | none => exact ⟨rfl, fun _ h => by cases h⟩
        | some slots' =>
          dsimp only [Option.bind]
          exact buildEntryBase_eq_and_noRsp nslots vw rest _ hent.2 hno

theorem bindBlockParams_eq_and_noRsp (nslots : Nat) :
    ∀ (ts : List Ty) (locs : List (Loc Reg64 RegMm CondCode)) (nv : Nat)
      (st : Rega.SymState vllX64IsaR),
      locs.all locNoRsp = true → regsNoRsp st.regs = true →
      mapOptSymSt (Rega.bindBlockParams vllX64IsaR nslots ts locs nv st) =
        Rega.bindBlockParams x64Isa nslots ts locs nv (symStToX64 st) ∧
      (∀ st', Rega.bindBlockParams vllX64IsaR nslots ts locs nv st = some st' →
        regsNoRsp st'.regs = true)
  | [], [], _, st, _, hno => ⟨rfl, fun _ h => by cases h; exact hno⟩
  | [], _ :: _, _, _, _, _ => ⟨rfl, fun _ h => by cases h⟩
  | _ :: _, [], _, _, _, _ => ⟨rfl, fun _ h => by cases h⟩
  | t :: ts, loc :: locs, nv, st, hlocs, hno => by
    simp only [List.all_cons, Bool.and_eq_true] at hlocs
    cases loc with
    | gpr r =>
      dsimp only [Rega.bindBlockParams]
      rw [list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg, vllR_scratch_eq,
        vllR_isGprTy_eq]
      split
      · exact bindBlockParams_eq_and_noRsp nslots ts locs (nv + 1) _ hlocs.2
          (by exact regsNoRsp_cons_loc hlocs.1 hno)
      · exact ⟨rfl, fun _ h => by cases h⟩
    | vec v =>
      dsimp only [Rega.bindBlockParams]
      rw [vllR_vecWidth?_eq]
      cases Rega.vecWidth? x64Isa t with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some w =>
        dsimp only [Option.bind]
        rw [list_contains_decEq_congr vllX64IsaR.decEqVReg x64Isa.decEqVReg, vllR_vecScratch_eq]
        split
        · exact bindBlockParams_eq_and_noRsp nslots ts locs (nv + 1) _ hlocs.2
            (regsNoRsp_cons_vec hno)
        · exact ⟨rfl, fun _ h => by cases h⟩
    | flag _ =>
      cases t with
      | bool =>
        exact bindBlockParams_eq_and_noRsp nslots ts locs (nv + 1) _ hlocs.2
          (regsNoRsp_cons_flag hno)
      | bits _ | float _ | pair _ _ => exact ⟨rfl, fun _ h => by cases h⟩
    | slot i w =>
      dsimp only [Rega.bindBlockParams]
      rw [vllR_isGprTy_eq, vllR_vecWidth?_eq]
      split
      · exact ⟨rfl, fun _ h => by cases h⟩
      · cases Rega.addSlotEntry _ (.var nv) i w st.slots with
        | none => exact ⟨rfl, fun _ h => by cases h⟩
        | some slots' =>
          dsimp only [Option.bind]
          exact bindBlockParams_eq_and_noRsp nslots ts locs (nv + 1) _ hlocs.2 hno

theorem bindAbiParams_eq_and_noRsp :
    ∀ {ts : List Ty} (locs : Tup (AbiReg Reg64 RegMm) ts) (nv : Nat)
      (st : Rega.SymState vllX64IsaR),
      locsNoRsp locs = true → regsNoRsp st.regs = true →
      mapOptSymSt (Rega.bindAbiParams vllX64IsaR locs nv st) =
        Rega.bindAbiParams x64Isa locs nv (symStToX64 st) ∧
      (∀ st', Rega.bindAbiParams vllX64IsaR locs nv st = some st' →
        regsNoRsp st'.regs = true)
  | [], (), _, st, _, hno => ⟨rfl, fun _ h => by cases h; exact hno⟩
  | t :: _, (loc, locs), nv, st, hlocs, hno => by
    cases loc with
    | gpr r =>
      simp only [locsNoRsp, Bool.and_eq_true] at hlocs
      dsimp only [Rega.bindAbiParams]
      rw [vllR_isGprTy_eq]
      split
      · cases Rega.tyEq t (.bits 32) with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact bindAbiParams_eq_and_noRsp locs (nv + 1) _ hlocs.2
            (regsNoRsp_cons_gprZ_loc hlocs.1 hno)
        | true =>
          simp only [↓reduceIte]
          have hk := bindAbiParams_eq_and_noRsp locs (nv + 1)
            { st with
              regs := (.var nv, .gprZ r) :: st.regs
              zeroExt32 :=
                r :: @Rega.killZeroExt vllX64IsaR.Reg vllX64IsaR.decEqReg [r] st.zeroExt32 }
            hlocs.2 (regsNoRsp_cons_gprZ_loc hlocs.1 hno)
          refine ⟨hk.1.trans ?_, hk.2⟩
          dsimp only [symStToX64]; rw [killZeroExt_eq]
      · exact ⟨rfl, fun _ h => by cases h⟩
    | vec v =>
      dsimp only [Rega.bindAbiParams]
      rw [vllR_vecWidth?_eq]
      cases Rega.vecWidth? x64Isa t with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some w =>
        dsimp only [Option.bind]
        exact bindAbiParams_eq_and_noRsp locs (nv + 1) _ hlocs (regsNoRsp_cons_vec hno)

theorem afterCallState_eq_and_noRsp (saved : List Reg64) (st : Rega.SymState vllX64IsaR)
    (hno : regsNoRsp st.regs = true) :
    symStToX64 (Rega.afterCallState vllX64IsaR saved st) =
      Rega.afterCallState x64Isa saved (symStToX64 st) ∧
    regsNoRsp (Rega.afterCallState vllX64IsaR saved st).regs = true := by
  refine ⟨?_, regsNoRsp_filter hno⟩
  dsimp only [Rega.afterCallState, symStToX64]
  congr 1
  exact List.filter_congr (fun p _ => by
    cases p.2 with
    | gpr _ | gprZ _ => exact list_contains_decEq_congr vllX64IsaR.decEqReg x64Isa.decEqReg saved _
    | vec _ | flag _ => rfl)

private theorem tryRmwHalf_eq (st : Rega.SymState vllX64IsaR) (vh : VariantHint) (n : Nat)
    (op : Rega.RmwOp) (x : Nat) (other : Arg Rega.VNat (.bits n)) (addr : Arg Rega.VNat i64)
    (hno : regsNoRsp st.regs = true) :
    mapOptCl (Rega.tryRmwHalf vllX64IsaR st vh n op x other addr) =
      Rega.tryRmwHalf x64Isa (symStToX64 st) vh n op x other addr := by
  dsimp only [Rega.tryRmwHalf, symStToX64]
  cases st.memDefs.find? x with
  | none => rfl
  | some p =>
    rcases p with ⟨ty, loadAddr⟩
    cases ty with
    | bits m =>
      dsimp only
      cases Nat.beq m n with
      | false => rfl
      | true =>
        simp only [↓reduceIte]
        refine mapOptCl_tryAddr st .default loadAddr hno fun aa1 _ =>
          mapOptCl_tryAddr st vh addr hno fun aa2 _ => ?_
        rw [addrArg_beq_congr]
        split
        · exact mapOptCl_tryArg st [] (.bits n) other fun pb => vllR_rmwMem_eq n _ aa1 pb
        · rfl
    | bool | float _ | pair _ _ => rfl

private theorem tryRmwStore_eq (st : Rega.SymState vllX64IsaR) (vh : VariantHint)
    (hno : regsNoRsp st.regs = true) :
    ∀ (t : Ty) (v : Arg Rega.VNat t) (addr : Arg Rega.VNat i64),
      mapOptCl (Rega.tryRmwStore vllX64IsaR st vh t v addr) =
        Rega.tryRmwStore x64Isa (symStToX64 st) vh t v addr
  | .bits n, .var y, addr => by
    dsimp only [Rega.tryRmwStore, symStToX64]
    split
    · rfl
    · cases st.defs.find? y with
      | none => rfl
      | some df =>
        dsimp only [Option.bind]
        cases Rega.rmwFact n df with
        | none => rfl
        | some p =>
          rcases p with ⟨op, x, rhs⟩
          dsimp only [Option.bind]
          refine mapOptCl_or_congr (tryRmwHalf_eq st vh n op x rhs addr hno) ?_
          split
          · cases rhs with
            | imm _ => rfl
            | var z => exact tryRmwHalf_eq st vh n op z (.var x) addr hno
          · rfl
  | .bits _, .imm _, _ | .bool, _, _ | .float _, _, _ | .pair _ _, _, _ => rfl

private theorem lowerStore_pair_wrap (st : Rega.SymState vllX64IsaR)
    {o₁ : Option (List (Instr x64Arch) × FlagMask)}
    {o₂ : Option (List _root_.Directive × FlagMask)} (ho : mapOptCl o₁ = o₂)
    (hk : ∀ cl : FlagMask, regsNoRsp (Rega.killRegs vllX64IsaR vllX64FrameR.scratch
      vllX64VecR.vecScratch cl st.regs) = true) :
    mapOptSt (o₁.map fun (c, clob) =>
      (c, { st with
        regs := Rega.killRegs vllX64IsaR vllX64FrameR.scratch vllX64VecR.vecScratch clob st.regs
        memDefs := .empty
        zeroExt32 := @Rega.killZeroExt vllX64IsaR.Reg vllX64IsaR.decEqReg
          vllX64FrameR.scratch st.zeroExt32
        flags := Rega.killFlags vllX64IsaR clob st.flags })) =
      (o₂.map fun (c, clob) =>
        (c, { symStToX64 st with
          regs := Rega.killRegs x64Isa x64Isa.frame.scratch x64Isa.vec.vecScratch clob st.regs
          memDefs := .empty
          zeroExt32 := @Rega.killZeroExt x64Isa.Reg x64Isa.decEqReg
            x64Isa.frame.scratch st.zeroExt32
          flags := Rega.killFlags x64Isa clob st.flags })) ∧
    (∀ c0 st', o₁.map (fun (c, clob) =>
      (c, { st with
        regs := Rega.killRegs vllX64IsaR vllX64FrameR.scratch vllX64VecR.vecScratch clob st.regs
        memDefs := .empty
        zeroExt32 := @Rega.killZeroExt vllX64IsaR.Reg vllX64IsaR.decEqReg
          vllX64FrameR.scratch st.zeroExt32
        flags := Rega.killFlags vllX64IsaR clob st.flags })) = some (c0, st') →
      regsNoRsp st'.regs = true) := by
  cases o₁ with
  | none => subst ho; exact ⟨rfl, fun _ _ h => by cases h⟩
  | some p =>
    rcases p with ⟨c, clob⟩
    subst ho
    dsimp only [mapOptCl, Option.map, mapOptSt, symStToX64]
    refine ⟨?_, fun _ _ h => by cases h; exact hk clob⟩
    rw [vllR_scratch_eq, vllR_vecScratch_eq, killRegs_eq, killZeroExt_eq, killFlags_eq]

theorem lowerStore_eq_and_noRsp (st : Rega.SymState vllX64IsaR) (vh : VariantHint) (t : Ty)
    (v : Arg Rega.VNat t) (addr : Arg Rega.VNat i64) (hno : regsNoRsp st.regs = true) :
    mapOptSt (Rega.lowerStore vllX64IsaR st vh t v addr) =
      Rega.lowerStore x64Isa (symStToX64 st) vh t v addr ∧
    (∀ c0 st', Rega.lowerStore vllX64IsaR st vh t v addr = some (c0, st') →
      regsNoRsp st'.regs = true) := by
  have hk_no : ∀ cl : FlagMask,
      regsNoRsp (Rega.killRegs vllX64IsaR vllX64FrameR.scratch vllX64VecR.vecScratch
        cl st.regs) = true := fun _ => regsNoRsp_killRegs _ hno
  have hk_no0 : ∀ cl : FlagMask,
      regsNoRsp (Rega.killRegs vllX64IsaR vllX64FrameR.scratch [] cl st.regs) = true :=
    fun _ => regsNoRsp_killRegs _ hno
  cases t with
  | pair a b =>
    dsimp only [Rega.lowerStore]
    refine lowerStore_pair_wrap st ?_ hk_no
    refine mapOptCl_tryArg st [] (.pair a b) v fun pa => ?_
    cases pa with
    | vec vs => exact mapOptCl_tryAddr st vh addr hno fun aa _ => vllR_vstore_eq _ vs aa
    | _ => rfl
  | bool | bits _ | float _ =>
    dsimp only [Rega.lowerStore]
    rw [vllR_isGprTy_eq]
    cases Rega.isGprTy x64Isa _ with
    | false => exact ⟨rfl, fun _ _ h => by cases h⟩
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hbody :
          mapOptCl
            ((Rega.tryArg vllX64IsaR st [] _ v fun pa =>
                Rega.tryAddr vllX64IsaR st vh addr (vllX64IsaR.gpr.store _ pa) <|>
                Rega.tryAddrZext vllX64IsaR st addr (vllX64IsaR.gpr.storeZextIdx _ pa)) <|>
              Rega.tryRmwStore vllX64IsaR st vh _ v addr) =
            ((Rega.tryArg x64Isa (symStToX64 st) [] _ v fun pa =>
                Rega.tryAddr x64Isa (symStToX64 st) vh addr (x64Isa.gpr.store _ pa) <|>
                Rega.tryAddrZext x64Isa (symStToX64 st) addr (x64Isa.gpr.storeZextIdx _ pa)) <|>
              Rega.tryRmwStore x64Isa (symStToX64 st) vh _ v addr) := by
        refine mapOptCl_or_congr (mapOptCl_tryArg st [] _ v fun pa => mapOptCl_or_congr
          (mapOptCl_tryAddr st vh addr hno fun aa haa => vllR_store_eq _ pa aa haa) ?_)
          (tryRmwStore_eq st vh hno _ v addr)
        have h1 :
            Rega.tryAddrZext vllX64IsaR st addr (vllX64IsaR.gpr.storeZextIdx _ pa) = none :=
          vllR_tryAddrZext_none st addr
        have h2 : Rega.tryAddrZext x64Isa (symStToX64 st) addr
            (x64Isa.gpr.storeZextIdx _ pa) = none := by
          rw [fun4_eq_none _ (x64_storeZextIdx_none _ pa)]
          exact x64_tryAddrZext_none (symStToX64 st) addr
        rw [h1, h2]; rfl
      cases ho :
          ((Rega.tryArg vllX64IsaR st [] _ v fun pa =>
              Rega.tryAddr vllX64IsaR st vh addr (vllX64IsaR.gpr.store _ pa) <|>
              Rega.tryAddrZext vllX64IsaR st addr (vllX64IsaR.gpr.storeZextIdx _ pa)) <|>
            Rega.tryRmwStore vllX64IsaR st vh _ v addr) with
      | none =>
        have hox :
            ((Rega.tryArg x64Isa (symStToX64 st) [] _ v fun pa =>
                Rega.tryAddr x64Isa (symStToX64 st) vh addr (x64Isa.gpr.store _ pa) <|>
                Rega.tryAddrZext x64Isa (symStToX64 st) addr (x64Isa.gpr.storeZextIdx _ pa)) <|>
              Rega.tryRmwStore x64Isa (symStToX64 st) vh _ v addr) = none := by
          rw [← hbody, ho]; rfl
        rw [hox]; exact ⟨rfl, fun _ _ h => by cases h⟩
      | some p =>
        rcases p with ⟨c, clob⟩
        have hox :
            ((Rega.tryArg x64Isa (symStToX64 st) [] _ v fun pa =>
                Rega.tryAddr x64Isa (symStToX64 st) vh addr (x64Isa.gpr.store _ pa) <|>
                Rega.tryAddrZext x64Isa (symStToX64 st) addr (x64Isa.gpr.storeZextIdx _ pa)) <|>
              Rega.tryRmwStore x64Isa (symStToX64 st) vh _ v addr) =
              some (asmX64List c, clob) := by
          rw [← hbody, ho]; rfl
        rw [hox]
        dsimp only [Option.map, mapOptSt, symStToX64]
        refine ⟨?_, fun _ _ h => by cases h; exact hk_no0 clob⟩
        rw [vllR_scratch_eq, killRegs_eq, killZeroExt_eq, killFlags_eq]

private theorem resolveDsts_eq_uncond (h : x64Isa.Hints) :
    ∀ (ts : List Ty) (nv : Nat),
      Rega.resolveDsts vllX64IsaR h ts nv = Rega.resolveDsts x64Isa h ts nv
  | [], _ => rfl
  | t :: ts, nv => by
    dsimp only [Rega.resolveDsts]
    rw [resolveDsts_eq_uncond h ts (nv + 1)]
    cases h.dest.find? nv with
    | none => rfl
    | some loc =>
      cases Rega.resolveDsts x64Isa h ts (nv + 1) with
      | none => cases loc <;> rfl
      | some rest =>
        cases loc with
        | gpr r => dsimp only; rw [vllR_isAllocGpr_eq, vllR_isGprTy_eq]
        | vec v => dsimp only; rw [vllR_isAllocVec_eq, vllR_vecWidth?_eq]
        | flag _ | slot _ _ => rfl

theorem fusesLoad_eq {ts : List Ty} (h : x64Isa.Hints) (st : Rega.SymState vllX64IsaR)
    (nv' ip' : Nat) (op : Op Rega.VNat ts) (hno : regsNoRsp st.regs = true) :
    Rega.fusesLoad vllX64IsaR h st nv' ip' op =
      Rega.fusesLoad x64Isa h (symStToX64 st) nv' ip' op := by
  dsimp only [Rega.fusesLoad]
  cases h.pre.find? ip' <;> try rfl
  dsimp only [Option.isNone, Bool.true_and]
  cases h.elide.getD ip' false <;> try rfl
  rw [resolveDsts_eq_uncond h ts nv']
  cases Rega.resolveDsts x64Isa h ts nv' with
  | none => rfl
  | some dsts =>
    dsimp only
    rw [option_isSome_mapOptCl (Rega.tryFuseCmp vllX64IsaR st _ op.code op.args dsts),
      tryFuseCmp_eq st _ op.code op.args dsts hno,
      option_isSome_mapOptCl (Rega.tryLoadSext vllX64IsaR st _ op.code op.args dsts),
      tryLoadSext_eq st _ op.code op.args dsts hno]

private theorem jumpAvoids_eq {rs : List Ty} (h : x64Isa.Hints) (x : Nat)
    (e : Expr Rega.VNat Rega.LNat rs) :
    Rega.jumpAvoids (I := vllX64IsaR) h x e = Rega.jumpAvoids (I := x64Isa) h x e := by
  cases e with
  | jump j _ => dsimp only [Rega.jumpAvoids]; cases h.entry.find? j <;> rfl
  | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _
  | hlt | group _ _ => rfl

theorem loadSextNext_eq {rs : List Ty} (h : x64Isa.Hints) (nv ip : Nat)
    (st : Rega.SymState vllX64IsaR) (t : Ty) (a : Arg Rega.VNat i64)
    (e : Expr Rega.VNat Rega.LNat rs) (hno : regsNoRsp st.regs = true) :
    Rega.loadSextNext vllX64IsaR h nv ip st t a e =
      Rega.loadSextNext x64Isa h nv ip (symStToX64 st) t a e := by
  dsimp only [Rega.loadSextNext]
  rw [vllR_isGprTy_eq]
  cases Rega.isGprTy x64Isa t with
  | false => rfl
  | true =>
    have hst' : regsNoRsp { st with memDefs := st.memDefs.insert nv (t, a) }.regs = true := hno
    cases e with
    | let_ op k =>
      dsimp only [symStToX64]
      rw [fusesLoad_eq h _ (nv + 1) (ip + 1) op hst']
      refine congrArg (fun b => true && b) (congr (congrArg (· || ·) ?_) ?_)
      · cases Rega.sextVar? op.code op.args with
        | none => rfl
        | some _ =>
          dsimp only
          first | rw [optLoc_optionBeq_congr _ _] | rw [optLoc_beq_congr _ _]
      · cases Rega.cmpVarImm? op.code op.args == some nv with
        | false => rfl
        | true =>
          cases h.dest.find? (nv + 1) with
          | none => rfl
          | some loc => cases loc with
            | gpr _ | vec _ | slot _ _ => rfl
            | flag _ =>
              dsimp only [Bool.true_and]
              split
              · rename_i cx tt ee _heq
                cases Rega.fusesLoad x64Isa h { symStToX64 st with
                    memDefs := st.memDefs.insert nv (t, a) } (nv + 1) (ip + 1) op with
                | false => rfl
                | true =>
                  rw [jumpAvoids_eq h nv tt, jumpAvoids_eq h nv ee]
                  refine congrArg
                    (fun b => Nat.beq cx (nv + 1) && (h.pre.find? (ip + 2)).isNone && b)
                    (congr (congrArg (· || ·)
                        (congrArg (fun b => Rega.jumpAvoids (I := x64Isa) h nv tt && b) ?_))
                      (congrArg (fun b => Rega.jumpAvoids (I := x64Isa) h nv ee && b) ?_))
                  · cases ee with
                    | let_ opE _ =>
                      dsimp only
                      cases Rega.sextVar? opE.code opE.args with
                      | none => rfl
                      | some _ =>
                        dsimp only
                        first | rw [optLoc_optionBeq_congr _ _] | rw [optLoc_beq_congr _ _]
                        rw [fusesLoad_eq h _ (nv + 2) (ip + 3) opE hst']
                    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _
                    | ret _ | exit _ _ | hlt | group _ _ => rfl
                  · cases tt with
                    | let_ opT _ =>
                      dsimp only
                      cases Rega.sextVar? opT.code opT.args with
                      | none => rfl
                      | some _ =>
                        dsimp only
                        first | rw [optLoc_optionBeq_congr _ _] | rw [optLoc_beq_congr _ _]
                        rw [fusesLoad_eq h _ (nv + 2) (ip + 4) opT hst']
                    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _
                    | ret _ | exit _ _ | hlt | group _ _ => rfl
              · simp only [Bool.and_false]
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _
    | hlt | group _ _ => rfl

theorem lowerLoad_eq_and_noRsp (h : x64Isa.Hints) (hs : savedNoRsp h.saved = true)
    (nv ip : Nat) (st : Rega.SymState vllX64IsaR) (t : Ty) (a : Arg Rega.VNat i64)
    (fuse : Bool) (hno : regsNoRsp st.regs = true) :
    mapOptSt (Rega.lowerLoad vllX64IsaR h nv ip st t a fuse) =
      Rega.lowerLoad x64Isa h nv ip (symStToX64 st) t a fuse ∧
    (∀ c0 st', Rega.lowerLoad vllX64IsaR h nv ip st t a fuse = some (c0, st') →
      regsNoRsp st'.regs = true) := by
  dsimp only [Rega.lowerLoad]
  cases h.elide.getD ip false || fuse with
  | true =>
    rw [vllR_isGprTy_eq]
    cases Rega.isGprTy x64Isa t with
    | false => exact ⟨rfl, fun _ _ h0 => by cases h0⟩
    | true =>
      dsimp only [mapOptSt, Option.map_some, symStToX64]
      exact ⟨rfl, fun _ _ h0 => by cases h0; exact hno⟩
  | false =>
    cases h.dest.find? nv with
    | none => exact ⟨rfl, fun _ _ h0 => by cases h0⟩
    | some loc => cases loc with
      | flag _ | slot _ _ => exact ⟨rfl, fun _ _ h0 => by cases h0⟩
      | gpr d =>
        dsimp only
        rw [vllR_isAllocGpr_eq, vllR_isGprTy_eq]
        cases hok : Rega.isAllocGpr x64Isa h.saved d && Rega.isGprTy x64Isa t with
        | false => exact ⟨rfl, fun _ _ h0 => by cases h0⟩
        | true =>
          have hd : d ≠ .rsp :=
            isAllocGpr_ne_rsp hs (by rw [vllR_isAllocGpr_eq]; exact (Bool.and_eq_true_iff.mp hok).1)
          have hbody :
              mapOptCl (Rega.tryAddr vllX64IsaR st (h.variant.getD ip .default) a
                  (vllX64IsaR.gpr.load t d) <|>
                Rega.tryAddrZext vllX64IsaR st a (vllX64IsaR.gpr.loadZextIdx t d)) =
              (Rega.tryAddr x64Isa (symStToX64 st) (h.variant.getD ip .default) a
                  (x64Isa.gpr.load t d) <|>
                Rega.tryAddrZext x64Isa (symStToX64 st) a (x64Isa.gpr.loadZextIdx t d)) := by
            refine mapOptCl_or_congr
              (mapOptCl_tryAddr st _ a hno fun aa haa => vllR_load_eq t d aa haa) ?_
            have h1 : Rega.tryAddrZext vllX64IsaR st a (vllX64IsaR.gpr.loadZextIdx t d) = none :=
              vllR_tryAddrZext_none st a
            have h2 : Rega.tryAddrZext x64Isa (symStToX64 st) a
                (x64Isa.gpr.loadZextIdx t d) = none := by
              rw [fun4_eq_none _ (x64_loadZextIdx_none t d)]
              exact x64_tryAddrZext_none (symStToX64 st) a
            rw [h1, h2]; rfl
          cases ho : Rega.tryAddr vllX64IsaR st (h.variant.getD ip .default) a
              (vllX64IsaR.gpr.load t d) <|>
              Rega.tryAddrZext vllX64IsaR st a (vllX64IsaR.gpr.loadZextIdx t d) with
          | none =>
            have hox :
                (Rega.tryAddr x64Isa (symStToX64 st) (h.variant.getD ip .default) a
                    (x64Isa.gpr.load t d) <|>
                  Rega.tryAddrZext x64Isa (symStToX64 st) a
                    (x64Isa.gpr.loadZextIdx t d)) = none := by rw [← hbody, ho]; rfl
            rw [hox]; exact ⟨rfl, fun _ _ h0 => by cases h0⟩
          | some p =>
            rcases p with ⟨c, clob⟩
            have hox :
                (Rega.tryAddr x64Isa (symStToX64 st) (h.variant.getD ip .default) a
                    (x64Isa.gpr.load t d) <|>
                  Rega.tryAddrZext x64Isa (symStToX64 st) a
                    (x64Isa.gpr.loadZextIdx t d)) = some (asmX64List c, clob) := by
              rw [← hbody, ho]; rfl
            rw [hox]
            dsimp only [Option.map, mapOptSt, symStToX64]
            refine ⟨?_, fun _ _ h0 => by
              cases h0
              cases vllX64GprR.zeroExtLoad ||
                  (vllX64GprR.zeroUpper32Load && Rega.tyEq t (.bits 32)) with
              | false => exact regsNoRsp_cons_gpr hd (regsNoRsp_killRegs _ hno)
              | true => exact regsNoRsp_cons_gprZ hd (regsNoRsp_killRegs _ hno)⟩
            rw [vllR_zeroUpper32Load_eq, vllR_zeroExtLoad_eq, vllR_scratch_eq,
              killZeroExt_eq, killRegs_eq, killFlags_eq]
            cases (x64Isa.gpr.zeroUpper32Load && Rega.tyEq t (.bits 32)) <;>
              cases x64Isa.gpr.zeroExtLoad <;> first | exact rfl |
                (dsimp only [vllX64IsaR, x64Isa]; rw [vllX64_zeroExtLoad_eq, vllX64_scratch_eq] <;>
                 try rfl)
      | vec vd =>
        dsimp only
        rw [vllR_vecWidth?_eq]
        cases Rega.vecWidth? x64Isa t with
        | none => exact ⟨rfl, fun _ _ h0 => by cases h0⟩
        | some w =>
          dsimp only [Option.bind]
          rw [vllR_isAllocVec_eq]
          cases Rega.isAllocVec x64Isa vd with
          | false => exact ⟨rfl, fun _ _ h0 => by cases h0⟩
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            have hbody := mapOptCl_tryAddr st (h.variant.getD ip .default) a hno
              fun aa _ => vllR_vload_eq t vd aa
            cases ho : Rega.tryAddr vllX64IsaR st (h.variant.getD ip .default) a
                (vllX64IsaR.vec.vload t vd) with
            | none =>
              have hox : Rega.tryAddr x64Isa (symStToX64 st) (h.variant.getD ip .default) a
                  (x64Isa.vec.vload t vd) = none := by rw [← hbody, ho]; rfl
              rw [hox]; exact ⟨rfl, fun _ _ h0 => by cases h0⟩
            | some p =>
              rcases p with ⟨c, clob⟩
              have hox : Rega.tryAddr x64Isa (symStToX64 st) (h.variant.getD ip .default) a
                  (x64Isa.vec.vload t vd) = some (asmX64List c, clob) := by
                rw [← hbody, ho]; rfl
              rw [hox]
              dsimp only [Option.map, mapOptSt, symStToX64]
              refine ⟨?_, fun _ _ h0 => by
                cases h0; exact regsNoRsp_cons_vec (regsNoRsp_killRegs _ hno)⟩
              rw [vllR_scratch_eq, vllR_vecScratch_eq, killRegs_eq, killZeroExt_eq, killFlags_eq]

@[expose] def mapJnzCond : Rega.JnzCond vllX64IsaR → Rega.JnzCond x64Isa
  | .flag cc => .flag cc
  | .gpr r => .gpr r
  | .slot i => .slot i
  | .cmpZero co w r => .cmpZero co w r
  | .cmpZeroMem co w x a cc => .cmpZeroMem co w x a cc
  | .cmpZeroFlag co w x r cc => .cmpZeroFlag co w x r cc
  | .testImm neg w r m => .testImm neg w r m

private theorem cmpZeroFlagCond?_eq (defs : Trie Rega.DefFact) (fl : Option Rega.FlagFact)
    (co : CmpOp) (w y : Nat) :
    Rega.cmpZeroFlagCond? vllX64IsaR defs fl co w y =
      Rega.cmpZeroFlagCond? x64Isa defs fl co w y := by
  cases fl with
  | none => rfl
  | some f =>
    cases f with
    | cmp w' lhs rhs eqNe =>
      dsimp only [Rega.cmpZeroFlagCond?]
      rw [reuseCmpPair?_eq]
      cases Rega.reuseCmpPair? x64Isa defs w' lhs rhs w co (.var y) (.imm 0#w) with
      | none => rfl
      | some p =>
        dsimp only [Option.bind_some]
        split
        · dsimp only [Option.bind_some]
          split <;> first | rfl | exact congrFun vllR_condOfCmp_eq _
        · split
          · dsimp only [Option.bind_some]
            split <;> first | rfl | exact congrFun vllR_condOfCmp_eq _
          · rfl

private theorem mapOpt_tryAddr {α β : Type} (f : α → β) (st : Rega.SymState vllX64IsaR)
    (vh : VariantHint) (a : Arg Rega.VNat i64)
    {k₁ : AddrArg Reg64 → Option α} {k₂ : AddrArg Reg64 → Option β}
    (hk : ∀ aa, (k₁ aa).map f = k₂ aa) :
    (Rega.tryAddr vllX64IsaR st vh a k₁).map f =
      Rega.tryAddr x64Isa (symStToX64 st) vh a k₂ := by
  cases a with
  | imm c =>
    dsimp only [Rega.tryAddr, symStToX64]
    refine mapOpt_or_congr f (hk (.imm c)) ?_
    rw [findGprFor_eq]
    cases Rega.findGprFor x64Isa true st.regs (.immBits 64 c) with
    | none => rfl
    | some r => dsimp only [Option.bind]; exact hk (.baseDisp r 0)
  | var x =>
    dsimp only [Rega.tryAddr, symStToX64]
    have hfold :
        Option.map f (match vh, st.defs.find? x with
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
      | some df => cases df with
        | addImm64 base d =>
          dsimp only; split
          · rw [findGprFor_eq]
            cases Rega.findGprFor x64Isa true st.regs (.var base) with
            | none => rfl
            | some rb => exact hk (.baseDisp rb off)
          · rfl
        | _ => rfl
    have hvar :
        Option.map f ((Rega.findGprFor vllX64IsaR true st.regs (.var x)).bind fun rx =>
          k₁ (.baseDisp rx 0)) =
        ((Rega.findGprFor x64Isa true st.regs (.var x)).bind fun rx => k₂ (.baseDisp rx 0)) := by
      rw [findGprFor_eq]
      cases Rega.findGprFor x64Isa true st.regs (.var x) with
      | none => rfl
      | some rx => exact hk (.baseDisp rx 0)
    have hdef :
        Option.map f (match st.defs.find? x with
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
      | some df => cases df with
        | imm64 c => exact hk (.imm c)
        | addImm64 base d =>
          dsimp only; rw [findGprFor_eq]
          cases Rega.findGprFor x64Isa true st.regs (.var base) with
          | none => rfl
          | some rb => exact hk (.baseDisp rb (Int64.ofBitVec d))
        | addrSum base idx sh d =>
          dsimp only
          cases AddrScale.ofShift? sh with
          | none => rfl
          | some sc =>
            dsimp only [Option.bind]
            rw [findGprFor_eq]
            cases Rega.findGprFor x64Isa true st.regs (.var base) with
            | none => rfl
            | some rb =>
              dsimp only [Option.bind]
              rw [findGprFor_eq]
              cases Rega.findGprFor x64Isa true st.regs (.var idx) with
              | none => rfl
              | some ri => exact hk (.baseIdxDisp rb ri sc (Int64.ofBitVec d))
        | _ => rfl
    exact mapOpt_or_congr f hfold (mapOpt_or_congr f hvar hdef)

private theorem findJnzCond_eq (nslots : Nat) (st : Rega.SymState vllX64IsaR) (x : Nat) :
    (Rega.findJnzCond vllX64IsaR nslots st x).map mapJnzCond =
      Rega.findJnzCond x64Isa nslots (symStToX64 st) x := by
  have h1 :
      ((Rega.findFlagFor vllX64IsaR st.regs (.var x)).map Rega.JnzCond.flag).map mapJnzCond =
      (Rega.findFlagFor x64Isa st.regs (.var x)).map Rega.JnzCond.flag := by
    rw [findFlagFor_eq]; cases Rega.findFlagFor x64Isa st.regs (.var x) <;> rfl
  have h2 :
      ((match st.defs.find? x with
        | some (.cmpZeroVar co w y) =>
          (Rega.cmpZeroFlagCond? vllX64IsaR st.defs st.flags co w y).map Rega.JnzCond.flag
        | _ => none).map mapJnzCond) =
      (match st.defs.find? x with
       | some (.cmpZeroVar co w y) =>
         (Rega.cmpZeroFlagCond? x64Isa st.defs st.flags co w y).map Rega.JnzCond.flag
       | _ => none) := by
    cases st.defs.find? x with
    | none => rfl
    | some df => cases df with
      | cmpZeroVar co w y =>
        dsimp only
        rw [cmpZeroFlagCond?_eq]
        cases Rega.cmpZeroFlagCond? x64Isa st.defs st.flags co w y <;> rfl
      | _ => rfl
  have h3 :
      ((Rega.findGprFor vllX64IsaR true st.regs (.var x)).map Rega.JnzCond.gpr).map mapJnzCond =
      (Rega.findGprFor x64Isa true st.regs (.var x)).map Rega.JnzCond.gpr := by
    rw [findGprFor_eq]; cases Rega.findGprFor x64Isa true st.regs (.var x) <;> rfl
  have h4 :
      ((match st.defs.find? x with
        | some (.cmpZeroVar co w y) =>
          (match st.memDefs.find? y with
           | some (.bits m, addr) =>
             if Nat.beq m w && Rega.isStdBitWidth w then
               (vllX64IsaR.gpr.condOfCmp? co).bind fun cc =>
                 Rega.tryAddr vllX64IsaR st .default addr fun aa =>
                   (vllX64IsaR.gpr.cmpMem co w aa (.imm 0#w) (.flag cc)).map fun _ =>
                     Rega.JnzCond.cmpZeroMem co w y aa cc
             else none
           | _ => none) <|>
          (Rega.findGprFor vllX64IsaR true st.regs (.var y)).bind fun r =>
            if (vllX64IsaR.gpr.cmpZeroJcc co w r (Rega.lname "" 0)).isSome then
              some (Rega.JnzCond.cmpZero co w r)
            else if Rega.isStdBitWidth w then
              (vllX64IsaR.gpr.condOfCmp? co).bind fun cc =>
                (vllX64IsaR.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ())
                  (.flag cc, ()) .default).map fun _ => Rega.JnzCond.cmpZeroFlag co w y r cc
            else none
        | some (.testBitVar neg w y c) =>
          (Rega.findGprFor vllX64IsaR true st.regs (.var y)).map fun r =>
            Rega.JnzCond.testImm neg w r (c.setWidth w)
        | _ => none).map mapJnzCond) =
      (match st.defs.find? x with
       | some (.cmpZeroVar co w y) =>
         (match st.memDefs.find? y with
          | some (.bits m, addr) =>
            if Nat.beq m w && Rega.isStdBitWidth w then
              (x64Isa.gpr.condOfCmp? co).bind fun cc =>
                Rega.tryAddr x64Isa (symStToX64 st) .default addr fun aa =>
                  (x64Isa.gpr.cmpMem co w aa (.imm 0#w) (.flag cc)).map fun _ =>
                    Rega.JnzCond.cmpZeroMem co w y aa cc
            else none
          | _ => none) <|>
         (Rega.findGprFor x64Isa true st.regs (.var y)).bind fun r =>
           if (x64Isa.gpr.cmpZeroJcc co w r (Rega.lname "" 0)).isSome then
             some (Rega.JnzCond.cmpZero co w r)
           else if Rega.isStdBitWidth w then
             (x64Isa.gpr.condOfCmp? co).bind fun cc =>
               (x64Isa.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ())
                 (.flag cc, ()) .default).map fun _ => Rega.JnzCond.cmpZeroFlag co w y r cc
           else none
       | some (.testBitVar neg w y c) =>
         (Rega.findGprFor x64Isa true st.regs (.var y)).map fun r =>
           Rega.JnzCond.testImm neg w r (c.setWidth w)
       | _ => none) := by
    cases st.defs.find? x with
    | none => rfl
    | some df => cases df with
      | testBitVar neg w y c =>
        dsimp only
        rw [findGprFor_eq]
        cases Rega.findGprFor x64Isa true st.regs (.var y) <;> rfl
      | cmpZeroVar co w y =>
        dsimp only
        have hmem :
            (Option.map mapJnzCond (match st.memDefs.find? y with
             | some (.bits m, addr) =>
               if Nat.beq m w && Rega.isStdBitWidth w then
                 (vllX64IsaR.gpr.condOfCmp? co).bind fun cc =>
                   Rega.tryAddr vllX64IsaR st .default addr fun aa =>
                     (vllX64IsaR.gpr.cmpMem co w aa (.imm 0#w) (.flag cc)).map fun _ =>
                       Rega.JnzCond.cmpZeroMem co w y aa cc
               else none
             | _ => none)) =
            (match st.memDefs.find? y with
             | some (.bits m, addr) =>
               if Nat.beq m w && Rega.isStdBitWidth w then
                 (x64Isa.gpr.condOfCmp? co).bind fun cc =>
                   Rega.tryAddr x64Isa (symStToX64 st) .default addr fun aa =>
                     (x64Isa.gpr.cmpMem co w aa (.imm 0#w) (.flag cc)).map fun _ =>
                       Rega.JnzCond.cmpZeroMem co w y aa cc
               else none
             | _ => none) := by
          cases st.memDefs.find? y with
          | none => rfl
          | some p =>
            rcases p with ⟨ty, addr⟩
            cases ty with
            | bool | float _ | pair _ _ => rfl
            | bits m =>
              dsimp only; split
              · rw [vllR_condOfCmp_eq]
                cases x64Isa.gpr.condOfCmp? co with
                | none => rfl
                | some cc =>
                  dsimp only [Option.bind]
                  refine mapOpt_tryAddr mapJnzCond st .default addr fun aa => ?_
                  have hcm := vllR_cmpMem_eq co w aa (.imm 0#w) (.flag cc)
                  cases h0 : vllX64GprR.cmpMem co w aa (.imm 0#w) (.flag cc) with
                  | none => rw [h0] at hcm; dsimp only [Option.map] at hcm; rw [← hcm]; rfl
                  | some _ => rw [h0] at hcm; dsimp only [Option.map] at hcm; rw [← hcm]; rfl
              · rfl
        have hgpr :
            Option.map mapJnzCond ((Rega.findGprFor vllX64IsaR true st.regs (.var y)).bind fun r =>
              if (vllX64IsaR.gpr.cmpZeroJcc co w r (Rega.lname "" 0)).isSome then
                some (Rega.JnzCond.cmpZero co w r)
              else if Rega.isStdBitWidth w then
                (vllX64IsaR.gpr.condOfCmp? co).bind fun cc =>
                  (vllX64IsaR.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ())
                    (.flag cc, ()) .default).map fun _ => Rega.JnzCond.cmpZeroFlag co w y r cc
              else none) =
            ((Rega.findGprFor x64Isa true st.regs (.var y)).bind fun r =>
              if (x64Isa.gpr.cmpZeroJcc co w r (Rega.lname "" 0)).isSome then
                some (Rega.JnzCond.cmpZero co w r)
              else if Rega.isStdBitWidth w then
                (x64Isa.gpr.condOfCmp? co).bind fun cc =>
                  (x64Isa.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ())
                    (.flag cc, ()) .default).map fun _ => Rega.JnzCond.cmpZeroFlag co w y r cc
              else none) := by
          rw [findGprFor_eq]
          cases Rega.findGprFor x64Isa true st.regs (.var y) with
          | none => rfl
          | some r =>
            dsimp only [Option.bind]
            rw [vllR_cmpZeroJcc_eq, vllR_cmpZeroJcc_none_x64]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            cases Rega.isStdBitWidth w with
            | false => simp only [Bool.false_eq_true, ↓reduceIte]; rfl
            | true =>
              simp only [↓reduceIte]
              rw [vllR_condOfCmp_eq]
              cases x64Isa.gpr.condOfCmp? co with
              | none => rfl
              | some cc =>
                dsimp only [Option.bind]
                rw [← vllR_op_eq (.cmp co (.bits w) .bool rfl) (.gpr r, .imm 0#w, ())
                  (.flag cc, ()) .default rfl]
                cases vllX64GprR.op (.cmp co (.bits w) .bool rfl) (.gpr r, .imm 0#w, ())
                    (.flag cc, ()) .default <;> rfl
        exact mapOpt_or_congr mapJnzCond hmem hgpr
      | _ => rfl
  have h5 :
      ((Rega.findSlotGpr nslots st.slots x).map Rega.JnzCond.slot).map mapJnzCond =
      (Rega.findSlotGpr nslots st.slots x).map Rega.JnzCond.slot := by
    cases Rega.findSlotGpr nslots st.slots x <;> rfl
  dsimp only [Rega.findJnzCond, symStToX64]
  exact mapOpt_or_congr mapJnzCond h1
    (mapOpt_or_congr mapJnzCond h2
      (mapOpt_or_congr mapJnzCond h3 (mapOpt_or_congr mapJnzCond h4 h5)))

@[expose] def mapOptJnzSetup :
    Option (Bool × Option Nat × List vllX64IsaR.Directive × Rega.SymState vllX64IsaR) →
    Option (Bool × Option Nat × List _root_.Directive × Rega.SymState x64Isa) :=
  Option.map fun (inv, tgt?, br, st) => (inv, tgt?, asmX64List br, symStToX64 st)

private theorem jnzMode_eq {rs : List Ty} (h : x64Isa.Hints) (ipT ipE : Nat)
    (st : Rega.SymState vllX64IsaR) (canInv : Bool) (t e : Expr Rega.VNat Rega.LNat rs)
    (ft : Option Nat) (fwd : Trie Nat) :
    Rega.jnzMode vllX64IsaR h ipT ipE st canInv t e ft fwd =
      Rega.jnzMode x64Isa h ipT ipE (symStToX64 st) canInv t e ft fwd := by
  dsimp only [Rega.jnzMode]
  rw [zeroMoveJump?_eq, zeroMoveJump?_eq]

private theorem threadFusedArm_eq {rs : List Ty} (h : x64Isa.Hints) (fn : Sym) (ipA : Nat)
    (st1 : Rega.SymState vllX64IsaR)
    {emitV : Sym → Option (List (Instr x64Arch) × FlagMask)}
    {emitX : Sym → Option (List _root_.Directive × FlagMask)}
    (hemit : ∀ l, mapOptCl (emitV l) = emitX l)
    (arm : Expr Rega.VNat Rega.LNat rs) (fwd : Trie Nat) (hno : regsNoRsp st1.regs = true) :
    (Rega.threadFusedArm vllX64IsaR h fn ipA st1 emitV arm fwd).map
        (fun (j, br, st) => (j, asmX64List br, symStToX64 st)) =
      Rega.threadFusedArm x64Isa h fn ipA (symStToX64 st1) emitX arm fwd ∧
    (∀ j br stB, Rega.threadFusedArm vllX64IsaR h fn ipA st1 emitV arm fwd = some (j, br, stB) →
      regsNoRsp stB.regs = true) := by
  cases arm with
  | jump j args =>
    dsimp only [Rega.threadFusedArm]
    have h0 := hemit (Rega.lname fn (Rega.tgtLab fwd j))
    cases he : emitV (Rega.lname fn (Rega.tgtLab fwd j)) with
    | none =>
      have hx : emitX (Rega.lname fn (Rega.tgtLab fwd j)) = none := by rw [← h0, he]; rfl
      rw [hx]; exact ⟨rfl, fun _ _ _ h1 => by cases h1⟩
    | some p =>
      rcases p with ⟨br, cl⟩
      have hx : emitX (Rega.lname fn (Rega.tgtLab fwd j)) = some (asmX64List br, cl) := by
        rw [← h0, he]; rfl
      rw [hx]
      refine ⟨?_, fun j' br' stB h1 => by
        dsimp only [Option.bind] at h1
        split at h1 <;> cases h1
        exact regsNoRsp_killRegs _ hno⟩
      dsimp only [Option.bind, symStToX64]
      rw [vllR_scratch_eq, killRegs_eq, killZeroExt_eq, killFlags_eq, zeroMoveJump?_eq]
      split <;> rfl
  | _ => exact ⟨rfl, fun _ _ _ h1 => by cases h1⟩

private theorem fuseJnzChoice_eq {rs : List Ty} (h : x64Isa.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : Rega.SymState vllX64IsaR) (t e : Expr Rega.VNat Rega.LNat rs) (ft : Option Nat)
    {emitV : Bool → Sym → Option (List (Instr x64Arch) × FlagMask)}
    {emitX : Bool → Sym → Option (List _root_.Directive × FlagMask)}
    (hemit : ∀ inv l, mapOptCl (emitV inv l) = emitX inv l)
    (fwd : Trie Nat) (hno : regsNoRsp st1.regs = true) :
    mapOptJnzSetup (Rega.fuseJnzChoice vllX64IsaR h fn nl ipT ipE st1 t e ft emitV fwd) =
      Rega.fuseJnzChoice x64Isa h fn nl ipT ipE (symStToX64 st1) t e ft emitX fwd ∧
    (∀ inv tgt? br stBr,
      Rega.fuseJnzChoice vllX64IsaR h fn nl ipT ipE st1 t e ft emitV fwd =
        some (inv, tgt?, br, stBr) →
      regsNoRsp stBr.regs = true) := by
  dsimp only [Rega.fuseJnzChoice]
  have h0 := hemit (h.invertJnz.getD (ipE - 1) false) (Rega.lname fn nl)
  cases he : emitV (h.invertJnz.getD (ipE - 1) false) (Rega.lname fn nl) with
  | none =>
    have hx : emitX (h.invertJnz.getD (ipE - 1) false) (Rega.lname fn nl) = none := by
      rw [← h0, he]; rfl
    rw [hx]; exact ⟨rfl, fun _ _ _ _ h1 => by cases h1⟩
  | some p =>
    rcases p with ⟨brNl, clNl⟩
    have hx : emitX (h.invertJnz.getD (ipE - 1) false) (Rega.lname fn nl) =
        some (asmX64List brNl, clNl) := by rw [← h0, he]; rfl
    rw [hx]
    dsimp only [Option.map, mapOptJnzSetup]
    obtain ⟨hf_eq, hf_no⟩ := threadFusedArm_eq h fn ipT st1 (hemit false) t fwd hno
    obtain ⟨hi_eq, hi_no⟩ := threadFusedArm_eq h fn ipE st1 (hemit true) e fwd hno
    cases hfV : Rega.threadFusedArm vllX64IsaR h fn ipT st1 (emitV false) t fwd with
    | none =>
      have hfX : Rega.threadFusedArm x64Isa h fn ipT (symStToX64 st1) (emitX false) t fwd =
          none := by rw [← hf_eq, hfV]; rfl
      rw [hfX]
      cases hiV : Rega.threadFusedArm vllX64IsaR h fn ipE st1 (emitV true) e fwd with
      | none =>
        have hiX : Rega.threadFusedArm x64Isa h fn ipE (symStToX64 st1) (emitX true) e fwd =
            none := by rw [← hi_eq, hiV]; rfl
        rw [hiX]
        refine ⟨?_, fun _ _ _ _ h1 => by cases h1; exact regsNoRsp_killRegs _ hno⟩
        dsimp only [symStToX64]
        rw [vllR_scratch_eq, killRegs_eq, killZeroExt_eq, killFlags_eq]
      | some q =>
        rcases q with ⟨je, brI, stI⟩
        have hiX : Rega.threadFusedArm x64Isa h fn ipE (symStToX64 st1) (emitX true) e fwd =
            some (je, asmX64List brI, symStToX64 stI) := by rw [← hi_eq, hiV]; rfl
        rw [hiX]
        exact ⟨rfl, fun _ _ _ _ h1 => by cases h1; exact hi_no je brI stI hiV⟩
    | some pF =>
      rcases pF with ⟨jt, brF, stF⟩
      have hfX : Rega.threadFusedArm x64Isa h fn ipT (symStToX64 st1) (emitX false) t fwd =
          some (jt, asmX64List brF, symStToX64 stF) := by rw [← hf_eq, hfV]; rfl
      rw [hfX]
      cases hiV : Rega.threadFusedArm vllX64IsaR h fn ipE st1 (emitV true) e fwd with
      | none =>
        have hiX : Rega.threadFusedArm x64Isa h fn ipE (symStToX64 st1) (emitX true) e fwd =
            none := by rw [← hi_eq, hiV]; rfl
        rw [hiX]
        exact ⟨rfl, fun _ _ _ _ h1 => by cases h1; exact hf_no jt brF stF hfV⟩
      | some q =>
        rcases q with ⟨je, brI, stI⟩
        have hiX : Rega.threadFusedArm x64Isa h fn ipE (symStToX64 st1) (emitX true) e fwd =
            some (je, asmX64List brI, symStToX64 stI) := by rw [← hi_eq, hiV]; rfl
        rw [hiX]
        cases hft : (ft == some (Rega.tgtLab fwd jt)) with
        | true =>
          simp only [hft, ↓reduceIte]
          exact ⟨trivial, fun _ _ _ _ h1 => by cases h1; exact hi_no je brI stI hiV⟩
        | false =>
          simp only [hft, Bool.false_eq_true, ↓reduceIte]
          exact ⟨trivial, fun _ _ _ _ h1 => by cases h1; exact hf_no jt brF stF hfV⟩

private theorem finishCmpJnz_eq {rs : List Ty} (h : x64Isa.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : Rega.SymState vllX64IsaR) (t e : Expr Rega.VNat Rega.LNat rs) (ft : Option Nat)
    (fwd : Trie Nat) (cc : CondCode) (cmpCode : List (Instr x64Arch)) (cl : FlagMask)
    (fl : Option Rega.FlagFact) (hno : regsNoRsp st1.regs = true) :
    let r := Rega.finishCmpJnz vllX64IsaR h fn nl ipT ipE st1 t e ft fwd cc cmpCode cl fl
    (r.1, r.2.1, asmX64List r.2.2.1, symStToX64 r.2.2.2) =
      Rega.finishCmpJnz x64Isa h fn nl ipT ipE (symStToX64 st1) t e ft fwd cc
        (asmX64List cmpCode) cl fl ∧
    regsNoRsp r.2.2.2.regs = true := by
  refine ⟨?_, regsNoRsp_killRegs _ (regsNoRsp_killRegs _ hno)⟩
  dsimp only [Rega.finishCmpJnz]
  rw [jnzMode_eq]
  dsimp only [symStToX64]
  rw [vllR_scratch_eq, killRegs_eq, killRegs_eq, killZeroExt_eq, killZeroExt_eq, killFlags_eq,
    asmX64List_append, vllR_negCond_eq, vllR_jcc_eq]

private theorem jnzSetup_slot_aux (stB1 : Rega.SymState vllX64IsaR)
    (stB2 : Rega.SymState x64Isa) (hst : symStToX64 stB1 = stB2)
    (inv : Bool) (tgt? : Option Nat) (sym : Sym) (a : AddrArg Reg64)
    (hno : regsNoRsp stB1.regs = true) :
    mapOptJnzSetup ((vllX64GprR.jnzMem a inv sym).bind fun (br, cl) =>
      if cl == FlagMask.all then some (inv, tgt?, br, stB1) else none) =
    ((x64Isa.gpr.jnzMem a inv sym).bind fun (br, cl) =>
      if cl == FlagMask.all then some (inv, tgt?, br, stB2) else none) ∧
    (∀ i t b s, ((vllX64GprR.jnzMem a inv sym).bind fun (br, cl) =>
      if cl == FlagMask.all then some (inv, tgt?, br, stB1) else none) = some (i, t, b, s) →
      regsNoRsp s.regs = true) := by
  have hjm := vllR_jnzMem_eq a inv sym
  cases h0 : vllX64GprR.jnzMem a inv sym with
  | none =>
    rw [h0] at hjm; dsimp only [Option.map] at hjm; rw [← hjm]
    exact ⟨rfl, fun _ _ _ _ h => by cases h⟩
  | some p =>
    rcases p with ⟨br, cl⟩
    rw [h0] at hjm; dsimp only [Option.map] at hjm; rw [← hjm]
    dsimp only [Option.bind]
    split
    · subst hst; exact ⟨rfl, fun _ _ _ _ h => by cases h; exact hno⟩
    · exact ⟨rfl, fun _ _ _ _ h => by cases h⟩

private theorem jnzSetup_eq_and_noRsp {rs : List Ty} (h : x64Isa.Hints) (fn : Sym)
    (nl ipT ipE : Nat) (st1 : Rega.SymState vllX64IsaR) (t e : Expr Rega.VNat Rega.LNat rs)
    (ft : Option Nat) (cond : Rega.JnzCond vllX64IsaR) (fwd : Trie Nat)
    (hno : regsNoRsp st1.regs = true) :
    mapOptJnzSetup (Rega.jnzSetup vllX64IsaR h fn nl ipT ipE st1 t e ft cond fwd) =
      Rega.jnzSetup x64Isa h fn nl ipT ipE (symStToX64 st1) t e ft (mapJnzCond cond) fwd ∧
    (∀ inv tgt? br stBr,
      Rega.jnzSetup vllX64IsaR h fn nl ipT ipE st1 t e ft cond fwd = some (inv, tgt?, br, stBr) →
      regsNoRsp stBr.regs = true) := by
  cases cond with
  | flag cc =>
    dsimp only [Rega.jnzSetup, mapJnzCond, mapOptJnzSetup, Option.map]
    refine ⟨?_, fun _ _ _ _ h1 => by cases h1; exact regsNoRsp_killRegs _ hno⟩
    dsimp only [symStToX64]
    rw [vllR_scratch_eq, killRegs_eq, killZeroExt_eq, killFlags_eq, jnzMode_eq,
      vllR_negCond_eq, vllR_jcc_eq]
  | gpr r =>
    dsimp only [Rega.jnzSetup, mapJnzCond]
    rw [vllR_jnzGprInv_some_eq, x64_jnzGprInv_some_eq]
    exact fuseJnzChoice_eq h fn nl ipT ipE st1 t e ft (fun inv l => by
      dsimp only [mapOptCl, Option.map]; rw [vllR_jnzGprInv_eq]) fwd hno
  | slot idx =>
    dsimp only [Rega.jnzSetup, mapJnzCond]
    rw [vllR_spAddr_eq]
    have hnoB : regsNoRsp (Rega.killRegs vllX64IsaR vllX64FrameR.scratch []
        FlagMask.all st1.regs) = true := regsNoRsp_killRegs _ hno
    have hstB : symStToX64
        { st1 with
          regs := Rega.killRegs vllX64IsaR vllX64FrameR.scratch [] FlagMask.all st1.regs
          zeroExt32 := @Rega.killZeroExt vllX64IsaR.Reg vllX64IsaR.decEqReg
            vllX64FrameR.scratch st1.zeroExt32
          flags := Rega.killFlags vllX64IsaR FlagMask.all st1.flags } =
        { symStToX64 st1 with
          regs := Rega.killRegs x64Isa x64Isa.frame.scratch [] FlagMask.all st1.regs
          zeroExt32 := @Rega.killZeroExt x64Isa.Reg x64Isa.decEqReg
            x64Isa.frame.scratch st1.zeroExt32
          flags := Rega.killFlags x64Isa FlagMask.all st1.flags } := by
      dsimp only [symStToX64]
      rw [vllR_scratch_eq, killRegs_eq, killZeroExt_eq, killFlags_eq]
    have hmeq :
        Rega.jnzMode vllX64IsaR h ipT ipE
          { st1 with
            regs := Rega.killRegs vllX64IsaR vllX64FrameR.scratch [] FlagMask.all st1.regs
            zeroExt32 := @Rega.killZeroExt vllX64IsaR.Reg vllX64IsaR.decEqReg
              vllX64FrameR.scratch st1.zeroExt32
            flags := Rega.killFlags vllX64IsaR FlagMask.all st1.flags } true t e ft fwd =
        Rega.jnzMode x64Isa h ipT ipE
          { symStToX64 st1 with
            regs := Rega.killRegs x64Isa x64Isa.frame.scratch [] FlagMask.all st1.regs
            zeroExt32 := @Rega.killZeroExt x64Isa.Reg x64Isa.decEqReg
              x64Isa.frame.scratch st1.zeroExt32
            flags := Rega.killFlags x64Isa FlagMask.all st1.flags } true t e ft fwd := by
      rw [jnzMode_eq, hstB]
    rw [hmeq]
    exact jnzSetup_slot_aux _ _ hstB _ _ _ _ hnoB
  | cmpZero co w r =>
    dsimp only [Rega.jnzSetup, mapJnzCond]
    exact fuseJnzChoice_eq h fn nl ipT ipE st1 t e ft (fun inv l => by
      dsimp only [mapOptCl]
      rw [vllR_cmpZeroJcc_eq, vllR_cmpZeroJcc_none_x64]; rfl) fwd hno
  | cmpZeroMem co w y aa cc =>
    dsimp only [Rega.jnzSetup, mapJnzCond]
    have hcm := vllR_cmpMem_eq co w aa (.imm 0#w) (.flag cc)
    cases h0 : vllX64GprR.cmpMem co w aa (.imm 0#w) (.flag cc) with
    | none =>
      rw [h0] at hcm; dsimp only [Option.map] at hcm; rw [← hcm]
      exact ⟨rfl, fun _ _ _ _ h1 => by cases h1⟩
    | some p =>
      rcases p with ⟨cmpCode, cl⟩
      rw [h0] at hcm; dsimp only [Option.map] at hcm; rw [← hcm]
      dsimp only [Option.map, mapOptJnzSetup]
      have hcres := cmpMemRes_eq st1 co w (.var y) (.immBits w 0#64) (.flag cc) cmpCode cl
      have hfl : (Rega.cmpMemRes vllX64IsaR st1 co w (.var y) (.immBits w 0#64) (.flag cc)
          cmpCode cl).2.2.1 =
          (Rega.cmpMemRes x64Isa (symStToX64 st1) co w (.var y) (.immBits w 0#64) (.flag cc)
            (asmX64List cmpCode) cl).2.2.1 :=
        congrArg (fun x => x.2.2.1) hcres
      have hfin := finishCmpJnz_eq h fn nl ipT ipE st1 t e ft fwd cc cmpCode cl
        (Rega.cmpMemRes vllX64IsaR st1 co w (.var y) (.immBits w 0#64) (.flag cc)
          cmpCode cl).2.2.1 hno
      refine ⟨?_, fun _ _ _ _ h1 => by cases h1; exact hfin.2⟩
      rw [hfin.1, hfl]
  | cmpZeroFlag co w y r cc =>
    dsimp only [Rega.jnzSetup, mapJnzCond]
    have hop := vllR_op_eq (.cmp co (.bits w) .bool rfl) (.gpr r, .imm 0#w, ())
      (.flag cc, ()) .default rfl
    cases h0 : vllX64GprR.op (.cmp co (.bits w) .bool rfl) (.gpr r, .imm 0#w, ())
        (.flag cc, ()) .default with
    | none =>
      rw [h0] at hop; dsimp only [Option.map] at hop; rw [← hop]
      exact ⟨rfl, fun _ _ _ _ h1 => by cases h1⟩
    | some p =>
      rcases p with ⟨cmpCode, cl⟩
      rw [h0] at hop; dsimp only [Option.map] at hop; rw [← hop]
      dsimp only [Option.map, mapOptJnzSetup]
      let fl : Option Rega.FlagFact :=
        if Nat.ble w 64 then
          match vllX64GprR.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
          | some lf => some (.cmp w (if lf then .var y else .immBits w 0#64)
                                     (if lf then .immBits w 0#64 else .var y) false)
          | none => Rega.killFlags vllX64IsaR cl st1.flags
        else Rega.killFlags vllX64IsaR cl st1.flags
      have hfl :
          fl =
          (if Nat.ble w 64 then
            match x64Isa.gpr.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
            | some lf => some (.cmp w (if lf then .var y else .immBits w 0#64)
                                       (if lf then .immBits w 0#64 else .var y) false)
            | none => Rega.killFlags x64Isa cl (symStToX64 st1).flags
          else Rega.killFlags x64Isa cl (symStToX64 st1).flags) := by
        dsimp only [fl]
        rw [vllR_cmpFlagsOut?_eq, killFlags_eq]
      have hfin := finishCmpJnz_eq h fn nl ipT ipE st1 t e ft fwd cc cmpCode cl fl hno
      refine ⟨?_, fun _ _ _ _ h1 => by cases h1; exact hfin.2⟩
      rw [hfl] at hfin; exact congrArg some hfin.1
  | testImm neg w r mask =>
    dsimp only [Rega.jnzSetup, mapJnzCond]
    exact fuseJnzChoice_eq h fn nl ipT ipE st1 t e ft (fun inv l => by
      dsimp only [mapOptCl]
      rw [vllR_testJcc_eq, vllR_testJcc_none_x64]; rfl) fwd hno

private theorem lowerTail_eq {ts : List Ty} (h : x64Isa.Hints) (hs : savedNoRsp h.saved = true)
    (E : Rega.Ext) (st1 : Rega.SymState vllX64IsaR) (mc : List (Instr x64Arch))
    (tail : List (Instr x64Arch)) (args : Tup (Arg Rega.VNat) ts)
    (locs : Tup (AbiReg Reg64 RegMm) ts) (nv nl ip : Nat) (hno : regsNoRsp st1.regs = true) :
    mapRes (Rega.lowerTail vllX64IsaR h E st1 mc tail args locs nv nl ip) =
      Rega.lowerTail x64Isa h E (symStToX64 st1) (asmX64List mc) (asmX64List tail)
        args locs nv nl ip := by
  dsimp only [Rega.lowerTail]
  rw [abiTargets_eq]
  cases Rega.abiTargets x64Isa args locs with
  | none => rfl
  | some tgts =>
    dsimp only
    obtain ⟨hsh, _⟩ := shuffle_eq_and_noRsp hs st1 tgts hno
    cases h0 : Rega.shuffle vllX64IsaR h.nslots h.saved st1 tgts with
    | none =>
      have hx : Rega.shuffle x64Isa h.nslots h.saved (symStToX64 st1) tgts = none := by
        rw [← hsh, h0]; rfl
      rw [hx]; rfl
    | some p =>
      rcases p with ⟨sc, st'⟩
      have hx : Rega.shuffle x64Isa h.nslots h.saved (symStToX64 st1) tgts =
          some (asmX64List sc, symStToX64 st') := by rw [← hsh, h0]; rfl
      rw [hx]
      dsimp only [mapRes, Rega.fnEpilogue]
      have hzl : Rega.isZeroLeaf vllX64IsaR h E = Rega.isZeroLeaf x64Isa h E := by
        dsimp only [Rega.isZeroLeaf]; rw [vllR_leafZeroFrame_eq]
      rw [hzl]
      cases Rega.isZeroLeaf x64Isa h E <;>
        simp only [Bool.false_eq_true, ↓reduceIte, asmX64List_append,
          asmX64List_nil, canonAbiCode_eq, abiSkips_eq, restoreCs_eq]
      have hepi : asmX64List (vllX64FrameR.epilogue h.totalSlots).1 =
          (x64Epilogue h.totalSlots).1 := vllR_epilogue_eq h.totalSlots
      simp only [hepi]

private theorem lowerOp_deferTrue_eq (h : x64Isa.Hints) (nv ip : Nat)
    (st1 : Rega.SymState vllX64IsaR) {ts : List Ty} (op : Op Rega.VNat ts) :
    mapOptSt (Rega.lowerOp vllX64IsaR h nv ip st1 op true) =
      Rega.lowerOp x64Isa h nv ip (symStToX64 st1) op true ∧
    (∀ c0 st', Rega.lowerOp vllX64IsaR h nv ip st1 op true = some (c0, st') →
      st'.regs = st1.regs) := by
  dsimp only [Rega.lowerOp, ↓reduceIte]
  cases Rega.recordBoolDef st1.defs op.code op.args with
  | some _ => exact ⟨rfl, fun _ _ h0 => by cases h0; rfl⟩
  | none =>
    cases Rega.recordDef st1.defs op.code op.args with
    | none => exact ⟨rfl, fun _ _ h0 => by cases h0⟩
    | some _ => exact ⟨rfl, fun _ _ h0 => by cases h0; rfl⟩

private theorem deferJnzNext_eq {rs : List Ty} (h : x64Isa.Hints) (hs : savedNoRsp h.saved = true)
    (fn : Sym) (nv nl ip : Nat) (st1 : Rega.SymState vllX64IsaR) {ts : List Ty}
    (op : Op Rega.VNat ts) (k' : Expr Rega.VNat Rega.LNat rs) (hno : regsNoRsp st1.regs = true) :
    Rega.deferJnzNext vllX64IsaR h fn nv nl ip st1 op k' =
      Rega.deferJnzNext x64Isa h fn nv nl ip (symStToX64 st1) op k' := by
  dsimp only [Rega.deferJnzNext]
  cases k' with
  | jnz cond _ _ =>
    cases cond with
    | imm _ => cases ts with | nil => rfl | cons t ts' => cases t <;> cases ts' <;> rfl
    | var cx =>
      cases ts with
      | nil => rfl
      | cons t ts' => cases t with
        | bits _ | float _ | pair _ _ => rfl
        | bool => cases ts' with
          | cons _ _ => rfl
          | nil =>
            dsimp only
            cases Nat.beq cx nv && h.deferJnz.getD ip false with
            | false => rfl
            | true =>
              obtain ⟨ho, hr⟩ := lowerOp_deferTrue_eq h nv ip st1 op
              cases h0 : Rega.lowerOp vllX64IsaR h nv ip st1 op true with
              | none =>
                have hx : Rega.lowerOp x64Isa h nv ip (symStToX64 st1) op true = none := by
                  rw [← ho, h0]; rfl
                rw [hx]
              | some p2 =>
                rcases p2 with ⟨c2, st2⟩
                have hx : Rega.lowerOp x64Isa h nv ip (symStToX64 st1) op true =
                    some (asmX64List c2, symStToX64 st2) := by rw [← ho, h0]; rfl
                rw [hx]; dsimp only
                have hno2 : regsNoRsp st2.regs = true := (hr c2 st2 h0) ▸ hno
                obtain ⟨hpre, _⟩ := stepPre_eq_and_noRsp h (ip + 1) hs st2 hno2
                cases hs0 : Rega.stepPre vllX64IsaR h (ip + 1) st2 with
                | none =>
                  have hsx : Rega.stepPre x64Isa h (ip + 1) (symStToX64 st2) = none := by
                    rw [← hpre, hs0]; rfl
                  rw [hsx]
                | some p3 =>
                  rcases p3 with ⟨c3, stAfter⟩
                  have hsx : Rega.stepPre x64Isa h (ip + 1) (symStToX64 st2) =
                      some (asmX64List c3, symStToX64 stAfter) := by rw [← hpre, hs0]; rfl
                  rw [hsx]
                  dsimp only
                  rw [← findJnzCond_eq h.nslots stAfter nv]
                  cases Rega.findJnzCond vllX64IsaR h.nslots stAfter nv with
                  | none => rfl
                  | some cond =>
                    cases cond with
                    | flag _ | slot _ | gpr _ => rfl
                    | cmpZero co w r =>
                      dsimp only [Option.map, mapJnzCond]
                      have hx0 : x64Gpr.cmpZeroJcc co w r (Rega.lname fn nl) = none :=
                        vllR_cmpZeroJcc_none_x64 co w r (Rega.lname fn nl)
                      rw [vllR_cmpZeroJcc_eq, vllR_cmpZeroJcc_none_x64, ← hx0]; rfl
                    | cmpZeroMem _ _ _ _ cc | cmpZeroFlag _ _ _ _ cc =>
                      dsimp only [Option.map, mapJnzCond, bne]
                      exact congrArg Bool.not
                        (optLoc_optionBeq_congr _ _ (h.dest.find? nv) (some (.flag cc)))
                    | testImm neg w r mask =>
                      dsimp only [Option.map, mapJnzCond]
                      have hx0 : x64Gpr.testJcc neg w r mask (Rega.lname fn nl) = none :=
                        vllR_testJcc_none_x64 neg w r mask (Rega.lname fn nl)
                      rw [vllR_testJcc_eq, vllR_testJcc_none_x64, ← hx0]; rfl
  | load _ _ _ | store _ _ _ | call _ _ _ | let_ _ _ | jump _ _ | ret _ | exit _ _
  | hlt | group _ _ => cases ts with | nil => rfl | cons t ts' => cases t <;> cases ts' <;> rfl

private theorem deferLeaNext_eq {rs : List Ty} (h : x64Isa.Hints) (hs : savedNoRsp h.saved = true)
    (nv ip : Nat) (st1 : Rega.SymState vllX64IsaR) {ts : List Ty} (op : Op Rega.VNat ts)
    (k' : Expr Rega.VNat Rega.LNat rs) (hno : regsNoRsp st1.regs = true) :
    Rega.deferLeaNext vllX64IsaR h nv ip st1 op k' =
      Rega.deferLeaNext x64Isa h nv ip (symStToX64 st1) op k' := by
  dsimp only [Rega.deferLeaNext]
  cases !Rega.isLeaDeferCand op.code with
  | true => simp only [↓reduceIte]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ts with
    | nil => rfl
    | cons _ ts' => cases ts' with
      | cons _ _ => rfl
      | nil => cases k' with
        | let_ op2 _ =>
          dsimp only
          cases Rega.recordDef st1.defs op.code op.args with
          | none => rfl
          | some df =>
            dsimp only
            have hno1 : regsNoRsp { st1 with defs := st1.defs.insert nv df }.regs = true := hno
            obtain ⟨hpre, _⟩ := stepPre_eq_and_noRsp h (ip + 1) hs _ hno1
            have hst : symStToX64 { st1 with defs := st1.defs.insert nv df } =
                { symStToX64 st1 with defs := (symStToX64 st1).defs.insert nv df } := rfl
            rw [hst] at hpre
            cases hs0 : Rega.stepPre vllX64IsaR h (ip + 1)
                { st1 with defs := st1.defs.insert nv df } with
            | none =>
              have hsx : Rega.stepPre x64Isa h (ip + 1)
                  { symStToX64 st1 with defs := (symStToX64 st1).defs.insert nv df } = none := by
                rw [← hpre, hs0]; rfl
              rw [hsx]
            | some p3 =>
              rcases p3 with ⟨c3, stAfter⟩
              have hsx : Rega.stepPre x64Isa h (ip + 1)
                  { symStToX64 st1 with defs := (symStToX64 st1).defs.insert nv df } =
                  some (asmX64List c3, symStToX64 stAfter) := by rw [← hpre, hs0]; rfl
              rw [hsx]
              dsimp only
              rw [resolveDsts_eq_uncond h _ (nv + 1)]
              cases Rega.resolveDsts x64Isa h _ (nv + 1) with
              | none => rfl
              | some dsts2 =>
                dsimp only
                have hla := tryLeaArith_eq stAfter op2.code op2.args dsts2
                have his :
                    (Rega.tryLeaArith vllX64IsaR stAfter op2.code op2.args dsts2).isSome =
                      (Rega.tryLeaArith x64Isa (symStToX64 stAfter) op2.code op2.args dsts2).isSome
                      := by
                  rw [← hla]
                  cases Rega.tryLeaArith vllX64IsaR stAfter op2.code op2.args dsts2 <;> rfl
                rw [his]
        | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _
        | hlt | group _ _ => rfl

private theorem blockTrampoline?_eq {rs : List Ty} (h : x64Isa.Hints) (hh : hintsNoRsp h = true)
    (hs : savedNoRsp h.saved = true) (defs : Trie Rega.DefFact) (vw : Trie SlotWidth)
    (lid nv ip : Nat) {ts : List Ty} (b : Tup Rega.VNat ts → Expr Rega.VNat Rega.LNat rs) :
    Rega.blockTrampoline? vllX64IsaR h defs vw lid nv ip b =
      Rega.blockTrampoline? x64Isa h defs vw lid nv ip b := by
  dsimp only [Rega.blockTrampoline?]
  cases hfen : h.entry.find? lid with
  | none => rfl
  | some en =>
    dsimp only
    have hen : entryNoRsp en = true := trieAll_find_entry hh hfen
    simp only [entryNoRsp, Bool.and_eq_true] at hen
    rw [entryScopeOk_eq]
    cases Rega.entryScopeOk (I := x64Isa) nv en with
    | false => rfl
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hb_eq, hb_no⟩ := buildEntryBase_eq_and_noRsp h.nslots vw en.live
        { regs := [], slots := .empty, defs := defs, vecWidths := vw } hen.1 rfl
      cases hbase : Rega.buildEntryBase vllX64IsaR h.nslots vw en.live
          { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
      | none =>
        have hbx : Rega.buildEntryBase x64Isa h.nslots vw en.live
            { regs := [], slots := .empty, defs := defs, vecWidths := vw } = none := by
          rw [← hb_eq, hbase]; rfl
        rw [hbx]
      | some baseSt =>
        have hbx : Rega.buildEntryBase x64Isa h.nslots vw en.live
            { regs := [], slots := .empty, defs := defs, vecWidths := vw } =
            some (symStToX64 baseSt) := by rw [← hb_eq, hbase]; rfl
        rw [hbx]; dsimp only
        have hno_b := hb_no baseSt hbase
        obtain ⟨hp_eq, hp_no⟩ := bindBlockParams_eq_and_noRsp h.nslots ts en.ploc nv baseSt
          hen.2 hno_b
        cases hinit : Rega.bindBlockParams vllX64IsaR h.nslots ts en.ploc nv baseSt with
        | none =>
          have hix : Rega.bindBlockParams x64Isa h.nslots ts en.ploc nv
              (symStToX64 baseSt) = none := by rw [← hp_eq, hinit]; rfl
          rw [hix]
        | some initSt =>
          have hix : Rega.bindBlockParams x64Isa h.nslots ts en.ploc nv
              (symStToX64 baseSt) = some (symStToX64 initSt) := by rw [← hp_eq, hinit]; rfl
          rw [hix]; dsimp only
          have hno_i := hp_no initSt hinit
          cases b (Tup.levels ts nv) with
          | jump j' args' =>
            dsimp only
            obtain ⟨hs_eq, hs_p⟩ := stepPre_eq_and_noRsp h ip hs initSt hno_i
            cases hst0 : Rega.stepPre vllX64IsaR h ip initSt with
            | none =>
              have hsx : Rega.stepPre x64Isa h ip (symStToX64 initSt) = none := by
                rw [← hs_eq, hst0]; rfl
              rw [hsx]
            | some p1 =>
              rcases p1 with ⟨c1, st1⟩
              have hsx : Rega.stepPre x64Isa h ip (symStToX64 initSt) =
                  some (asmX64List c1, symStToX64 st1) := by rw [← hs_eq, hst0]; rfl
              rw [hsx]; dsimp only
              obtain ⟨hno1, hnil1⟩ := hs_p c1 st1 hst0
              cases c1 with
              | cons _ _ =>
                have hne : asmX64List (_ :: _) ≠ [] := fun hc => by cases hnil1 hc
                cases ha : asmX64List (_ :: _) with
                | nil => exact absurd ha hne
                | cons _ _ => cases h.entry.find? j' <;> rfl
              | nil =>
                cases h.entry.find? j' with
                | none => rfl
                | some en' =>
                  simp only [asmX64List, List.flatMap_nil]
                  rw [jumpTargets_eq]
                  cases Rega.jumpTargets x64Isa args' en'.ploc with
                  | none => rfl
                  | some argTgts =>
                    dsimp only
                    rw [list_all_congr' (fun p => jumpLocOk_eq h.nslots p.2) (en'.live ++ argTgts)]
                    split
                    · rfl
                    · obtain ⟨hsh_eq, hsh_p⟩ :=
                        shuffle_eq_and_noRsp hs st1 (en'.live ++ argTgts) hno1
                      cases hsh0 : Rega.shuffle vllX64IsaR h.nslots h.saved st1
                          (en'.live ++ argTgts) with
                      | none =>
                        have hshx : Rega.shuffle x64Isa h.nslots h.saved (symStToX64 st1)
                            (en'.live ++ argTgts) = none := by rw [← hsh_eq, hsh0]; rfl
                        rw [hshx]
                      | some p2 =>
                        rcases p2 with ⟨sc, st2⟩
                        have hshx : Rega.shuffle x64Isa h.nslots h.saved (symStToX64 st1)
                            (en'.live ++ argTgts) = some (asmX64List sc, symStToX64 st2) := by
                          rw [← hsh_eq, hsh0]; rfl
                        rw [hshx]; dsimp only
                        have hnil2 := (hsh_p sc st2 hsh0).2
                        cases sc with
                        | nil => rfl
                        | cons _ _ =>
                          have hne : asmX64List (_ :: _) ≠ [] := fun hc => by cases hnil2 hc
                          cases ha : asmX64List (_ :: _) with
                          | nil => exact absurd ha hne
                          | cons _ _ => rfl
          | _ => rfl

private theorem collectRawFwds_eq {rs : List Ty} (h : x64Isa.Hints) (hh : hintsNoRsp h = true)
    (hs : savedNoRsp h.saved = true) (defs : Trie Rega.DefFact) (vw : Trie SlotWidth)
    (fwd : Trie Nat) (fwdTgts : Trie Bool) :
    ∀ {sig : List (List Ty)} (bs : Blocks Rega.VNat Rega.LNat rs sig)
      (lid nv nl ip : Nat) (raw : Trie Nat) (lids : List Nat),
      Rega.collectRawFwds vllX64IsaR h defs vw fwd fwdTgts bs lid nv nl ip raw lids =
        Rega.collectRawFwds x64Isa h defs vw fwd fwdTgts bs lid nv nl ip raw lids
  | _, .nil, _, _, _, _, raw, lids => rfl
  | _, .cons (ts := ts) b bs, lid, nv, nl, ip, raw, lids => by
    dsimp only [Rega.collectRawFwds]
    rw [blockTrampoline?_eq h hh hs defs vw lid nv ip b]
    exact collectRawFwds_eq h hh hs defs vw fwd fwdTgts bs (lid + 1) _ _ _ _ _

private theorem findGroupFwds_eq {rs : List Ty} (h : x64Isa.Hints) (hh : hintsNoRsp h = true)
    (hs : savedNoRsp h.saved = true) (st : Rega.SymState vllX64IsaR)
    {sig : List (List Ty)} (bodies : Blocks Rega.VNat Rega.LNat rs sig)
    (k : Expr Rega.VNat Rega.LNat rs) (nv nl ip : Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool) :
    Rega.findGroupFwds vllX64IsaR h st bodies k nv nl ip fwd fwdTgts =
      Rega.findGroupFwds x64Isa h (symStToX64 st) bodies k nv nl ip fwd fwdTgts := by
  dsimp only [Rega.findGroupFwds, symStToX64]
  rw [collectRawFwds_eq h hh hs st.defs st.vecWidths fwd fwdTgts bodies nl _ _ _ .empty []]

private theorem lowerExpr_jump_nil (h : x64Isa.Hints) (hs : savedNoRsp h.saved = true)
    (E : Rega.Ext) (fn : Sym) {rs : List Ty} {ts : List Ty} (j : Nat)
    (args : Tup (Arg Rega.VNat) ts) (nv nl ip : Nat) (st : Rega.SymState vllX64IsaR)
    (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool)
    (hno : regsNoRsp st.regs = true) {c : List (Instr x64Arch)} {nv' nl' ip' : Nat}
    (hok : Rega.lowerExpr vllX64IsaR h E fn (.jump j args : Expr Rega.VNat Rega.LNat rs)
      nv nl ip st ft fwd fwdTgts = .ok (c, nv', nl', ip'))
    (hnil : asmX64List c = []) : c = [] := by
  dsimp only [Rega.lowerExpr] at hok
  obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
  cases hs0 : Rega.stepPre vllX64IsaR h ip st with
  | none => rw [hs0] at hok; cases hok
  | some p1 =>
    rcases p1 with ⟨mc, st1⟩
    rw [hs0] at hok
    have ⟨hno1, hnil1⟩ := hsp_p mc st1 hs0
    cases hen : h.entry.find? j with
    | none => simp [hen] at hok
    | some en =>
      simp only [hen] at hok
      cases hjt : Rega.jumpTargets vllX64IsaR args en.ploc with
      | none => simp [hjt] at hok
      | some argTgts =>
        simp only [hjt] at hok
        split at hok
        · cases hok
        · cases hsh : Rega.shuffle vllX64IsaR h.nslots h.saved st1 (en.live ++ argTgts) with
          | none => rw [hsh] at hok; cases hok
          | some p2 =>
            rcases p2 with ⟨sc, st2⟩
            have hnil2 := (shuffle_eq_and_noRsp hs st1 (en.live ++ argTgts) hno1).2 sc st2 hsh
            rw [hsh] at hok; cases hok
            simp only [asmX64List_append, List.append_eq_nil_iff] at hnil
            have hmc : mc = [] := hnil1 hnil.1.1
            have hsc : sc = [] := hnil2.2 hnil.1.2
            have hjmp := hnil.2
            cases hft : (ft == some (Rega.tgtLab fwd j)) with
            | true =>
              simp only [hft, ↓reduceIte] at hjmp ⊢
              simp [hmc, hsc]
            | false =>
              simp only [hft, Bool.false_eq_true, ↓reduceIte] at hjmp
              rw [vllR_jmp_eq] at hjmp; cases hjmp

private theorem finishJnzBranch_eq {rs : List Ty} (fn : Sym) (nl : Nat) (tgt? : Option Nat)
    (b_taken : Expr Rega.VNat Rega.LNat rs) (br c_ft c_taken : List vllX64IsaR.Directive)
    (nv2 nl2 ip2 : Nat)
    (hnil : ∀ j, tgt? = some j → ∀ {ts'} (j' : Rega.LNat ts') (args : Tup (Arg Rega.VNat) ts'),
      b_taken = .jump j' args → asmX64List c_taken = [] → c_taken = []) :
    mapRes (Rega.finishJnzBranch vllX64IsaR fn nl tgt? b_taken br c_ft c_taken nv2 nl2 ip2) =
      Rega.finishJnzBranch x64Isa fn nl tgt? b_taken (asmX64List br) (asmX64List c_ft)
        (asmX64List c_taken) nv2 nl2 ip2 := by
  cases tgt? with
  | none =>
    dsimp only [Rega.finishJnzBranch, mapRes]
    simp only [asmX64List_append, vllR_label_eq]
  | some j =>
    cases b_taken with
    | jump j' args =>
      dsimp only [Rega.finishJnzBranch]
      have heq : c_taken.isEmpty = (asmX64List c_taken).isEmpty := by
        cases c_taken with
        | nil => rfl
        | cons x xs =>
          have hne : asmX64List (x :: xs) ≠ [] := fun h0 => by
            have := hnil j rfl j' args rfl h0; cases this
          cases ha : asmX64List (x :: xs) with
          | nil => exact absurd ha hne
          | cons _ _ => rfl
      rw [heq]
      split
      · simp [mapRes, asmX64List_append]
      · rfl
    | _ => rfl

mutual
theorem lowerExpr_eq (h : x64Isa.Hints) (hh : hintsNoRsp h = true)
    (hs : savedNoRsp h.saved = true) (E : Rega.Ext) (fn : Sym) {rs : List Ty} :
    ∀ (e : Expr Rega.VNat Rega.LNat rs) (nv nl ip : Nat) (st : Rega.SymState vllX64IsaR)
      (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool),
      regsNoRsp st.regs = true → ExprNoSameExt e →
      mapRes (Rega.lowerExpr vllX64IsaR h E fn e nv nl ip st ft fwd fwdTgts) =
        Rega.lowerExpr x64Isa h E fn e nv nl ip (symStToX64 st) ft fwd fwdTgts
  | .let_ (ts := ts) op k, nv, nl, ip, st, ft, fwd, fwdTgts, hno, hexpr => by
    cases hexpr with | let_ hok_op hk_ex =>
    unfold Rega.lowerExpr
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx]; dsimp only
      have hno1 := (hsp_p mc st1 hs0).1
      rw [deferJnzNext_eq h hs fn nv nl ip st1 op (k (Tup.levels ts nv)) hno1,
        deferLeaNext_eq h hs nv ip st1 op (k (Tup.levels ts nv)) hno1]
      let df := Rega.deferJnzNext x64Isa h fn nv nl ip (symStToX64 st1) op (k (Tup.levels ts nv)) ||
        Rega.deferLeaNext x64Isa h nv ip (symStToX64 st1) op (k (Tup.levels ts nv))
      obtain ⟨hop, hop_p⟩ := lowerOp_eq_and_noRsp h hs nv ip st1 op df hno1 hok_op
      cases ho0 : Rega.lowerOp vllX64IsaR h nv ip st1 op df with
      | none =>
        have hox : Rega.lowerOp x64Isa h nv ip (symStToX64 st1) op df = none := by
          rw [← hop, ho0]; rfl
        rw [hox]; rfl
      | some p2 =>
        rcases p2 with ⟨c, st2⟩
        have hox : Rega.lowerOp x64Isa h nv ip (symStToX64 st1) op df =
            some (asmX64List c, symStToX64 st2) := by rw [← hop, ho0]; rfl
        rw [hox]
        have hno2 := hop_p c st2 ho0
        rw [mapRes_prepend, asmX64List_append]
        exact congrArg (Rega.prepend (asmX64List mc ++ asmX64List c))
          (lowerExpr_eq h hh hs E fn (k (Tup.levels ts nv)) (nv + ts.length) nl (ip + 1) st2
            ft fwd fwdTgts hno2 (hk_ex (Tup.levels ts nv)))
  | .load t a k, nv, nl, ip, st, ft, fwd, fwdTgts, hno, hexpr => by
    cases hexpr with | load hk_ex =>
    dsimp only [Rega.lowerExpr]
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx]; dsimp only
      have hno1 := (hsp_p mc st1 hs0).1
      rw [loadSextNext_eq h nv ip st1 t a (k nv) hno1]
      let fuse := Rega.loadSextNext x64Isa h nv ip (symStToX64 st1) t a (k nv)
      obtain ⟨hl_eq, hl_p⟩ := lowerLoad_eq_and_noRsp h hs nv ip st1 t a fuse hno1
      cases hl0 : Rega.lowerLoad vllX64IsaR h nv ip st1 t a fuse with
      | none =>
        have hlx : Rega.lowerLoad x64Isa h nv ip (symStToX64 st1) t a fuse = none := by
          rw [← hl_eq, hl0]; rfl
        rw [hlx]; rfl
      | some p2 =>
        rcases p2 with ⟨c, st2⟩
        have hlx : Rega.lowerLoad x64Isa h nv ip (symStToX64 st1) t a fuse =
            some (asmX64List c, symStToX64 st2) := by rw [← hl_eq, hl0]; rfl
        rw [hlx]
        have hno2 := hl_p c st2 hl0
        rw [mapRes_prepend, asmX64List_append]
        exact congrArg (Rega.prepend (asmX64List mc ++ asmX64List c))
          (lowerExpr_eq h hh hs E fn (k nv) (nv + 1) nl (ip + 1) st2 ft fwd fwdTgts hno2 (hk_ex nv))
  | .store v a k, nv, nl, ip, st, ft, fwd, fwdTgts, hno, hexpr => by
    cases hexpr with | store hk_ex =>
    dsimp only [Rega.lowerExpr]
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx]; dsimp only
      have hno1 := (hsp_p mc st1 hs0).1
      obtain ⟨hst_eq, hst_p⟩ := lowerStore_eq_and_noRsp st1 (h.variant.getD ip .default) _ v a hno1
      cases hst0 : Rega.lowerStore vllX64IsaR st1 (h.variant.getD ip .default) _ v a with
      | none =>
        have hstx : Rega.lowerStore x64Isa (symStToX64 st1)
            (h.variant.getD ip .default) _ v a = none := by rw [← hst_eq, hst0]; rfl
        rw [hstx]; rfl
      | some p2 =>
        rcases p2 with ⟨c, st2⟩
        have hstx : Rega.lowerStore x64Isa (symStToX64 st1)
            (h.variant.getD ip .default) _ v a = some (asmX64List c, symStToX64 st2) := by
          rw [← hst_eq, hst0]; rfl
        rw [hstx]
        have hno2 := hst_p c st2 hst0
        rw [mapRes_prepend, asmX64List_append]
        exact congrArg (Rega.prepend (asmX64List mc ++ asmX64List c))
          (lowerExpr_eq h hh hs E fn k nv nl (ip + 1) st2 ft fwd fwdTgts hno2 hk_ex)
  | .call f (as := as) (bs := bs) args k, nv, nl, ip, st, ft, fwd, fwdTgts, hno, hexpr => by
    cases hexpr with | call hk_ex =>
    dsimp only [Rega.lowerExpr]
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx]; dsimp only
      have hno1 := (hsp_p mc st1 hs0).1
      cases Rega.calleeAllowed E f as bs with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [vllR_assignArgs_eq, vllR_assignRets_eq]
        cases hal : x64Isa.assignArgs as with
        | none => rfl
        | some argLocs =>
          cases hrl : x64Isa.assignRets bs with
          | none => rfl
          | some retLocs =>
            have hrl_no : locsNoRsp retLocs = true :=
              assignRets_locsNoRsp (by rw [vllR_assignRets_eq]; exact hrl)
            dsimp only
            rw [abiTargets_eq]
            cases Rega.abiTargets x64Isa args argLocs with
            | none => rfl
            | some tgts =>
              dsimp only
              obtain ⟨hsh_eq, hsh_p⟩ := shuffle_eq_and_noRsp hs st1 tgts hno1
              cases hsh0 : Rega.shuffle vllX64IsaR h.nslots h.saved st1 tgts with
              | none =>
                have hshx : Rega.shuffle x64Isa h.nslots h.saved (symStToX64 st1) tgts =
                    none := by rw [← hsh_eq, hsh0]; rfl
                rw [hshx]; rfl
              | some p2 =>
                rcases p2 with ⟨sc, st2⟩
                have hshx : Rega.shuffle x64Isa h.nslots h.saved (symStToX64 st1) tgts =
                    some (asmX64List sc, symStToX64 st2) := by rw [← hsh_eq, hsh0]; rfl
                rw [hshx]; dsimp only
                have hno2 := (hsh_p sc st2 hsh0).1
                obtain ⟨hac_eq, hac_no⟩ := afterCallState_eq_and_noRsp h.saved st2 hno2
                obtain ⟨hbp_eq, hbp_p⟩ := bindAbiParams_eq_and_noRsp retLocs nv
                  (Rega.afterCallState vllX64IsaR h.saved st2) hrl_no hac_no
                rw [hac_eq] at hbp_eq
                cases hbp0 : Rega.bindAbiParams vllX64IsaR retLocs nv
                    (Rega.afterCallState vllX64IsaR h.saved st2) with
                | none =>
                  have hbpx : Rega.bindAbiParams x64Isa retLocs nv
                      (Rega.afterCallState x64Isa h.saved (symStToX64 st2)) = none := by
                    rw [← hbp_eq, hbp0]; rfl
                  rw [hbpx]; rfl
                | some st4 =>
                  have hbpx : Rega.bindAbiParams x64Isa retLocs nv
                      (Rega.afterCallState x64Isa h.saved (symStToX64 st2)) =
                      some (symStToX64 st4) := by rw [← hbp_eq, hbp0]; rfl
                  rw [hbpx]
                  have hno4 := hbp_p st4 hbp0
                  rw [mapRes_prepend]
                  simp only [asmX64List_append, canonAbiCode_eq, abiSkips_eq, vllR_call_eq,
                    symStToX64]
                  exact congrArg _ (lowerExpr_eq h hh hs E fn (k (Tup.levels bs nv))
                    (nv + bs.length) nl (ip + 1) st4 ft fwd fwdTgts hno4
                    (hk_ex (Tup.levels bs nv)))
  | .jnz (.imm b) t e, nv, nl, ip, st, ft, fwd, fwdTgts, hno, hexpr => by
    cases hexpr with | jnz ht_ex he_ex =>
    dsimp only [Rega.lowerExpr]
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx]
      have hno1 := (hsp_p mc st1 hs0).1
      rw [mapRes_prepend]
      cases b with
      | true =>
        exact congrArg (Rega.prepend (asmX64List mc))
          (lowerExpr_eq h hh hs E fn t nv nl (ip + 1) st1 ft fwd fwdTgts hno1 ht_ex)
      | false =>
        exact congrArg (Rega.prepend (asmX64List mc))
          (lowerExpr_eq h hh hs E fn e nv nl (ip + 1) st1 ft fwd fwdTgts hno1 he_ex)
  | .jnz (.var cx) t e, nv, nl, ip, st, ft, fwd, fwdTgts, hno, hexpr => by
    cases hexpr with | jnz ht_ex he_ex =>
    dsimp only [Rega.lowerExpr]
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx]; dsimp only
      have hno1 := (hsp_p mc st1 hs0).1
      have hfj := findJnzCond_eq h.nslots st1 cx
      cases hfc : Rega.findJnzCond vllX64IsaR h.nslots st1 cx with
      | none =>
        have hfcx : Rega.findJnzCond x64Isa h.nslots (symStToX64 st1) cx = none := by
          rw [← hfj, hfc]; rfl
        rw [hfcx]; rfl
      | some cond =>
        have hfcx : Rega.findJnzCond x64Isa h.nslots (symStToX64 st1) cx =
            some (mapJnzCond cond) := by rw [← hfj, hfc]; rfl
        rw [hfcx]; dsimp only
        obtain ⟨hjz_eq, hjz_p⟩ :=
          jnzSetup_eq_and_noRsp h fn nl (Rega.jnzIpT nv nl ip t e) (ip + 1) st1 t e ft cond fwd
            hno1
        cases hjz0 : Rega.jnzSetup vllX64IsaR h fn nl (Rega.jnzIpT nv nl ip t e) (ip + 1)
            st1 t e ft cond fwd with
        | none =>
          have hjzx : Rega.jnzSetup x64Isa h fn nl (Rega.jnzIpT nv nl ip t e) (ip + 1)
              (symStToX64 st1) t e ft (mapJnzCond cond) fwd = none := by rw [← hjz_eq, hjz0]; rfl
          rw [hjzx]; rfl
        | some p2 =>
          rcases p2 with ⟨inv, tgt?, br, stBr⟩
          have hjzx : Rega.jnzSetup x64Isa h fn nl (Rega.jnzIpT nv nl ip t e) (ip + 1)
              (symStToX64 st1) t e ft (mapJnzCond cond) fwd =
              some (inv, tgt?, asmX64List br, symStToX64 stBr) := by rw [← hjz_eq, hjz0]; rfl
          rw [hjzx]; dsimp only
          have hnoBr := hjz_p inv tgt? br stBr hjz0
          cases tgt? with
          | none =>
            dsimp only
            have ihe := lowerExpr_eq h hh hs E fn e nv (nl + 1) (ip + 1) stBr
              (if inv then ft else none) fwd fwdTgts hnoBr he_ex
            cases he0 : Rega.lowerExpr vllX64IsaR h E fn e nv (nl + 1) (ip + 1) stBr
                (if inv then ft else none) fwd fwdTgts with
            | error err =>
              have hex : Rega.lowerExpr x64Isa h E fn e nv (nl + 1) (ip + 1) (symStToX64 stBr)
                  (if inv then ft else none) fwd fwdTgts = .error err := by
                rw [← ihe, he0]; rfl
              rw [hex]; rfl
            | ok resE =>
              rcases resE with ⟨ce, nv1, nl1, ip1⟩
              have hex : Rega.lowerExpr x64Isa h E fn e nv (nl + 1) (ip + 1) (symStToX64 stBr)
                  (if inv then ft else none) fwd fwdTgts =
                  .ok (asmX64List ce, nv1, nl1, ip1) := by rw [← ihe, he0]; rfl
              rw [hex]; dsimp only
              have iht := lowerExpr_eq h hh hs E fn t nv1 nl1 ip1 stBr
                (if inv then none else ft) fwd fwdTgts hnoBr ht_ex
              cases ht0 : Rega.lowerExpr vllX64IsaR h E fn t nv1 nl1 ip1 stBr
                  (if inv then none else ft) fwd fwdTgts with
              | error err =>
                have htx : Rega.lowerExpr x64Isa h E fn t nv1 nl1 ip1 (symStToX64 stBr)
                    (if inv then none else ft) fwd fwdTgts = .error err := by
                  rw [← iht, ht0]; rfl
                rw [htx]; rfl
              | ok resT =>
                rcases resT with ⟨ct, nv2, nl2, ip2⟩
                have htx : Rega.lowerExpr x64Isa h E fn t nv1 nl1 ip1 (symStToX64 stBr)
                    (if inv then none else ft) fwd fwdTgts =
                    .ok (asmX64List ct, nv2, nl2, ip2) := by rw [← iht, ht0]; rfl
                rw [htx]; dsimp only; rw [mapRes_prepend]; congr 1
                cases inv with
                | true =>
                  exact finishJnzBranch_eq fn nl none e br ct ce nv2 nl2 ip2
                    fun _ h0 => by cases h0
                | false =>
                  exact finishJnzBranch_eq fn nl none t br ce ct nv2 nl2 ip2
                    fun _ h0 => by cases h0
          | some j =>
            dsimp only
            have ihe := lowerExpr_eq h hh hs E fn e nv (nl + 1) (ip + 1) stBr
              (if inv then some (Rega.tgtLab fwd j) else ft) fwd fwdTgts hnoBr he_ex
            cases he0 : Rega.lowerExpr vllX64IsaR h E fn e nv (nl + 1) (ip + 1) stBr
                (if inv then some (Rega.tgtLab fwd j) else ft) fwd fwdTgts with
            | error err =>
              have hex : Rega.lowerExpr x64Isa h E fn e nv (nl + 1) (ip + 1) (symStToX64 stBr)
                  (if inv then some (Rega.tgtLab fwd j) else ft) fwd fwdTgts = .error err := by
                rw [← ihe, he0]; rfl
              rw [hex]; rfl
            | ok resE =>
              rcases resE with ⟨ce, nv1, nl1, ip1⟩
              have hex : Rega.lowerExpr x64Isa h E fn e nv (nl + 1) (ip + 1) (symStToX64 stBr)
                  (if inv then some (Rega.tgtLab fwd j) else ft) fwd fwdTgts =
                  .ok (asmX64List ce, nv1, nl1, ip1) := by rw [← ihe, he0]; rfl
              rw [hex]; dsimp only
              have iht := lowerExpr_eq h hh hs E fn t nv1 nl1 ip1 stBr
                (if inv then ft else some (Rega.tgtLab fwd j)) fwd fwdTgts hnoBr ht_ex
              cases ht0 : Rega.lowerExpr vllX64IsaR h E fn t nv1 nl1 ip1 stBr
                  (if inv then ft else some (Rega.tgtLab fwd j)) fwd fwdTgts with
              | error err =>
                have htx : Rega.lowerExpr x64Isa h E fn t nv1 nl1 ip1 (symStToX64 stBr)
                    (if inv then ft else some (Rega.tgtLab fwd j)) fwd fwdTgts = .error err := by
                  rw [← iht, ht0]; rfl
                rw [htx]; rfl
              | ok resT =>
                rcases resT with ⟨ct, nv2, nl2, ip2⟩
                have htx : Rega.lowerExpr x64Isa h E fn t nv1 nl1 ip1 (symStToX64 stBr)
                    (if inv then ft else some (Rega.tgtLab fwd j)) fwd fwdTgts =
                    .ok (asmX64List ct, nv2, nl2, ip2) := by rw [← iht, ht0]; rfl
                rw [htx]; dsimp only; rw [mapRes_prepend]; congr 1
                cases inv with
                | true =>
                  exact finishJnzBranch_eq fn nl (some j) e br ct ce nv2 nl2 ip2
                    fun _ _ _ j' args hj =>
                      lowerExpr_jump_nil h hs E fn j' args nv (nl + 1) (ip + 1) stBr _
                        fwd fwdTgts hnoBr (hj ▸ he0)
                | false =>
                  exact finishJnzBranch_eq fn nl (some j) t br ce ct nv2 nl2 ip2
                    fun _ _ _ j' args hj =>
                      lowerExpr_jump_nil h hs E fn j' args nv1 nl1 ip1 stBr _
                        fwd fwdTgts hnoBr (hj ▸ ht0)
  | .jump j args, nv, nl, ip, st, ft, fwd, _, hno, _ => by
    dsimp only [Rega.lowerExpr]
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; cases h.entry.find? j <;> rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx]
      have hno1 := (hsp_p mc st1 hs0).1
      cases hen : h.entry.find? j with
      | none => rfl
      | some en =>
        dsimp only
        rw [jumpTargets_eq]
        cases Rega.jumpTargets x64Isa args en.ploc with
        | none => rfl
        | some argTgts =>
          dsimp only
          rw [list_all_congr' (fun p => jumpLocOk_eq h.nslots p.2) (en.live ++ argTgts)]
          split
          · rfl
          · obtain ⟨hsh_eq, _⟩ := shuffle_eq_and_noRsp hs st1 (en.live ++ argTgts) hno1
            cases hsh0 : Rega.shuffle vllX64IsaR h.nslots h.saved st1 (en.live ++ argTgts) with
            | none =>
              have hshx : Rega.shuffle x64Isa h.nslots h.saved (symStToX64 st1)
                  (en.live ++ argTgts) = none := by rw [← hsh_eq, hsh0]; rfl
              rw [hshx]; rfl
            | some p2 =>
              rcases p2 with ⟨sc, st2⟩
              have hshx : Rega.shuffle x64Isa h.nslots h.saved (symStToX64 st1)
                  (en.live ++ argTgts) = some (asmX64List sc, symStToX64 st2) := by
                rw [← hsh_eq, hsh0]; rfl
              rw [hshx]
              dsimp only [mapRes]
              rw [asmX64List_append, asmX64List_append]
              split <;> simp only [asmX64List_nil, vllR_jmp_eq]
  | .ret vs, nv, nl, ip, st, _, _, _, hno, _ => by
    dsimp only [Rega.lowerExpr]
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; rw [vllR_assignRets_eq]; cases x64Isa.assignRets rs <;> rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx, vllR_assignRets_eq]
      cases x64Isa.assignRets rs with
      | none => rfl
      | some retLocs =>
        rw [lowerTail_eq h hs E st1 mc _ vs retLocs nv nl ip (hsp_p mc st1 hs0).1, vllR_ret_eq]
  | .exit f (as := as) args, nv, nl, ip, st, _, _, _, hno, _ => by
    dsimp only [Rega.lowerExpr]
    obtain ⟨hsp, hsp_p⟩ := stepPre_eq_and_noRsp h ip hs st hno
    cases hs0 : Rega.stepPre vllX64IsaR h ip st with
    | none =>
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) = none := by rw [← hsp, hs0]; rfl
      rw [hsx]; rw [vllR_assignArgs_eq]; cases x64Isa.assignArgs as <;> rfl
    | some p1 =>
      rcases p1 with ⟨mc, st1⟩
      have hsx : Rega.stepPre x64Isa h ip (symStToX64 st) =
          some (asmX64List mc, symStToX64 st1) := by rw [← hsp, hs0]; rfl
      rw [hsx, vllR_assignArgs_eq]
      cases x64Isa.assignArgs as with
      | none => rfl
      | some argLocs =>
        dsimp only; split
        · rfl
        · rw [lowerTail_eq h hs E st1 mc _ args argLocs nv nl ip (hsp_p mc st1 hs0).1,
            vllR_exitJmp_eq]
  | .hlt, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, nv, nl, ip, st, ft, fwd, fwdTgts, hno, hexpr => by
    cases hexpr with | group hb_ex hk_ex =>
    dsimp only [Rega.lowerExpr]
    let ls := Tup.levels sig nl
    rw [findGroupFwds_eq h hh hs st (bodies ls) (k ls) nv nl ip fwd fwdTgts]
    let p := Rega.findGroupFwds x64Isa h (symStToX64 st) (bodies ls) (k ls) nv nl ip fwd fwdTgts
    have ihk := lowerExpr_eq h hh hs E fn (k ls) nv (nl + sig.length) ip st
      (Rega.firstNonFwd p.1 (bodies ls) nl ft) p.1 p.2 hno (hk_ex ls)
    cases hk0 : Rega.lowerExpr vllX64IsaR h E fn (k ls) nv (nl + sig.length) ip st
        (Rega.firstNonFwd p.1 (bodies ls) nl ft) p.1 p.2 with
    | error err =>
      have hkx : Rega.lowerExpr x64Isa h E fn (k ls) nv (nl + sig.length) ip (symStToX64 st)
          (Rega.firstNonFwd p.1 (bodies ls) nl ft) p.1 p.2 = .error err := by
        rw [← ihk, hk0]; rfl
      rw [hkx]; rfl
    | ok resK =>
      rcases resK with ⟨ck, nv1, nl1, ip1⟩
      have hkx : Rega.lowerExpr x64Isa h E fn (k ls) nv (nl + sig.length) ip (symStToX64 st)
          (Rega.firstNonFwd p.1 (bodies ls) nl ft) p.1 p.2 =
          .ok (asmX64List ck, nv1, nl1, ip1) := by rw [← ihk, hk0]; rfl
      rw [hkx]
      rw [mapRes_prepend]
      exact congrArg (Rega.prepend (asmX64List ck))
        (lowerBlocks_eq h hh hs E fn (bodies ls) nl nv1 nl1 ip1 st.defs st.vecWidths ft p.1 p.2
          (hb_ex ls))

theorem lowerBlocks_eq (h : x64Isa.Hints) (hh : hintsNoRsp h = true)
    (hs : savedNoRsp h.saved = true) (E : Rega.Ext) (fn : Sym) {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks Rega.VNat Rega.LNat rs sig)
      (lid nv nl ip : Nat) (defs : Trie Rega.DefFact) (vw : Trie SlotWidth)
      (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool),
      BlocksNoSameExt bs →
      mapRes (Rega.lowerBlocks vllX64IsaR h E fn bs lid nv nl ip defs vw ft fwd fwdTgts) =
        Rega.lowerBlocks x64Isa h E fn bs lid nv nl ip defs vw ft fwd fwdTgts
  | _, .nil, _, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts, hblks => by
    cases hblks with | cons hb_ex hbs_ex =>
    dsimp only [Rega.lowerBlocks]
    cases fwd.find? lid with
    | some fwdTgt =>
      rw [blockTrampoline?_eq h hh hs defs vw lid nv ip b]
      cases Rega.blockTrampoline? x64Isa h defs vw lid nv ip b with
      | none => rfl
      | some j' =>
        dsimp only; split
        · rfl
        · exact lowerBlocks_eq h hh hs E fn bs (lid + 1) (nv + ts.length) nl (ip + 1)
            defs vw ft fwd fwdTgts hbs_ex
    | none =>
      cases hfen : h.entry.find? lid with
      | none => rfl
      | some en =>
        dsimp only
        have hen := trieAll_find_entry hh hfen
        simp only [entryNoRsp, Bool.and_eq_true] at hen
        rw [entryScopeOk_eq]
        cases Rega.entryScopeOk (I := x64Isa) nv en with
        | false => rfl
        | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨hb_eq, hb_no⟩ := buildEntryBase_eq_and_noRsp h.nslots vw en.live
            { regs := [], slots := .empty, defs := defs, vecWidths := vw } hen.1 rfl
          cases hbase : Rega.buildEntryBase vllX64IsaR h.nslots vw en.live
              { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
          | none =>
            have hbx : Rega.buildEntryBase x64Isa h.nslots vw en.live
                { regs := [], slots := .empty, defs := defs, vecWidths := vw } = none := by
              rw [← hb_eq, hbase]; rfl
            rw [hbx]; rfl
          | some baseSt =>
            have hbx : Rega.buildEntryBase x64Isa h.nslots vw en.live
                { regs := [], slots := .empty, defs := defs, vecWidths := vw } =
                some (symStToX64 baseSt) := by rw [← hb_eq, hbase]; rfl
            rw [hbx]; dsimp only
            have hno_b := hb_no baseSt hbase
            obtain ⟨hp_eq, hp_no⟩ := bindBlockParams_eq_and_noRsp h.nslots ts en.ploc nv baseSt
              hen.2 hno_b
            cases hinit : Rega.bindBlockParams vllX64IsaR h.nslots ts en.ploc nv baseSt with
            | none =>
              have hix : Rega.bindBlockParams x64Isa h.nslots ts en.ploc nv
                  (symStToX64 baseSt) = none := by rw [← hp_eq, hinit]; rfl
              rw [hix]; rfl
            | some initSt =>
              have hix : Rega.bindBlockParams x64Isa h.nslots ts en.ploc nv
                  (symStToX64 baseSt) = some (symStToX64 initSt) := by rw [← hp_eq, hinit]; rfl
              rw [hix]; dsimp only
              have hno_i := hp_no initSt hinit
              let ftB := Rega.firstNonFwd fwd bs (lid + 1) ft
              have ihb := lowerExpr_eq h hh hs E fn (b (Tup.levels ts nv)) (nv + ts.length) nl ip
                initSt ftB fwd fwdTgts hno_i (hb_ex (Tup.levels ts nv))
              cases hb0 : Rega.lowerExpr vllX64IsaR h E fn (b (Tup.levels ts nv))
                  (nv + ts.length) nl ip initSt ftB fwd fwdTgts with
              | error err =>
                have hbx' : Rega.lowerExpr x64Isa h E fn (b (Tup.levels ts nv))
                    (nv + ts.length) nl ip (symStToX64 initSt) ftB fwd fwdTgts =
                    .error err := by rw [← ihb, hb0]; rfl
                dsimp only [ftB] at hbx'
                rw [hbx']; rfl
              | ok resB =>
                rcases resB with ⟨cb, nv1, nl1, ip1⟩
                have hbx' : Rega.lowerExpr x64Isa h E fn (b (Tup.levels ts nv))
                    (nv + ts.length) nl ip (symStToX64 initSt) ftB fwd fwdTgts =
                    .ok (asmX64List cb, nv1, nl1, ip1) := by rw [← ihb, hb0]; rfl
                dsimp only [ftB] at hbx'
                rw [hbx']
                rw [mapRes_prepend]
                have hlbl : asmX64List [vllX64FrameR.label (Rega.lname fn lid)] =
                    [x64Isa.frame.label (Rega.lname fn lid)] := vllR_label_eq _
                simp only [asmX64List, List.flatMap_cons, List.flatMap_nil,
                  List.append_nil] at hlbl ⊢
                rw [hlbl]
                exact congrArg
                  (Rega.prepend (x64Isa.frame.label (Rega.lname fn lid) :: asmX64List cb))
                  (lowerBlocks_eq h hh hs E fn bs (lid + 1) nv1 nl1 ip1 defs vw ft fwd fwdTgts
                    hbs_ex)
end

end LeanQbe.T.Amd64
