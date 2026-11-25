module

public import LeanQbe.T.Amd64.IselLemmasBitcnt

/-!
# x64 Scalar `GprTarget` Proofs — Part 5

1-for-1 `x64SupportsScalarOp` soundness & completeness, unified `x64Gpr_op_spec`,
and assembled `x64GprSpec : GprTarget x64Mach x64Gpr x64Scratch`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Amd64

open LeanQbe.T

@[expose] public section

/-! ## 1. `supportsScalarOp` Soundness & Completeness -/

private theorem none_ne_some {α : Type} {P : Prop} {x : Option α} {y : α}
    (hn : x = none) (hs : x = some y) : P := by cases (hn.symm.trans hs)

private theorem false_ne_true_of {P : Prop} {b : Bool} (hf : b = false) (ht : b = true) : P := by
  cases (hf.symm.trans ht)

private theorem width_mem {F : Nat → Type} {β : Type} {n : Nat} (x : F n)
    (f : (w : Width) → F w.bits → Option β) {y : β} (h : withWidth n x f = some y) :
    x64BitWidths.contains n = true := by
  unfold withWidth at h; split at h <;> first | contradiction | rfl

private theorem wide_mem {F : Nat → Type} {β : Type} {n : Nat} (x : F n)
    (f : (w : Width) → F w.bits → Option β) {y : β} (h : withWideWidth n x f = some y) :
    x64WideWidths.contains n = true := by
  unfold withWideWidth at h; split at h <;> first | contradiction | rfl

private theorem mem_x64BitWidths {n : Nat} (h : x64BitWidths.contains n = true) :
    n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by simp [x64BitWidths] at h; exact h

private theorem mem_x64WideWidths {n : Nat} (h : x64WideWidths.contains n = true) :
    n = 32 ∨ n = 64 := by simp [x64WideWidths] at h; exact h

private theorem arg1_nv {t : Ty} {ts : List Ty} {pas : Tup (PArg Reg64 RegMm CondCode) (t :: ts)}
    (h : tupArgVecs pas = []) : ∀ r, pas.1 ≠ .vec r := fun r he => by
  rcases pas with ⟨pa, as⟩; simp only at he; subst he; simp [tupArgVecs] at h

private theorem arg2_nv {t1 t2 : Ty} {ts : List Ty}
    {pas : Tup (PArg Reg64 RegMm CondCode) (t1 :: t2 :: ts)}
    (h : tupArgVecs pas = []) : ∀ r, pas.2.1 ≠ .vec r := fun r he => by
  rcases pas with ⟨pa, pb, as⟩; simp only at he; subst he; cases pa <;> simp [tupArgVecs] at h

private theorem arg3_nv {t1 t2 t3 : Ty} {ts : List Ty}
    {pas : Tup (PArg Reg64 RegMm CondCode) (t1 :: t2 :: t3 :: ts)}
    (h : tupArgVecs pas = []) : ∀ r, pas.2.2.1 ≠ .vec r := fun r he => by
  rcases pas with ⟨pa, pb, pc, as⟩; simp only at he; subst he
  cases pa <;> cases pb <;> simp [tupArgVecs] at h

theorem x64Op_supportsScalarOp {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    (h0 : x64Gpr.op code pas dsts vh = some (c, clob)) (u : Tup (Arg (fun _ => Unit)) sig) :
    x64Gpr.supportsScalarOp code u = true := by
  dsimp only [x64Gpr, x64Op] at h0 ⊢
  obtain ⟨ci, h, rfl⟩ := emitCleanPair_eq_some.mp h0
  cases code
  case copy t | neg t | not t =>
    cases t <;> (first
      | rfl
      | exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) h
      | (rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;>
          first | exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
                | (dsimp only [x64OpIns] at h; first | contradiction | exact width_mem _ _ h)))
  case add t | sub t | mul t | and t | or t | xor t | shl t | lshr t | ashr t | rotl t | rotr t =>
    cases t <;> (first
      | rfl
      | exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) h
      | (rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;>
          first | exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
                | (dsimp only [x64OpIns] at h; first | contradiction | exact width_mem _ _ h)))
  case select t =>
    cases t <;> (first
      | exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) h
      | (rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;>
          first | exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
                | (dsimp only [x64OpIns] at h; first | contradiction | exact width_mem _ _ h)))
  case bswap t =>
    cases t with
    | bits n =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
      rcases (by omega : n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64)) with
        rfl | rfl | rfl | ⟨h1, h2, h3⟩
      · rfl
      · rfl
      · rfl
      · exfalso; change opBswapIns n pa _ = _ at h; unfold opBswapIns at h; cases n <;> simp_all
    | _ => exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) h
  case clz n | cls n | ctz n | popcnt n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
    dsimp only [x64OpIns] at h; exact width_mem _ _ h
  case cmp co t m hm =>
    cases t <;> (first
      | exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) h
      | (subst hm; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
         dsimp only [x64OpIns] at h; first | contradiction | exact width_mem _ _ h))
  case zext m n | sext m n | trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
    first
    | (change opZextIns m n pa _ = _ at h; unfold opZextIns at h; split at h <;> first
        | contradiction
        | (change (x64BitWidths.contains m && x64BitWidths.contains n &&
                   Nat.ble (m + 1) n) = true; simp_all))
    | (change opSextIns m n pa _ = _ at h; unfold opSextIns at h; split at h <;> first
        | contradiction
        | (change (x64BitWidths.contains m && x64BitWidths.contains n &&
                   Nat.ble (m + 1) n) = true; simp_all))
    | (change opTruncIns m n pa _ = _ at h; unfold opTruncIns at h; split at h <;> first
        | contradiction
        | (change (x64BitWidths.contains m && x64BitWidths.contains n &&
                   Nat.ble (n + 1) m) = true; simp_all))
  case ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
    change (if x64BitWidths.contains n = true then _ else none) = _ at h
    split at h <;> first | exact ‹x64BitWidths.contains n = true› | contradiction
  case fshl n | fshr n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
    dsimp only [x64OpIns] at h; exact wide_mem _ _ h
  case addc n | subb n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨d0, d1, ⟨⟩⟩
    dsimp only [x64OpIns] at h; exact wide_mem _ _ h
  case umulw n | smulw n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d0, d1, ⟨⟩⟩
    dsimp only [x64OpIns] at h; exact wide_mem _ _ h
  case udiv n | sdiv n | urem n | srem n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
    dsimp only [x64OpIns] at h; exact width_mem _ _ h
  case bitcast t1 t2 hb =>
    cases t1 <;> cases t2 <;> try exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) h
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) h
    change (if x64BitWidths.contains _ = true then withWidth _ _ _ else none) = _ at h
    split at h <;> try contradiction
    next hn =>
      have hm := width_mem _ _ h
      change (x64BitWidths.contains _ && x64BitWidths.contains _) = true
      rw [Bool.and_eq_true]; exact ⟨hm, hn⟩
  all_goals exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) h

private theorem opCopyBitsIns_isSome (w : Width) {pa : PArg Reg64 RegMm CondCode (.bits w.bits)}
    (rd : Reg64) (ha : ∀ r, pa ≠ .vec r) : (opCopyBitsIns w pa rd).isSome = true := by
  cases pa with | vec r => exact absurd rfl (ha r) | _ => simp [opCopyBitsIns]; try split <;> rfl

private theorem opBinIns_isSome (w : Width) (k : AluBinKind)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} (rd : Reg64)
    (ha : ∀ r, pa ≠ .vec r) (hb : ∀ r, pb ≠ .vec r) :
    (opBinIns w k pa pb rd .default).isSome = true := by
  cases pa <;> cases pb <;> first
    | exact absurd rfl (ha _) | exact absurd rfl (hb _)
    | ((unfold opBinIns opBinLeaReg? opBinLeaImm?; dsimp only; repeat' split) <;> rfl)

private theorem opShiftIns_isSome (w : Width) (sk : ShiftKind)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} (rd : Reg64)
    (ha : ∀ r, pa ≠ .vec r) (hb : ∀ r, pb ≠ .vec r) : (opShiftIns w sk pa pb rd).isSome = true := by
  cases w <;> cases sk <;> cases pa <;> cases pb <;>
    first | exact absurd rfl (ha _) | exact absurd rfl (hb _) |
      ((simp [opShiftIns, argToBitsI, opCopyBitsIns, shiftMaskRcxIns,
          ShiftKind.isRot, ShiftKind.toBmi2Op?];
        repeat' split) <;> rfl)

private theorem opBitcntIns_isSome (w : Width) (bk : BitcntKind)
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} (rd : Reg64)
    (ha : ∀ r, pa ≠ .vec r) : (opBitcntIns w bk pa rd).isSome = true := by
  cases pa with | vec r => exact absurd rfl (ha r) | _ => rfl

private theorem opSelectIns_isSome (w : Width) {pc : PArg Reg64 RegMm CondCode .bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} (rd : Reg64)
    (hc : ∀ r, pc ≠ .vec r) (ha : ∀ r, pa ≠ .vec r) (hb : ∀ r, pb ≠ .vec r) :
    (opSelectIns w pc pa pb rd).isSome = true := by
  cases pc with
  | vec r => exact absurd rfl (hc r)
  | imm b =>
    cases b <;> first | exact opCopyBitsIns_isSome w rd ha | exact opCopyBitsIns_isSome w rd hb
  | flag _ | gpr _ =>
    cases pa <;> cases pb <;> first
      | exact absurd rfl (ha _) | exact absurd rfl (hb _)
      | ((simp [opSelectIns, selectFlagSeqIns]; repeat' split) <;> rfl)

private theorem opFunnelIns_isSome (w : Width) (isRight : Bool)
    {pa pb pc : PArg Reg64 RegMm CondCode (.bits w.bits)} (rd : Reg64)
    (ha : ∀ r, pa ≠ .vec r) (hb : ∀ r, pb ≠ .vec r) (hc : ∀ r, pc ≠ .vec r) :
    (opFunnelIns w isRight pa pb pc rd).isSome = true := by
  cases isRight <;> cases pa <;> cases pb <;> cases pc <;> first
    | exact absurd rfl (ha _) | exact absurd rfl (hb _) | exact absurd rfl (hc _)
    | ((simp [opFunnelIns, argToBitsI, opCopyBitsIns]; repeat' split) <;> rfl)

private theorem carryCoreIns_isSome (w : Width) (isComm supp : Bool)
    (mr : Reg64 → Reg64 → Instr) (mi : Reg64 → BitVec w.bits → Instr)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} (rd : Reg64)
    (ha : ∀ r, pa ≠ .vec r) (hb : ∀ r, pb ≠ .vec r) :
    (carryCoreIns w isComm mr mi supp pa pb rd).isSome = true := by
  cases pa <;> cases pb <;> first
    | exact absurd rfl (ha _) | exact absurd rfl (hb _)
    | ((simp [carryCoreIns]; repeat' split) <;> rfl)

private theorem isSome_bind_some {α β : Type} (o : Option α) (f : α → β) :
    (o.bind fun x => some (f x)).isSome = o.isSome := by cases o <;> rfl

theorem x64SupportsScalarOp_complete {sig rs : List Ty} {code : OpCode sig rs}
    {u : Tup (Arg (fun _ => Unit)) sig}
    (hsup : x64Gpr.supportsScalarOp code u = true)
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    (hp : tupArgVecs pas = [])
    (hd : tupDstVecs dsts = [] ∧ (tupDstGprs dsts).length = rs.length ∧ (tupDstGprs dsts).Nodup ∧
      ∀ r ∈ tupDstGprs dsts, r ∉ x64Scratch) :
    (x64Gpr.op code pas dsts .default).isSome = true := by
  dsimp only [x64Gpr, x64Op] at hsup ⊢
  simp only [emitCleanPair_isSome]
  cases code
  all_goals first | exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup | skip
  case copy t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    · have ha := arg1_nv hp; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd <;> simp [tupDstGprs] at hd
      cases pa with
      | vec r => exact absurd rfl (ha r)
      | _ => dsimp only [x64OpIns]; simp [opCopyBoolIns] <;> try split <;> rfl
    · rename_i n; change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> exact opCopyBitsIns_isSome _ _ ha
  case neg t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i n; change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> cases pa <;> first
      | exact absurd rfl (ha _) | (dsimp only [x64OpIns]; simp [opNegIns] <;> rfl)
  case not t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    · have ha := arg1_nv hp; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd <;> simp [tupDstGprs] at hd
      cases pa <;> first
        | exact absurd rfl (ha _)
        | (dsimp only [x64OpIns]; simp [opBoolNotIns] <;>
            try split <;> rfl)
    · rename_i n; change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> cases pa <;> first
        | exact absurd rfl (ha _) | (dsimp only [x64OpIns]; simp [opNotIns] <;> rfl)
  case add t | sub t | mul t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i n; change x64BitWidths.contains n = true at hsup
    have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> exact opBinIns_isSome _ _ _ ha hb
  case and t | or t | xor t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    · have ha := arg1_nv hp; have hb := arg2_nv hp
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      cases pa <;> cases pb <;> first
        | exact absurd rfl (ha _) | exact absurd rfl (hb _)
        | (dsimp only [x64OpIns]
           simp only [opBoolBinIns, boolBinSelfIns, boolBinDstIns, boolArgTo8I]
           repeat' split
           all_goals rfl)
    · rename_i n; change x64BitWidths.contains n = true at hsup
      have ha := arg1_nv hp; have hb := arg2_nv hp
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> exact opBinIns_isSome _ _ _ ha hb
  case shl t | lshr t | ashr t | rotl t | rotr t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i n; change x64BitWidths.contains n = true at hsup
    have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> exact opShiftIns_isSome _ _ _ ha hb
  case bswap t =>
    cases t with
    | bits n =>
      change [16, 32, 64].contains n = true at hsup; have ha := arg1_nv hp
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      rcases (by omega : n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64)) with
        rfl | rfl | rfl | ⟨h1, h2, h3⟩
      · cases pa <;> first
          | exact absurd rfl (ha _) | (dsimp only [x64OpIns]; simp [opBswapIns] <;> rfl)
      · cases pa <;> first
          | exact absurd rfl (ha _) | (dsimp only [x64OpIns]; simp [opBswapIns] <;> rfl)
      · cases pa <;> first
          | exact absurd rfl (ha _) | (dsimp only [x64OpIns]; simp [opBswapIns] <;> rfl)
      · exfalso; revert hsup; cases n <;> simp [h1, h2, h3]
    | _ => exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
  case clz n | cls n | ctz n | popcnt n =>
    change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> exact opBitcntIns_isSome _ _ _ ha
  case cmp co t m hm =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i n; change x64BitWidths.contains n = true at hsup; subst hm
    have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;>
      cases pa <;> cases pb <;> first
        | exact absurd rfl (ha _) | exact absurd rfl (hb _)
        | ((dsimp only [x64OpIns]; simp [withWidth, opCmpIns, cmpDirectIns, cmpRegImmIns];
            repeat' split) <;> rfl)
  case select t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i n; change x64BitWidths.contains n = true at hsup
    have hc' := arg1_nv hp; have ha := arg2_nv hp; have hb := arg3_nv hp
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;>
      exact opSelectIns_isSome _ _ hc' ha hb
  case zext m n | sext m n | trunc m n =>
    first | change (x64BitWidths.contains m && x64BitWidths.contains n &&
                    Nat.ble (m + 1) n) = true at hsup
          | change (x64BitWidths.contains m && x64BitWidths.contains n &&
                    Nat.ble (n + 1) m) = true at hsup
    simp only [Bool.and_eq_true, Nat.ble_eq] at hsup; rcases hsup with ⟨⟨hm, hn⟩, hord⟩
    have ha := arg1_nv hp; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hm with rfl | rfl | rfl | rfl <;>
      rcases mem_x64BitWidths hn with rfl | rfl | rfl | rfl <;> try omega
    all_goals (cases pa <;> first
      | exact absurd rfl (ha _)
      | ((dsimp only [x64OpIns]
          simp [opZextIns, opSextIns, opTruncIns, x64BitWidths]; repeat' split) <;> rfl))
  case ofBool n =>
    change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    cases pa <;> first
      | exact absurd rfl (ha _) | (dsimp only [x64OpIns]; rw [hsup]; simp [opOfBoolIns] <;> rfl)
  case fshl n | fshr n =>
    change x64WideWidths.contains n = true at hsup
    have ha := arg1_nv hp; have hb := arg2_nv hp; have hc' := arg3_nv hp
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64WideWidths hsup with rfl | rfl <;> exact opFunnelIns_isSome _ _ _ ha hb hc'
  case addc n | subb n =>
    change x64WideWidths.contains n = true at hsup
    rcases mem_x64WideWidths hsup with rfl | rfl <;> (
      rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; have ha : ∀ r, pa ≠ .vec r := arg1_nv hp
      have hb : ∀ r, pb ≠ .vec r := arg2_nv hp; have hc' : ∀ r, pc ≠ .vec r := arg3_nv hp
      rcases dsts with ⟨d0, d1, ⟨⟩⟩
      cases d0 <;> cases d1 <;> simp [tupDstGprs, List.nodup_cons] at hd
      rename_i r0 r1; have hne : (r1 != r0) = true := by
        cases r0 <;> cases r1 <;> first | exact absurd rfl hd.2.1 | rfl
      cases pc with
      | vec r => exact absurd rfl (hc' r)
      | imm b =>
        cases b <;> dsimp only [x64OpIns] <;>
          simp [withWideWidth, opAddcIns, opSubbIns, hne, isSome_bind_some] <;>
          exact carryCoreIns_isSome _ _ _ _ _ r0 ha hb
      | flag cc =>
        cases cc <;> dsimp only [x64OpIns] <;>
          simp [withWideWidth, opAddcIns, opSubbIns, hne, isSome_bind_some] <;>
          exact carryCoreIns_isSome _ _ _ _ _ r0 ha hb
      | gpr _ =>
        dsimp only [x64OpIns]
        simp [withWideWidth, opAddcIns, opSubbIns, hne, isSome_bind_some]
        exact carryCoreIns_isSome _ _ _ _ _ r0 ha hb)
  case umulw n | smulw n =>
    change x64WideWidths.contains n = true at hsup; have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d0, d1, ⟨⟩⟩
    cases d0 <;> cases d1 <;> simp [tupDstGprs, List.nodup_cons] at hd
    rename_i rlo rhi; have hne : (rlo == rhi) = false := by
      cases rlo <;> cases rhi <;> first | exact absurd rfl hd.2.1 | rfl
    rcases mem_x64WideWidths hsup with rfl | rfl <;> cases pa <;> cases pb <;> first
      | exact absurd rfl (ha _) | exact absurd rfl (hb _)
      | (dsimp only [x64OpIns]; simp [withWideWidth, opMulwIns, argToBitsI, hne])
  case udiv n | sdiv n | urem n | srem n =>
    change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> simp [tupDstGprs, x64Scratch] at hd; rename_i rd
    have h10 : (rd == .r10) = false := by cases rd <;> first | exact absurd rfl hd.2.1 | rfl
    have h11 : (rd == .r11) = false := by cases rd <;> first | exact absurd rfl hd.2.2 | rfl
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> cases pa <;> cases pb <;> first
      | exact absurd rfl (ha _) | exact absurd rfl (hb _)
      | (dsimp only [x64OpIns]; simp [withWidth, opDivIns, h10, h11])
  case bitcast t1 t2 hb =>
    cases t1 <;> cases t2 <;>
      try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i m n
    change (x64BitWidths.contains m && x64BitWidths.contains n) = true at hsup
    simp only [Bool.and_eq_true] at hsup
    have ha := arg1_nv hp; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup.1 with rfl | rfl | rfl | rfl <;>
      (dsimp only [x64OpIns]; rw [hsup.2]; exact opCopyBitsIns_isSome _ _ ha)

/-! ## 2. Unified `x64Gpr_op_spec` and `x64GprSpec` -/

private theorem arg2_not_sc {t1 t2} {pa : PArg Reg64 RegMm CondCode t1}
    {pb : PArg Reg64 RegMm CondCode t2}
    (h : ∀ r ∈ @tupArgGprs Reg64 RegMm CondCode [t1, t2] (pa, pb, ()), r ∉ x64Scratch) :
    ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch := fun r hr => h r (by
  cases pa <;> cases pb <;> simp [PArg.gprs, tupArgGprs] at hr ⊢ <;> grind)

private theorem arg3_not_sc {t1 t2 t3} {pa : PArg Reg64 RegMm CondCode t1}
    {pb : PArg Reg64 RegMm CondCode t2} {pc : PArg Reg64 RegMm CondCode t3}
    (h : ∀ r ∈ @tupArgGprs Reg64 RegMm CondCode [t1, t2, t3] (pa, pb, pc, ()), r ∉ x64Scratch) :
    ∀ r ∈ pa.gprs ++ pb.gprs ++ pc.gprs, r ∉ x64Scratch := fun r hr => h r (by
  cases pa <;> cases pb <;> cases pc <;> simp [PArg.gprs, tupArgGprs] at hr ⊢ <;> grind)

private theorem trel1 {R : ∀ t, PArg Reg64 RegMm CondCode t → Val t → Prop} {t}
    {pa : PArg Reg64 RegMm CondCode t} {va : Val t}
    (h : TRel R (as := [t]) (pa, ()) (va, ())) : R t pa va := by
  cases h with | cons a _ => exact a

private theorem trel2 {R : ∀ t, PArg Reg64 RegMm CondCode t → Val t → Prop} {t1 t2}
    {pa : PArg Reg64 RegMm CondCode t1} {pb : PArg Reg64 RegMm CondCode t2}
    {va : Val t1} {vb : Val t2}
    (h : TRel R (as := [t1, t2]) (pa, pb, ()) (va, vb, ())) : R t1 pa va ∧ R t2 pb vb := by
  cases h with | cons a h1 => cases h1 with | cons b _ => exact ⟨a, b⟩

private theorem trel3 {R : ∀ t, PArg Reg64 RegMm CondCode t → Val t → Prop} {t1 t2 t3}
    {pa : PArg Reg64 RegMm CondCode t1} {pb : PArg Reg64 RegMm CondCode t2}
    {pc : PArg Reg64 RegMm CondCode t3}
    {va : Val t1} {vb : Val t2} {vc : Val t3}
    (h : TRel R (as := [t1, t2, t3]) (pa, pb, pc, ()) (va, vb, vc, ())) :
    R t1 pa va ∧ R t2 pb vb ∧ R t3 pc vc := by
  cases h with
  | cons a h1 =>
    cases h1 with
    | cons b h2 =>
      cases h2 with
      | cons c _ => exact ⟨a, b, c⟩

theorem x64Gpr_op_spec {h : x64Mach.Host} {k : Nat} {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask} {vs : Tup Val sig}
    {P : Tup Val rs → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc0 : x64Gpr.op code pas dsts vh = some (c, clob))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ x64Scratch) (hdst : ∀ r ∈ tupDstGprs dsts, r ∉ x64Scratch)
    (hvs : TRel (x64Mach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    x64Mach.FallsTo x64Gpr.condReads h k c (tupDstGprs dsts ++ x64Scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64Op] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  cases code
  all_goals first | exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) hc | skip
  case copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    · dsimp only [x64OpIns] at hc; exact opPostDst1_fallsTo hwp fun {_} _ => opCopyBool_spec hc ha
    · (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
      dsimp only [x64OpIns] at hc
      exact withWidth_elim hc fun w hn hw => by
        subst hn; exact opPost1_fallsTo hwp fun {_} _ => opCopyBits_spec w hw ha
  case add t | sub t | mul t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      exact opPost1_fallsTo hwp fun {_} _ =>
        opBin_spec w _ hw (hdst rd (by simp [tupDstGprs])) (arg2_not_sc hargs) ha hb
  case and t | or t | xor t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    · dsimp only [x64OpIns] at hc; dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      refine opPostDst1_fallsTo hwp fun {_} _ =>
        opBoolBin_spec _ _ (by first | exact Bool.and_comm | exact Bool.or_comm | exact Bool.xor_comm)
          (fun dst src s0 _ p0 n0 j0 P0 hk => ?_) hc
          (fun r hr => hdst r (by simpa [tupDstGprs] using hr)) (arg2_not_sc hargs) ha hb
      first
      | exact fallsTo_and8 s0 dst src p0 n0 j0 P0 fun _ ⟨st, hzf, hs⟩ =>
          hk _ ⟨_, st, fun a b h1 h2 =>
            ⟨by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le],
             by cases a <;> cases b <;> simp_all⟩, hs⟩
      | exact fallsTo_or8 s0 dst src p0 n0 j0 P0 fun _ ⟨st, hzf, hs⟩ =>
          hk _ ⟨_, st, fun a b h1 h2 =>
            ⟨by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le],
             by cases a <;> cases b <;> simp_all⟩, hs⟩
      | exact fallsTo_xor8 s0 dst src p0 n0 j0 P0 fun _ ⟨st, hzf, hs⟩ =>
          hk _ ⟨_, st, fun a b h1 h2 =>
            ⟨by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le],
             by cases a <;> cases b <;> simp_all⟩, hs⟩
    · (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
      dsimp only [x64OpIns] at hc
      rename_i rd; exact withWidth_elim hc fun w hn hw => by
        subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
        exact opPost1_fallsTo hwp fun {_} _ =>
          opBin_spec w _ hw (hdst rd (by simp [tupDstGprs])) (arg2_not_sc hargs) ha hb
  case neg t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift1] at hwp
      exact opPost1_fallsTo hwp fun {_} _ => opNeg_spec w hw ha
  case not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    · dsimp only [x64OpIns] at hc; exact opPostDst1_fallsTo hwp fun {_} _ => opBoolNot_spec hc ha
    · (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
      dsimp only [x64OpIns] at hc
      exact withWidth_elim hc fun w hn hw => by
        subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift1] at hwp
        exact opPost1_fallsTo hwp fun {_} _ => opNot_spec w hw ha
  case shl t | lshr t | ashr t | rotl t | rotr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      exact opPost1_fallsTo hwp fun {_} _ =>
        opShift_spec w _ hw (hdst rd (by simp [tupDstGprs])) (arg2_not_sc hargs) ha hb
  case fshl n | fshr n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases vs with ⟨va, vb, vc, ⟨⟩⟩
    obtain ⟨ha, hb, hc'⟩ := trel3 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWideWidth_elim hc fun w hn hw => by
      subst hn; cases w <;> (first
        | (unfold withWideWidth at hc; contradiction)
        | exact opPost1_fallsTo hwp fun {_} _ =>
            opFunnel_spec _ (by first | exact .inl rfl | exact .inr rfl) _ hw
              (hdst rd (by simp [tupDstGprs])) (arg3_not_sc hargs) ha hb hc')
  case bswap t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i n _; have hok := (@opBswap_spec _ (fun _ _ => True) n pa _ ci clob va s hc ha).1
    dsimp only [OpCode.wp, lift1] at hwp
    simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwp
    exact opPost1_fallsTo hwp fun {_} _ => (@opBswap_spec _ _ n pa _ ci clob va s hc ha).2
  case clz n | cls n | ctz n | popcnt n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp] at hwp
      exact opPost1_fallsTo hwp fun {_} _ =>
        opBitcnt_spec w _ hw (hdst rd (by simp [tupDstGprs]))
          (fun r hr => hargs r (by
            cases pa with | gpr _ => simpa [tupArgGprs] using hr | _ => simp at hr)) ha
  case cmp co t m hm =>
    (cases t <;> try exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) hc); subst hm
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    dsimp only [x64OpIns] at hc; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, Ty.hasFloat, liftCmp] at hwp
      exact opPostDst1_fallsTo hwp fun {_} _ => opCmp_spec w co hw (arg2_not_sc hargs) ha hb
  case select t =>
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases vs with ⟨vc, va, vb, ⟨⟩⟩
    obtain ⟨hc', ha, hb⟩ := trel3 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; exact opPost1_fallsTo hwp fun {_} _ =>
        opSelect_spec w hw (hdst rd (by simp [tupDstGprs])) (arg3_not_sc hargs) hc' ha hb
  case zext m n | sext m n | trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    exact opPost1_fallsTo hwp.2 fun {_} _ => by
      first | exact (opZext_spec m n hc ha).2
            | exact (opSext_spec m n hc ha).2
            | exact (opTrunc_spec m n hc ha).2
  case ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc; split at hc <;> try contradiction
    next hnw =>
      rcases mem_x64BitWidths hnw with rfl | rfl | rfl | rfl <;> (first
        | exact opPost1_fallsTo hwp fun {_} _ => opOfBool_spec .W8 hc ha
        | exact opPost1_fallsTo hwp fun {_} _ => opOfBool_spec .W16 hc ha
        | exact opPost1_fallsTo hwp fun {_} _ => opOfBool_spec .W32 hc ha
        | exact opPost1_fallsTo hwp fun {_} _ => opOfBool_spec .W64 hc ha)
  case addc n | subb n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases vs with ⟨va, vb, vc, ⟨⟩⟩
    obtain ⟨ha, hb, hc'⟩ := trel3 hvs
    rcases dsts with ⟨d0, d1, ⟨⟩⟩; dsimp only [x64OpIns] at hc
    exact withWideWidth_elim hc fun w hn hw => by
      subst hn; cases w <;> (first
        | (unfold withWideWidth at hc; contradiction)
        | exact opPost2_fallsTo hwp fun {_} _ =>
            opAddc_spec _ (by first | exact .inl rfl | exact .inr rfl) hw
              (arg3_not_sc hargs) hdst ha hb hc'
        | exact opPost2_fallsTo hwp fun {_} _ =>
            opSubb_spec _ (by first | exact .inl rfl | exact .inr rfl) hw
              (arg3_not_sc hargs) hdst ha hb hc')
  case umulw n | smulw n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs
    rcases dsts with ⟨d0, d1, ⟨⟩⟩; dsimp only [x64OpIns] at hc
    exact withWideWidth_elim hc fun w hn hw => by
      subst hn; cases w <;> (first
        | (unfold withWideWidth at hc; contradiction)
        | exact opPost2_fallsTo hwp fun {_} _ =>
            opMulw_spec _ (by first | exact .inl rfl | exact .inr rfl) _ hw
              (arg2_not_sc hargs) hdst ha hb)
  case udiv n | sdiv n | urem n | srem n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp] at hwp
      exact opPost1_fallsTo hwp.2 fun {_} _ =>
        opDiv_spec w _ _ hw (hdst rd (by simp [tupDstGprs])) (arg2_not_sc hargs) ha hb hwp.1
  case bitcast t1 t2 hb =>
    cases t1 <;> cases t2 <;> try exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) hc
    rename_i m n; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc; split at hc <;> try contradiction
    rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs; have hmn : m = n := hb; subst hmn
    exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, toBits, ofBits, BitVec.cast] at hwp
      exact opPost1_fallsTo hwp fun {_} _ => opCopyBits_spec w hw ha

theorem x64Gpr_op_zero32 {h : x64Mach.Host} {k : Nat} {sig : List Ty}
    {code : OpCode sig [.bits 32]} {pas : Tup (PArg Reg64 RegMm CondCode) sig}
    {dsts : Tup (PDst Reg64 RegMm CondCode) [.bits 32]} {rd : Reg64} {vh : VariantHint}
    {c : List Directive} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val [.bits 32] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hz : x64Gpr.zeroUpper32Op code pas dsts = true)
    (hc0 : x64Gpr.op code pas dsts vh = some (c, clob)) (hd : dsts = (.gpr rd, ()))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ x64Scratch) (hrd : rd ∉ x64Scratch)
    (hvs : TRel (x64Mach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    x64Mach.FallsTo x64Gpr.condReads h k c (rd :: x64Scratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.regs.get64 rd = rv.setWidth 64) ∧
        s'.dmem = s.dmem) post := by
  subst hd
  dsimp only [x64Gpr, x64Op] at hc0 hz
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  cases code <;>
    (try exact absurd hz Bool.false_ne_true)
  case copy =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
    dsimp only [x64OpIns, withWidth] at hc
    have hne : pa ≠ .gpr rd := by
      intro h; subst h; cases rd <;> exact Bool.false_ne_true hz
    exact opPostZ_fallsTo hwp fun {_} _ => opCopyBits_zero32_spec hne hc ha
  case add | sub | mul | and | or | xor =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs; dsimp only [x64OpIns, withWidth] at hc
    dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
    exact opPostZ_fallsTo hwp fun {_} _ =>
      opBin_zero32_spec _ hc hrd (arg2_not_sc hargs) ha hb
  case neg | not =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    have ha := trel1 hvs; dsimp only [x64OpIns, withWidth] at hc
    dsimp only [OpCode.wp, Ty.hasFloat, lift1] at hwp
    exact opPostZ_fallsTo hwp fun {_} _ => by
      first | exact opNeg_zero32_spec hc ha | exact opNot_zero32_spec hc ha
  case shl | lshr | ashr | rotl | rotr =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs; dsimp only [x64OpIns, withWidth] at hc
    dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
    exact opPostZ_fallsTo hwp fun {_} _ =>
      opShift_zero32_spec _ (pa := pa) (pb := pb) (by
        cases pb with
        | gpr _ => exact rfl
        | vec _ => exact Bool.false_ne_true hz
        | imm cb => change (cb.toNat % 32 != 0) = true at hz; exact bne_iff_ne.mp hz)
        hc hrd (arg2_not_sc hargs) ha hb
  case bswap =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    have ha := trel1 hvs; dsimp only [x64OpIns] at hc
    have hok := (@opBswap_spec _ (fun _ _ => True) 32 pa _ ci clob va s hc ha).1
    dsimp only [OpCode.wp, lift1] at hwp
    simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwp
    exact opPostZ_fallsTo hwp fun {_} _ => opBswap_zero32_spec hc ha
  case zext m =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    have ha := trel1 hvs; dsimp only [x64OpIns] at hc
    exact opPostZ_fallsTo hwp.2 fun {_} _ => opZext_zero32_spec m hc ha
  case sext m =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    have ha := trel1 hvs; dsimp only [x64OpIns] at hc
    exact opPostZ_fallsTo hwp.2 fun {_} _ => opSext_zero32_spec m hc ha
  case ofBool =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    have ha := trel1 hvs; dsimp only [x64OpIns] at hc
    exact opPostZ_fallsTo hwp fun {_} _ => opOfBool_zero32_spec hc ha
  case clz | cls | ctz | popcnt =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    have ha := trel1 hvs; dsimp only [x64OpIns, withWidth] at hc
    dsimp only [OpCode.wp] at hwp
    exact opPostZ_fallsTo hwp fun {_} _ =>
      opBitcnt_zero32_spec _ hc (fun r hr => hargs r (by
        cases pa with | gpr _ => simpa [tupArgGprs] using hr | _ => simp at hr)) ha
  case udiv | sdiv | urem | srem =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨ha, hb⟩ := trel2 hvs; dsimp only [x64OpIns, withWidth] at hc
    dsimp only [OpCode.wp] at hwp
    exact opPostZ_fallsTo hwp.2 fun {_} _ =>
      opDiv_zero32_spec _ _ hc hrd (arg2_not_sc hargs) ha hb hwp.1
  case trunc m =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    change (m == 64 && _) = true at hz
    rcases Bool.and_eq_true_iff.mp hz with ⟨hm64, hz'⟩
    have hm64' : m = 64 := beq_iff_eq.mp hm64
    subst hm64'
    have ha := trel1 hvs; dsimp only [x64OpIns] at hc
    have hne : pa ≠ .gpr rd := by
      intro h; subst h; cases rd <;> exact Bool.false_ne_true hz'
    exact opPostZ_fallsTo hwp.2 fun {_} _ => opTrunc_zero32_spec hne hc ha
  case fshl | fshr =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases vs with ⟨va, vb, vc, ⟨⟩⟩
    obtain ⟨ha, hb, hc'⟩ := trel3 hvs; dsimp only [x64OpIns, withWideWidth] at hc
    exact opPostZ_fallsTo hwp fun {_} _ =>
      opFunnel_zero32_spec _ (pa := pa) (pb := pb) (pc := pc) (by
        cases pc with
        | gpr _ => trivial
        | vec _ => exact Bool.false_ne_true hz
        | imm cb =>
          change (cb.toNat % 32 != 0 || _) = true at hz
          rcases Bool.or_eq_true_iff.mp hz with hnz | hne
          · exact Or.inl (bne_iff_ne.mp hnz)
          · exact Or.inr fun h => by
              first
              | (rw [h] at hne; cases rd <;> exact Bool.false_ne_true hne)
              | (simp only [↓reduceIte, Bool.false_eq_true] at h; rw [h] at hne;
                 cases rd <;> exact Bool.false_ne_true hne))
        hc hrd (arg3_not_sc hargs) ha hb hc'
  case select =>
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases vs with ⟨vc, va, vb, ⟨⟩⟩
    obtain ⟨hc', ha, hb⟩ := trel3 hvs; dsimp only [x64OpIns, withWidth] at hc
    cases pc with
    | vec _ => exact absurd hz Bool.false_ne_true
    | imm b0 =>
      exact opPostZ_fallsTo hwp fun {_} _ =>
        opSelect_zero32_spec (by
          intro h; cases b0
          · simp only [Bool.false_eq_true, ↓reduceIte] at h
            rw [h] at hz; cases rd <;> exact Bool.false_ne_true hz
          · simp only [↓reduceIte] at h
            rw [h] at hz; cases rd <;> exact Bool.false_ne_true hz)
          hc hrd (arg3_not_sc hargs) hc' ha hb
    | flag _ | gpr _ =>
      exact opPostZ_fallsTo hwp fun {_} _ =>
        opSelect_zero32_spec (by
          intro ra ⟨h1, h2, h3⟩; subst h1 h2 h3
          cases ra <;> exact Bool.false_ne_true hz)
          hc hrd (arg3_not_sc hargs) hc' ha hb
  case bitcast t1 hb =>
    cases t1 with
    | bits m =>
      have hm32 : m = 32 := hb
      subst hm32
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
      dsimp only [x64OpIns, x64BitWidths, List.contains_eq_mem, List.mem_cons,
        List.not_mem_nil, or_false, decide_true, ↓reduceIte, withWidth] at hc
      dsimp only [OpCode.wp, toBits, ofBits, BitVec.cast] at hwp
      have hne : pa ≠ .gpr rd := by
        intro h; subst h; cases rd <;> exact Bool.false_ne_true hz
      exact opPostZ_fallsTo hwp fun {_} _ => opCopyBits_zero32_spec hne hc ha
    | _ => exact absurd hz Bool.false_ne_true

private theorem aluMem_kind_eval {w : Width} {k : AluBinKind}
    {code : OpCode [.bits w.bits, .bits w.bits] [.bits w.bits]} {memRhs : Bool}
    {va vb : BitVec w.bits} {P : Tup Val [.bits w.bits] → Prop}
    (hk : x64AluMemKind? code = some k) (hcm : (memRhs || k.isComm) = true)
    (hwp : code.wp (if memRhs then (vb, va, ()) else (va, vb, ())) P) :
    P (k.eval vb va, ()) := by
  have hk_comm : memRhs = false → k.isComm = true := by
    intro hm; subst hm; simpa using hcm
  cases code <;> simp only [x64AluMemKind?, reduceCtorEq] at hk
  all_goals
    cases hk
    dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
    cases hm : memRhs <;> simp only [hm, Bool.false_eq_true, ↓reduceIte] at hwp
    · first
      | (rw [AluBinKind.comm_eq (hk_comm hm)]; exact hwp)
      | exact absurd (hk_comm hm) (by decide)
    · exact hwp

local macro "close_aluMem_z" : tactic => `(tactic|
  (refine Or.inl ⟨trivial, _, _, ?_, ?_, rfl⟩
   · first | exact replaceLow_setWidth_le (by decide) _ _
           | (rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide),
               BitVec.setWidth_eq]; done)
           | exact BitVec.setWidth_eq _
   · exact fun h => by (cases h <;> exact BitVec.zeroExtend_eq_setWidth)))

private theorem wp_aluBinMem_z [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (k : AluBinKind) (hk : ¬ (k = .mul ∧ w = .W8)) (s : MachineData) (rd : Reg64)
    (addr : AddrExpr) (addrVal : BitVec 64) (va : BitVec w.bits)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    _root_.Program.wp [aluBinIns w k rd (.regOrMem (.mem addr))] (fun s' =>
      ∃ rv status,
        rv.setWidth w.bits = k.eval ((s.regs.get64 rd).setWidth w.bits) va ∧
        (w = .W32 → rv = (k.eval ((s.regs.get64 rd).setWidth w.bits) va).setWidth 64) ∧
        s' = { s with regs := s.regs.set64 rd rv, status := status }) E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases k with
  | add =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp, MachineData.load,
      Effects.All_require_read_access, haddr, hi, Reg64s.set] <;>
      simp only [AluBinKind.eval, Width.bits] <;> rw [BitVec.add_comm] <;> close_aluMem_z
  | sub =>
    cases w <;> simp only [aluBinIns, regW, t_step_simp, MachineData.load,
      Effects.All_require_read_access, haddr, hi, Reg64s.set] <;>
      simp only [AluBinKind.eval, Width.bits] <;> close_aluMem_z
  | and | or | xor =>
    cases w with
    | W8 | W16 =>
      simp only [aluBinIns, regW, t_step_simp, MachineData.load,
        Effects.All_require_read_access, haddr, hi, Reg64s.set, Effects.All]
      intro _
      refine Or.inl ⟨trivial, _, _, replaceLow_setWidth_le (by decide) _ _,
        (fun h => by cases h), rfl⟩
    | W32 =>
      simp only [aluBinIns, regW, t_step_simp, MachineData.load,
        Effects.All_require_read_access, haddr, hi, Reg64s.set, Effects.All]
      intro _
      refine Or.inl ⟨trivial, _, _, ?_, (fun _ => BitVec.zeroExtend_eq_setWidth), rfl⟩
      dsimp only [AluBinKind.eval, Width.bits]
      rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide),
        BitVec.setWidth_eq]
    | W64 =>
      simp only [aluBinIns, regW, t_step_simp, MachineData.load,
        Effects.All_require_read_access, haddr, hi, Reg64s.set, Effects.All]
      intro _
      refine Or.inl ⟨trivial, _, _, BitVec.setWidth_eq _, (fun h => by cases h), rfl⟩
  | mul =>
    cases w with
    | W8 => exact absurd ⟨rfl, rfl⟩ hk
    | W16 | W32 | W64 =>
      simp only [aluBinIns, regW, t_step_simp, MachineData.load,
        Effects.All_require_read_access, haddr, hi, Reg64s.set, Effects.All]
      intro _ _ _ _; simp only [AluBinKind.eval, Width.bits]; close_aluMem_z

private theorem not_mem_of_contains_false {r : Reg64} :
    ∀ {xs : List Reg64}, xs.contains r = false → r ∉ xs
  | [], _ => List.not_mem_nil
  | y :: ys, h => fun hm => by
    rcases List.mem_cons.mp hm with rfl | hm'
    · simp only [List.contains, List.elem, (beq_reg64_iff r r).2 rfl] at h
      cases h
    · cases he : r == y <;> simp only [List.contains, List.elem, he] at h
      · exact not_mem_of_contains_false h hm'
      · cases h

private theorem x64AluMem_z {h : x64Mach.Host} {k n : Nat} (z32 : Bool) {memRhs : Bool}
    {code : OpCode [.bits n, .bits n] [.bits n]} {a : AddrArg Reg64}
    {pb : PArg Reg64 RegMm CondCode (.bits n)} {rd : Reg64} {c : List Directive}
    {clob : FlagMask} {va vb : BitVec n} {P : Tup Val [.bits n] → Prop} {s : MachineData}
    {post : MachineState → Prop}
    (hz : z32 = true → n = 32)
    (hc0 : x64Gpr.aluMem n code memRhs a pb rd = some (c, clob))
    (hregs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ x64Scratch) (hrd : rd ∉ x64Scratch)
    (hlv : loadVal (x64Mach.mem s) (.bits n) (a.eval (x64Mach.getGpr s)) = some va)
    (hpb : x64Mach.PArgHolds s (.bits n) pb vb)
    (hwp : code.wp (if memRhs then (vb, va, ()) else (va, vb, ())) P) :
    x64Mach.FallsTo x64Gpr.condReads h k c (rd :: x64Scratch) [] clob s
      (fun s' => (∃ rv : BitVec n, P (rv, ()) ∧
        GprHolds (s'.regs.get64 rd) (.bits n) rv ∧
        (z32 = true → s'.regs.get64 rd = rv.setWidth 64)) ∧ s'.dmem = s.dmem) post := by
  dsimp only [x64Gpr, x64AluMem] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  have hva : x64AddrValid a = true := by cases hv : x64AddrValid a <;> simp_all [x64AluMemIns]
  simp only [x64AluMemIns, hva, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
  cases hk? : x64AluMemKind? code with
  | none => rw [hk?] at hc; cases hc
  | some kd =>
    rw [hk?] at hc; dsimp only at hc
    split at hc
    · cases hc
    rename_i hbad
    have hcm : (memRhs || kd.isComm) = true := by
      cases hb : (memRhs || kd.isComm)
      · exact False.elim (hbad (by simp [hb]))
      · rfl
    have hmul8 : ¬ (kd = .mul ∧ n = 8) := fun ⟨h1, h2⟩ => by
      subst h1 h2; exact hbad (by simp)
    refine withWidth_elim hc fun w hn hw => ?_
    subst hn
    have hk_ne : ¬ (kd = .mul ∧ w = .W8) := fun ⟨h1, h2⟩ => hmul8 ⟨h1, by subst h2; rfl⟩
    have ha : ∀ r ∈ a.regs, r ∉ x64Scratch := fun r hr => hregs r (List.mem_append_left _ hr)
    have hres_p : P (kd.eval vb va, ()) := aluMem_kind_eval hk? hcm hwp
    have runAfterPre (preMov : List Directive) (vb' : BitVec w.bits)
        (hpre : ∀ [Host] (E : Int64 → MachineData → Prop),
          _root_.Program.wp preMov (fun s1 =>
            (s1.regs.get64 rd).setWidth w.bits = vb' ∧
            (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
            (∀ r ∈ a.regs, s1.regs.get64 r = s.regs.get64 r) ∧
            s1.dmem = s.dmem ∧ s1.zmms = s.zmms) E s)
        (hc_eq : emitClean ci =
          preMov ++ (addrToExpr a).1 ++ [aluBinIns w kd rd (.regOrMem (.mem (addrToExpr a).2.1))])
        (hcl_eq : clob = maskAll) (hvb' : vb' = vb) :
        x64Mach.FallsTo x64Gpr.condReads h k (emitClean ci) (rd :: x64Scratch) [] clob s
          (fun s' => (∃ rv : BitVec w.bits, P (rv, ()) ∧
            GprHolds (s'.regs.get64 rd) (.bits w.bits) rv ∧
            (z32 = true → s'.regs.get64 rd = rv.setWidth 64)) ∧ s'.dmem = s.dmem) post := by
      subst hvb' hcl_eq; rw [hc_eq]
      have hrd10 := (ne_of_not_mem_x64Scratch hrd).1
      refine x64_fallsTo_of_wp fun {_} _ => ?_
      rw [List.append_assoc]
      refine Program.wp.append (hpre _) ?_
      rintro s1 ⟨hrd1, hr1, hra1, hm1, hz1⟩
      refine Program.wp.append (wp_addrToExpr s1 s a ha hra1) ?_
      rintro s2 ⟨_, hr2, hm2, hz2, haddr2, _⟩
      refine Program.wp.mono (wp_aluBinMem_z w kd hk_ne s2 rd _ (a.eval s.regs.get64) va
        (fun {_} p => haddr2 s2.regs (fun _ _ => rfl) p) (hm2 ▸ hm1 ▸ hlv)) ?_
      rintro s3 ⟨rv, st, hrv, hrvz, rfl⟩
      have hrd2 : (s2.regs.get64 rd).setWidth w.bits = vb' := by rw [hr2 rd hrd10, hrd1]
      rw [hrd2] at hrv hrvz
      refine ⟨⟨⟨kd.eval vb' va, hres_p, (GprHolds.bits_iff w _ _).2 (by
          rw [Reg64s.get64_set64_same, hrv]),
          fun hz1' => by
            have hbits := hz hz1'
            have hw32 : w = .W32 := by cases w <;> simp [Width.bits] at hbits; rfl
            rw [Reg64s.get64_set64_same, hrvz hw32]⟩, hm2.trans hm1⟩,
        x64_frame_of_eq ?_ (hz2.trans hz1) (updFlags_maskAll _ _)⟩
      intro r hr; rw [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        hr2 r (ne_of_not_mem_x64Scratch hr.2).1, hr1 r hr.1]
    cases pb with
    | vec _ => simp at hw
    | gpr rs =>
      dsimp only at hw
      by_cases hrr : rs == rd
      · simp only [hrr, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hw
        rcases hw with ⟨rfl, rfl⟩
        refine runAfterPre [] vb (fun _ => _root_.Program.wp_nil ⟨?_, fun _ _ => rfl,
          fun _ _ => rfl, rfl, rfl⟩)
          (by simp [emitClean_append, emitClean_cons, emitClean_nil, addrToExpr, aluBinIns]) rfl rfl
        have hrs := (beq_reg64_iff rs rd).1 hrr; subst hrs; exact hpb.2
      · simp only [hrr, Bool.false_eq_true, ↓reduceIte] at hw
        by_cases hcont : a.regs.contains rd
        · simp [hcont] at hw
        · simp only [hcont, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hw
          rcases hw with ⟨rfl, rfl⟩
          have hno : ∀ r ∈ a.regs, r ≠ rd := fun r hr h' => by
            subst h'
            exact not_mem_of_contains_false (Bool.eq_false_iff.mpr hcont) hr
          refine runAfterPre [movW w rd rs] vb (fun {_} _ => ?_)
            (by simp [emitClean_append, emitClean_cons, emitClean_nil, addrToExpr, movW,
              aluBinIns])
            rfl rfl
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w s rd rs)) ?_
          rintro s1 rfl
          refine ⟨?_, fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            fun r hr => Reg64s.get64_set64_of_ne _ rd r _ (hno r hr).symm, rfl, rfl⟩
          rw [Reg64s.get64_set64_same, setWidth_64_setWidth, hpb.2]
    | imm cb =>
      dsimp only at hw
      rcases hpb with rfl
      by_cases hcont : a.regs.contains rd
      · simp [hcont] at hw
      · simp only [hcont, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at hw
        rcases hw with ⟨rfl, rfl⟩
        have hno : ∀ r ∈ a.regs, r ≠ rd := fun r hr h' => by
          subst h'
          exact not_mem_of_contains_false (Bool.eq_false_iff.mpr hcont) hr
        refine runAfterPre [moviD rd (cb.setWidth 64)] cb (fun {_} _ => ?_)
          (by simp [emitClean_append, emitClean_cons, emitClean_nil, addrToExpr, moviD,
            aluBinIns])
          rfl rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (cb.setWidth 64))) ?_
        rintro s1 rfl
        refine ⟨?_, fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
          fun r hr => Reg64s.get64_set64_of_ne _ rd r _ (hno r hr).symm, rfl, rfl⟩
        rw [Reg64s.get64_set64_same, setWidth_64_setWidth]

theorem x64Gpr_aluMem_spec {h : x64Mach.Host} {k n : Nat} {memRhs : Bool}
    {code : OpCode [.bits n, .bits n] [.bits n]} {a : AddrArg Reg64}
    {pb : PArg Reg64 RegMm CondCode (.bits n)} {rd : Reg64} {c : List Directive}
    {clob : FlagMask} {va vb : BitVec n} {P : Tup Val [.bits n] → Prop} {s : MachineData}
    {post : MachineState → Prop}
    (hc0 : x64Gpr.aluMem n code memRhs a pb rd = some (c, clob))
    (hregs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ x64Scratch) (hrd : rd ∉ x64Scratch)
    (hlv : loadVal (x64Mach.mem s) (.bits n) (a.eval (x64Mach.getGpr s)) = some va)
    (hpb : x64Mach.PArgHolds s (.bits n) pb vb)
    (hwp : code.wp (if memRhs then (vb, va, ()) else (va, vb, ())) P) :
    x64Mach.FallsTo x64Gpr.condReads h k c (rd :: x64Scratch) [] clob s
      (fun s' => (∃ rv : BitVec n, P (rv, ()) ∧
        GprHolds (x64Mach.getGpr s' rd) (.bits n) rv) ∧ x64Mach.mem s' = x64Mach.mem s) post :=
  fun hinf kont =>
    x64AluMem_z false (fun h => by cases h) hc0 hregs hrd hlv hpb hwp hinf
      fun s' ⟨⟨rv, hp, hg, _⟩, hm⟩ hfr => kont s' ⟨⟨rv, hp, hg⟩, hm⟩ hfr

theorem x64Gpr_aluMem_zero32 (_ : x64Gpr.zeroUpper32AluMem = true)
    {h : x64Mach.Host} {k : Nat} {memRhs : Bool}
    {code : OpCode [.bits 32, .bits 32] [.bits 32]} {a : AddrArg Reg64}
    {pb : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64} {c : List Directive}
    {clob : FlagMask} {va vb : BitVec 32} {P : Tup Val [.bits 32] → Prop} {s : MachineData}
    {post : MachineState → Prop}
    (hc0 : x64Gpr.aluMem 32 code memRhs a pb rd = some (c, clob))
    (hregs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ x64Scratch) (hrd : rd ∉ x64Scratch)
    (hlv : loadVal (x64Mach.mem s) (.bits 32) (a.eval (x64Mach.getGpr s)) = some va)
    (hpb : x64Mach.PArgHolds s (.bits 32) pb vb)
    (hwp : code.wp (if memRhs then (vb, va, ()) else (va, vb, ())) P) :
    x64Mach.FallsTo x64Gpr.condReads h k c (rd :: x64Scratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧
        x64Mach.getGpr s' rd = rv.setWidth 64) ∧ x64Mach.mem s' = x64Mach.mem s) post :=
  fun hinf kont =>
    x64AluMem_z true (fun _ => rfl) hc0 hregs hrd hlv hpb hwp hinf
      fun s' ⟨⟨rv, hp, _, hz⟩, hm⟩ hfr => kont s' ⟨⟨rv, hp, hz rfl⟩, hm⟩ hfr

theorem x64Gpr_jnzMem_spec {h : x64Mach.Host} {k j : Nat} {a : AddrArg Reg64} {inv : Bool}
    {l : Sym} {c : List Directive} {clob : FlagMask} {v8 : BitVec 8} {b : Bool}
    {s : MachineData} {post : MachineState → Prop}
    (hc0 : x64Gpr.jnzMem a inv l = some (c, clob))
    (hinf : c.IsInfixAt (x64Mach.prog h) k) (hj : x64Mach.labelAddr h l = x64Mach.addrOf h j)
    (ha : ∀ r ∈ a.regs, r ∉ x64Scratch)
    (hlv : loadVal (x64Mach.mem s) (.bits 8) (a.eval (x64Mach.getGpr s)) = some v8)
    (hv8 : v8 = BitVec.ofNat 8 b.toNat)
    (hk : ∀ s', x64Mach.Frame x64Gpr.condReads s s' x64Scratch [] clob →
      x64Mach.mem s' = x64Mach.mem s →
      ((if inv then !b else b) = true → x64Mach.Run h j s' post) ∧
      ((if inv then !b else b) = false → x64Mach.Run h (k + c.length) s' post)) :
    x64Mach.Run h k s post := by
  letI := h
  dsimp only [x64Gpr, x64JnzMem] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  have hva : x64AddrValid a = true := by cases hv : x64AddrValid a <;> simp_all [x64JnzMemIns]
  simp only [x64JnzMemIns, hva, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq, Prod.mk.injEq] at hc
  rcases hc with ⟨rfl, rfl⟩
  let cc : CondCode := if inv then .z else .nz
  let preCmp := (addrToExpr a).1 ++ [ins8 (.cmp (.mem (addrToExpr a).2.1) (immBitsOp .W8 0#8))]
  have hc_eq : emitClean ((addrToExprIns a).1 ++
      [x64InsI .W8 (.cmp (.mem (addrToExprIns a).2.1) (immBitsOp .W8 0#8)),
       x64InsI .W64 (.jcc cc l)]) = preCmp ++ [ins (.jcc cc l)] := by
    simp [preCmp, addrToExpr, emitClean_append, emitClean_cons, emitClean_nil]
  rw [hc_eq] at hinf hk
  obtain ⟨hinfPre, hinfJcc⟩ := List.IsInfixAt.append hinf
  have hwPre : _root_.Program.wp preCmp (fun s2 =>
      (∀ r, r ∉ x64Scratch → s2.regs.get64 r = s.regs.get64 r) ∧
      s2.dmem = s.dmem ∧ s2.zmms = s.zmms ∧ s2.status = subFlags v8 0#8)
      (fun _ _ => False) s := by
    refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
    rintro s1 ⟨_, hr1, hm1, hz1, haddr1, _⟩
    refine Program.wp.mono (wp_cmp_mem_imm .W8 s1 _ (a.eval s.regs.get64) v8 0#8
      (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
    rintro s2 rfl
    exact ⟨fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1, hm1, hz1, rfl⟩
  refine Program.wp.eventually hwPre hinfPre ?_ (fun _ _ hf => hf.elim)
  rintro s2 ⟨hr2, hm2, hz2, hst2⟩
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hinfJcc) ?_
  simp only [t_step_simp]
  have hfr : x64Mach.Frame x64Gpr.condReads s s2 x64Scratch [] maskAll :=
    x64_frame_of_eq hr2 hz2 (updFlags_maskAll s s2)
  have hrun := hk s2 hfr hm2
  have hlab : Labels.label l = Host.addrOf j := hj
  have hlen : k + (preCmp ++ [ins (.jcc cc l)]).length = k + preCmp.length + 1 := by
    simp; omega
  have hcond : cc.interp s2.status = if inv then !b else b := by
    rw [hst2, hv8]
    cases inv <;> cases b <;> rfl
  cases hb' : (if inv then !b else b) with
  | true =>
    have hcc : cc.interp s2.status = true := hcond.trans hb'
    simp only [hcc, ↓reduceIte, Effects.All, hlab]
    exact hrun.1 hb'
  | false =>
    have hcc : cc.interp s2.status = false := hcond.trans hb'
    simp only [hcc, Bool.false_eq_true, ↓reduceIte, Effects.All, ← hlen]
    exact hrun.2 hb'

private def rmwKindEval {n : Nat} : RmwKind → BitVec n → BitVec n → BitVec n
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .and, a, b => a &&& b
  | .or,  a, b => a ||| b
  | .xor, a, b => a ^^^ b

private theorem rmwOp_close {P E : Prop} (hP : P) (s : MachineData) (st : StatusFlags)
    {dm1 dm2 : Mem 64} (hdm : dm1 = dm2) :
    (P ∧ ∃ status : StatusFlags,
      ({ s with status := st, dmem := dm1 } : MachineData) =
        { s with status := status, dmem := dm2 }) ∨ E :=
  Or.inl ⟨hP, st, by cases s; rw [hdm]⟩

private theorem rmwIncDec_close {P E : Prop} (hP : P) (s : MachineData)
    {st : StatusFlags} {dm1 dm2 : Mem 64}
    (hdm : dm1 = dm2) (hst : st.cf = s.status.cf) :
    (P ∧ ∃ status : StatusFlags, status.cf = s.status.cf ∧
      ({ s with status := st, dmem := dm1 } : MachineData) =
        { s with status := status, dmem := dm2 }) ∨ E :=
  Or.inl ⟨hP, st, hst, by cases s; rw [hdm]⟩

private theorem wp_rmwMem_op_reg [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (k : RmwKind) (s : MachineData) (addr : AddrExpr) (addrVal : BitVec 64)
    (va vb : BitVec w.bits) (ry : Reg64)
    (hry : (s.regs.get64 ry).setWidth w.bits = vb)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    let dm' := storeMem s.dmem (.bits w.bits) addrVal (rmwKindEval k va vb)
    _root_.Program.wp [.instr (rmwMemI w k addr (.reg (regW w ry)))] (fun s' =>
      ∃ status, s' = { s with status := status, dmem := dm' }) E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases k with
  | add =>
    cases w with
    | W8 | W16 | W32 =>
      simp only [rmwMemI, rmwKindEval, x64InsI, regW, t_step_simp,
        MachineData.load, MachineData.store, Effects.All_require_read_access,
        Effects.All_require_write_access, haddr, hi, storeMem_width_eq s.dmem _]
      refine rmwOp_close trivial s _ ?_
      simp only [hry, BitVec.add_comm]
    | W64 =>
      simp only [rmwMemI, rmwKindEval, x64InsI, regW, t_step_simp,
        MachineData.load, MachineData.store, Effects.All_require_read_access,
        Effects.All_require_write_access, haddr, hi, storeMem_width_eq s.dmem _]
      refine rmwOp_close trivial s _ ?_
      rw [← hry, BitVec.add_comm]; dsimp only [Width.bits]; rw [BitVec.setWidth_eq]
  | sub =>
    cases w with
    | W8 | W16 | W32 =>
      simp only [rmwMemI, rmwKindEval, x64InsI, regW, t_step_simp,
        MachineData.load, MachineData.store, Effects.All_require_read_access,
        Effects.All_require_write_access, haddr, hi, storeMem_width_eq s.dmem _]
      refine rmwOp_close trivial s _ ?_
      simp only [hry]
    | W64 =>
      simp only [rmwMemI, rmwKindEval, x64InsI, regW, t_step_simp,
        MachineData.load, MachineData.store, Effects.All_require_read_access,
        Effects.All_require_write_access, haddr, hi, storeMem_width_eq s.dmem _]
      refine rmwOp_close trivial s _ ?_
      rw [← hry]; dsimp only [Width.bits]; rw [BitVec.setWidth_eq]
  | and | or | xor =>
    cases w with
    | W8 | W16 | W32 =>
      simp only [rmwMemI, rmwKindEval, x64InsI, regW, t_step_simp,
        MachineData.load, MachineData.store, Effects.All_require_read_access,
        Effects.All_require_write_access, haddr, hi, storeMem_width_eq s.dmem _, Effects.All]
      intro _
      refine rmwOp_close trivial s _ ?_
      simp only [hry]
    | W64 =>
      simp only [rmwMemI, rmwKindEval, x64InsI, regW, t_step_simp,
        MachineData.load, MachineData.store, Effects.All_require_read_access,
        Effects.All_require_write_access, haddr, hi, storeMem_width_eq s.dmem _, Effects.All]
      intro _
      refine rmwOp_close trivial s _ ?_
      rw [← hry]; dsimp only [Width.bits]; rw [BitVec.setWidth_eq]

private theorem wp_rmwMem_op_imm [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (k : RmwKind) (s : MachineData) (addr : AddrExpr) (addrVal : BitVec 64)
    (va cy : BitVec w.bits)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    let dm' := storeMem s.dmem (.bits w.bits) addrVal (rmwKindEval k va cy)
    _root_.Program.wp [.instr (rmwMemI w k addr (immBitsOp w cy))] (fun s' =>
      ∃ status, s' = { s with status := status, dmem := dm' }) E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  have htr : (cy.signExtend 64).truncate w.bits = cy :=
    truncate_signExtend_64 (width_bits_le_64 w) cy
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases k with
  | add =>
    cases w <;> simp only [rmwMemI, rmwKindEval, x64InsI, immBitsOp, t_step_simp,
      Int64.toBitVec_ofBitVec, htr, MachineData.load, MachineData.store,
      Effects.All_require_read_access, Effects.All_require_write_access, haddr, hi,
      storeMem_width_eq s.dmem _] <;>
      (refine rmwOp_close trivial s _ ?_; simp only [BitVec.add_comm])
  | sub =>
    cases w <;> simp only [rmwMemI, rmwKindEval, x64InsI, immBitsOp, t_step_simp,
      Int64.toBitVec_ofBitVec, htr, MachineData.load, MachineData.store,
      Effects.All_require_read_access, Effects.All_require_write_access, haddr, hi,
      storeMem_width_eq s.dmem _] <;>
      (refine rmwOp_close trivial s _ ?_; rfl)
  | and | or | xor =>
    cases w <;> simp only [rmwMemI, rmwKindEval, x64InsI, immBitsOp, t_step_simp,
      Int64.toBitVec_ofBitVec, htr, MachineData.load, MachineData.store,
      Effects.All_require_read_access, Effects.All_require_write_access, haddr, hi,
      storeMem_width_eq s.dmem _, Effects.All] <;>
      intro _ <;> (refine rmwOp_close trivial s _ ?_; rfl)

private theorem wp_rmwMem_incDec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (isInc : Bool) (s : MachineData) (addr : AddrExpr) (addrVal : BitVec 64) (va : BitVec w.bits)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    let v' := if isInc then va + 1#w.bits else va - 1#w.bits
    let dm' := storeMem s.dmem (.bits w.bits) addrVal v'
    _root_.Program.wp [insW w (if isInc then .inc (.mem addr) else .dec (.mem addr))]
      (fun s' => ∃ status, status.cf = s.status.cf ∧
        s' = { s with status := status, dmem := dm' }) E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases isInc <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    cases w <;>
    simp only [insW, t_step_simp, MachineData.load, MachineData.store,
      Effects.All_require_read_access, Effects.All_require_write_access, haddr, hi,
      storeMem_width_eq s.dmem _] <;>
    (refine rmwIncDec_close trivial s ?_ ?_
     · rfl
     · simp only [StatusFlags.from_result])

private theorem addrToExpr_maskNone (a : AddrArg Reg64) : (addrToExpr a).2.2 = maskNone := by
  cases a <;> simp only [addrToExpr, addrToExprIns] <;>
    first | rfl | (split <;> first | rfl | (split <;> rfl))

theorem x64Gpr_rmwMem_spec {h : x64Mach.Host} {k n : Nat}
    {code : OpCode [.bits n, .bits n] [.bits n]} {a : AddrArg Reg64}
    {pb : PArg Reg64 RegMm CondCode (.bits n)} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec n} {P : Tup Val [.bits n] → Prop} {s : MachineData}
    {post : MachineState → Prop}
    (hc0 : x64Gpr.rmwMem n code a pb = some (c, clob))
    (hregs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ x64Scratch)
    (hlv : loadVal (x64Mach.mem s) (.bits n) (a.eval (x64Mach.getGpr s)) = some va)
    (_hok : storeOk (x64Mach.mem s) (.bits n) (a.eval (x64Mach.getGpr s)))
    (hpb : x64Mach.PArgHolds s (.bits n) pb vb) (hwp : code.wp (va, vb, ()) P) :
    x64Mach.FallsTo x64Gpr.condReads h k c x64Scratch [] clob s
      (fun s' => ∃ rv : BitVec n, P (rv, ()) ∧
        x64Mach.mem s' =
          storeMem (x64Mach.mem s) (.bits n) (a.eval (x64Mach.getGpr s)) rv) post := by
  dsimp only [x64Gpr, x64RmwMem] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  have hva : x64AddrValid a = true := by cases hv : x64AddrValid a <;> simp_all [x64RmwMemIns]
  simp only [x64RmwMemIns, hva, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
  cases hk? : x64RmwKind? code with
  | none => rw [hk?] at hc; cases hc
  | some kd =>
    rw [hk?] at hc; dsimp only at hc
    refine withWidth_elim hc fun w hn hw => ?_
    subst hn
    have hp_match : P (rmwKindEval kd va vb, ()) := by
      cases code <;> simp only [x64RmwKind?, reduceCtorEq] at hk? <;> cases hk? <;> exact hwp
    have ha : ∀ r ∈ a.regs, r ∉ x64Scratch := fun r hr => hregs r (List.mem_append_left _ hr)
    cases pb with
    | vec _ => dsimp only at hw; simp at hw
    | gpr ry =>
      dsimp only at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw; rcases hw with ⟨rfl, rfl⟩
      simp only [emitClean_append, emitClean_cons, emitClean_nil]
      have hry10 := (ne_of_not_mem_x64Scratch (hregs ry (by simp [PArg.gprs]))).1
      refine x64_fallsTo_of_wp fun {_} _ => ?_
      refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
      rintro s1 ⟨_, hr1, hm1, hz1, haddr1, _⟩
      have hry : (s1.regs.get64 ry).setWidth w.bits = vb := by rw [hr1 ry hry10, hpb.2]
      refine Program.wp.mono (wp_rmwMem_op_reg w kd s1 _ (a.eval s.regs.get64) va vb ry hry
        (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
      rintro s2 ⟨st, rfl⟩
      exact ⟨⟨_, hp_match, hm1 ▸ rfl⟩,
        x64_frame_of_eq (fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1) hz1
          (updFlags_maskAll _ _)⟩
    | imm cy =>
      dsimp only at hw
      rcases hpb with rfl
      have go_incDec (isInc : Bool)
          (hstep : rmwKindEval kd va cy = if isInc then va + 1#w.bits else va - 1#w.bits)
          (hw' : (some ((addrToExprIns a).1 ++
              [x64InsI w (if isInc then .inc (.mem (addrToExprIns a).2.1) else
                .dec (.mem (addrToExprIns a).2.1))], maskDecInc) :
            Option (List Instr × FlagMask)) = some (ci, clob)) :
          x64Mach.FallsTo x64Gpr.condReads h k (emitClean ci) x64Scratch [] clob s
            (fun s' => ∃ rv : BitVec w.bits, P (rv, ()) ∧
              x64Mach.mem s' =
                storeMem (x64Mach.mem s) (.bits w.bits) (a.eval (x64Mach.getGpr s)) rv) post := by
        simp only [Option.some.injEq, Prod.mk.injEq] at hw'; rcases hw' with ⟨rfl, rfl⟩
        simp only [emitClean_append, emitClean_cons, emitClean_nil]
        rw [hstep] at hp_match
        refine x64_fallsTo_of_wp fun {_} _ => ?_
        refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
        rintro s1 ⟨_, hr1, hm1, hz1, haddr1, hf1⟩
        refine Program.wp.mono (wp_rmwMem_incDec w isInc s1 _ (a.eval s.regs.get64) va
          (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
        rintro s2 ⟨st, hcf, rfl⟩
        let dm' := storeMem s1.dmem (.bits w.bits) (a.eval s.regs.get64)
          (if isInc then va + 1#w.bits else va - 1#w.bits)
        refine ⟨⟨_, hp_match, hm1 ▸ rfl⟩,
          x64_frame_of_eq (fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1) hz1 ?_⟩
        intro cc hdisj
        have h1 : x64Mach.evalCond { s1 with status := st, dmem := dm' } cc =
            x64Mach.evalCond s1 cc := updFlags_maskDecInc hcf cc hdisj
        have h0 : (x64CondReads cc).disjoint (addrToExpr a).2.2 = true := by
          rw [addrToExpr_maskNone]; exact FlagMask.disjoint_none _
        exact h1.trans (hf1 cc h0)
      split at hw
      · rename_i hinc
        have hstep : rmwKindEval kd va cy = va + 1#w.bits := by
          cases kd <;> simp only [beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true,
            reduceCtorEq, false_and, or_false, false_or, true_and] at hinc
          · simp [rmwKindEval, hinc]
          · simp [rmwKindEval, hinc, BitVec.sub_eq_add_neg, BitVec.neg_neg]
        exact go_incDec true (by simp [hstep]) hw
      · split at hw
        · rename_i hdec
          have hstep : rmwKindEval kd va cy = va - 1#w.bits := by
            cases kd <;> simp only [beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true,
              reduceCtorEq, false_and, or_false, false_or, true_and] at hdec
            · simp [rmwKindEval, hdec, BitVec.sub_eq_add_neg]
            · simp [rmwKindEval, hdec]
          exact go_incDec false (by simp [hstep]) hw
        · split at hw
          · simp only [Option.some.injEq, Prod.mk.injEq] at hw; rcases hw with ⟨rfl, rfl⟩
            simp only [emitClean_append, emitClean_cons, emitClean_nil]
            refine x64_fallsTo_of_wp fun {_} _ => ?_
            refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
            rintro s1 ⟨_, hr1, hm1, hz1, haddr1, _⟩
            refine Program.wp.mono (wp_rmwMem_op_imm w kd s1 _ (a.eval s.regs.get64) va cy
              (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
            rintro s2 ⟨st, rfl⟩
            exact ⟨⟨_, hp_match, hm1 ▸ rfl⟩,
              x64_frame_of_eq (fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1) hz1
                (updFlags_maskAll _ _)⟩
          · simp only [Option.some.injEq, Prod.mk.injEq] at hw; rcases hw with ⟨rfl, rfl⟩
            simp only [emitClean_append, emitClean_cons, emitClean_nil]
            refine x64_fallsTo_of_wp fun {_} _ => ?_
            refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
            rintro s1 ⟨_, hr1, hm1, hz1, haddr1, _⟩
            refine Program.wp.cons
              (Directive.FallsTo.wp (fallsTo_moviD s1 .r11 (cy.setWidth 64))) ?_
            rintro s2 rfl
            have hregs11 : ∀ r ∈ .r10 :: a.regs,
                (s1.regs.set64 .r11 (cy.setWidth 64)).get64 r = s1.regs.get64 r := by
              intro r hr; rcases List.mem_cons.mp hr with rfl | hr
              · exact Reg64s.get64_set64_of_ne _ .r11 .r10 _ (by decide)
              · exact Reg64s.get64_set64_of_ne _ .r11 r _
                  (ne_of_not_mem_x64Scratch (ha r hr)).2.symm
            have hcy11 : ((s1.regs.set64 .r11 (cy.setWidth 64)).get64 .r11).setWidth w.bits =
                cy := by
              rw [Reg64s.get64_set64_same, setWidth_64_setWidth]
            refine Program.wp.mono (wp_rmwMem_op_reg w kd _ _ (a.eval s.regs.get64) va cy
              .r11 hcy11 (fun {_} p => haddr1 _ hregs11 p) (hm1 ▸ hlv)) ?_
            rintro s3 ⟨st, rfl⟩
            refine ⟨⟨_, hp_match, hm1 ▸ rfl⟩,
              x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
            intro r hr
            have hne := ne_of_not_mem_x64Scratch hr
            rw [Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm, hr1 r hne.1]

private theorem x64LeaArith_z {w : Nat} (z32 : Bool) (hz32 : z32 = true → w = 32)
    {h : x64Mach.Host} {k : Nat} {base? : Option Reg64} {idx : Reg64} {sc : AddrScale}
    {disp : Int64} {rd : Reg64} {c : List Directive} {clob : FlagMask}
    {vb vi : BitVec w} {s : MachineData} {post : MachineState → Prop}
    (hc0 : x64Gpr.leaArith w base? idx sc disp rd = some (c, clob))
    (hvb : ∀ r, base? = some r → GprHolds (x64Mach.getGpr s r) (.bits w) vb)
    (hvi : GprHolds (x64Mach.getGpr s idx) (.bits w) vi) :
    let res : BitVec w :=
      (if base?.isSome then vb else 0#w) + (vi <<< sc.shift) + disp.toBitVec.setWidth w
    x64Mach.FallsTo x64Gpr.condReads h k c (rd :: x64Scratch) [] clob s
      (fun s' => GprHolds (x64Mach.getGpr s' rd) (.bits w) res ∧
        (z32 = true → x64Mach.getGpr s' rd = res.setWidth 64) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64LeaArith] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  dsimp only [x64LeaArithIns] at hc
  split at hc; · simp at hc
  have go : ∀ (wd : Width) (hw : wd = .W32 ∨ wd = .W64), wd.bits = w →
      ∀ (b? : Option Reg64),
      (∀ r, b? = some r → GprHolds (x64Mach.getGpr s r) (.bits w) vb) →
      (match b? with
      | some rb =>
        if idx != .rsp then
          some ([x64InsI wd (.lea (regW wd rd) (atSIB rb idx sc disp))], maskNone)
        else if sc == .s1 && rb != .rsp then
          some ([x64InsI wd (.lea (regW wd rd) (atSIB idx rb .s1 disp))], maskNone)
        else none
      | none =>
        if idx != .rsp then
          some ([x64InsI wd (.lea (regW wd rd) (atIdx idx sc disp))], maskNone)
        else none) = some (ci, clob) →
      x64Mach.FallsTo x64Gpr.condReads h k (emitClean ci) (rd :: x64Scratch) [] clob s
        (fun s' => GprHolds (x64Mach.getGpr s' rd) (.bits w)
            ((if b?.isSome then vb else 0#w) + (vi <<< sc.shift) +
              disp.toBitVec.setWidth w) ∧
          (z32 = true → x64Mach.getGpr s' rd =
            ((if b?.isSome then vb else 0#w) + (vi <<< sc.shift) +
              disp.toBitVec.setWidth w).setWidth 64) ∧
          x64Mach.mem s' = x64Mach.mem s) post := by
    rintro wd hw rfl b? hvb' hci
    have hvi' : (s.regs.get64 idx).setWidth wd.bits = vi := (GprHolds.bits_iff wd _ _).1 hvi
    cases b? with
    | some rb =>
      have hvbr : (s.regs.get64 rb).setWidth wd.bits = vb :=
        (GprHolds.bits_iff wd _ _).1 (hvb' rb rfl)
      dsimp only at hci
      split at hci
      · simp only [Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine x64_fallsTo_of_wp fun {_} _ => Program.wp.mono
          (Directive.FallsTo.wp (fallsTo_leaSIB_disp_z wd hw s rd rb idx sc disp)) ?_
        rintro s' ⟨rv, hrv, hrvz, rfl⟩
        have hres : rv.setWidth wd.bits =
            vb + (vi <<< sc.shift) + disp.toBitVec.setWidth wd.bits := by
          rw [hrv, hvbr, hvi']
        refine ⟨⟨(GprHolds.bits_iff wd _ _).2 (by simpa [Reg64s.get64_set64_same] using hres),
          fun hz => ?_, rfl⟩, ?_⟩
        · have hw32 : wd = .W32 := by
            have := hz32 hz; cases wd <;> simp [Width.bits] at this <;> rfl
          simpa [Reg64s.get64_set64_same, hvbr, hvi'] using hrvz hw32
        · refine x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_of_status_eq rfl _)
          simp only [List.mem_cons, not_or] at hr
          exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
      · split at hci
        · rename_i hswap
          have hsc : sc = .s1 := by simp only [Bool.and_eq_true, beq_iff_eq] at hswap; exact hswap.1
          subst hsc
          simp only [Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          refine x64_fallsTo_of_wp fun {_} _ => Program.wp.mono
            (Directive.FallsTo.wp (fallsTo_leaSIB_disp_z wd hw s rd idx rb .s1 disp)) ?_
          rintro s' ⟨rv, hrv, hrvz, rfl⟩
          have hcomm : (s.regs.get64 idx).setWidth wd.bits +
              ((s.regs.get64 rb).setWidth wd.bits <<< AddrScale.s1.shift) +
              disp.toBitVec.setWidth wd.bits =
              vb + (vi <<< AddrScale.s1.shift) + disp.toBitVec.setWidth wd.bits := by
            simp only [AddrScale.shift, BitVec.shiftLeft_zero, hvbr, hvi', BitVec.add_comm]
          refine ⟨⟨(GprHolds.bits_iff wd _ _).2
              (by simpa [Reg64s.get64_set64_same, hcomm] using hrv), fun hz => ?_, rfl⟩, ?_⟩
          · have hw32 : wd = .W32 := by
              have := hz32 hz; cases wd <;> simp [Width.bits] at this <;> rfl
            simpa [Reg64s.get64_set64_same, hcomm] using hrvz hw32
          · refine x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_of_status_eq rfl _)
            simp only [List.mem_cons, not_or] at hr
            exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
        · cases hci
    | none =>
      dsimp only at hci
      split at hci
      · simp only [Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine x64_fallsTo_of_wp fun {_} _ => Program.wp.mono
          (Directive.FallsTo.wp (fallsTo_leaIdx_z wd hw s rd idx sc disp)) ?_
        rintro s' ⟨rv, hrv, hrvz, rfl⟩
        have hres : rv.setWidth wd.bits =
            (vi <<< sc.shift) + disp.toBitVec.setWidth wd.bits := by
          rw [hrv, hvi']
        refine ⟨⟨(GprHolds.bits_iff wd _ _).2 (by simpa [Reg64s.get64_set64_same] using hres),
          fun hz => ?_, rfl⟩, ?_⟩
        · have hw32 : wd = .W32 := by
            have := hz32 hz; cases wd <;> simp [Width.bits] at this <;> rfl
          simpa [Reg64s.get64_set64_same, hvi'] using hrvz hw32
        · refine x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_of_status_eq rfl _)
          simp only [List.mem_cons, not_or] at hr
          exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
      · cases hci
  split at hc
  · exact go .W32 (Or.inl rfl) rfl base? hvb hc
  · exact go .W64 (Or.inr rfl) rfl base? hvb hc
  · cases hc

theorem x64Gpr_leaArith_spec {h : x64Mach.Host} {k w : Nat} {base? : Option Reg64} {idx : Reg64}
    {sc : AddrScale} {disp : Int64} {rd : Reg64} {c : List Directive} {clob : FlagMask}
    {vb vi : BitVec w} {s : MachineData} {post : MachineState → Prop}
    (hc0 : x64Gpr.leaArith w base? idx sc disp rd = some (c, clob))
    (_ : ∀ r, base? = some r → r ∉ x64Scratch) (_ : idx ∉ x64Scratch) (_ : rd ∉ x64Scratch)
    (hvb : ∀ r, base? = some r → GprHolds (x64Mach.getGpr s r) (.bits w) vb)
    (hvi : GprHolds (x64Mach.getGpr s idx) (.bits w) vi) :
    let res : BitVec w :=
      (if base?.isSome then vb else 0#w) + (vi <<< sc.shift) + disp.toBitVec.setWidth w
    x64Mach.FallsTo x64Gpr.condReads h k c (rd :: x64Scratch) [] clob s
      (fun s' => GprHolds (x64Mach.getGpr s' rd) (.bits w) res ∧
        x64Mach.mem s' = x64Mach.mem s) post :=
  fun hinf kont =>
    x64LeaArith_z (w := w) false (fun h => by cases h) hc0 hvb hvi hinf
      fun s' ⟨hg, _, hm⟩ hfr => kont s' ⟨hg, hm⟩ hfr

theorem x64Gpr_leaArith_zero32 (_ : x64Gpr.zeroUpper32LeaArith = true)
    {h : x64Mach.Host} {k : Nat} {base? : Option Reg64} {idx : Reg64} {sc : AddrScale}
    {disp : Int64} {rd : Reg64} {c : List Directive} {clob : FlagMask}
    {vb vi : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc0 : x64Gpr.leaArith 32 base? idx sc disp rd = some (c, clob))
    (_ : ∀ r, base? = some r → r ∉ x64Scratch) (_ : idx ∉ x64Scratch) (_ : rd ∉ x64Scratch)
    (hvb : ∀ r, base? = some r → GprHolds (x64Mach.getGpr s r) (.bits 32) vb)
    (hvi : GprHolds (x64Mach.getGpr s idx) (.bits 32) vi) :
    let res : BitVec 32 :=
      (if base?.isSome then vb else 0#32) + (vi <<< sc.shift) + disp.toBitVec.setWidth 32
    x64Mach.FallsTo x64Gpr.condReads h k c (rd :: x64Scratch) [] clob s
      (fun s' => x64Mach.getGpr s' rd = res.setWidth 64 ∧
        x64Mach.mem s' = x64Mach.mem s) post :=
  fun hinf kont =>
    x64LeaArith_z (w := 32) true (fun _ => rfl) hc0 hvb hvi hinf
      fun s' ⟨_, hz, hm⟩ hfr => kont s' ⟨hz rfl, hm⟩ hfr

theorem x64Gpr_op_boolFlag_spec {h : x64Mach.Host} {k : Nat} {sig : List Ty}
    {code : OpCode sig [.bool]} {pas : Tup (PArg Reg64 RegMm CondCode) sig}
    {pd : PDst Reg64 RegMm CondCode .bool} {cc : CondCode} {vh : VariantHint}
    {c : List Directive} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val [.bool] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hfl : x64Gpr.boolFlagOut? code pas pd = some cc)
    (hc0 : x64Gpr.op code pas (pd, ()) vh = some (c, clob))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ x64Scratch)
    (hdst : ∀ r ∈ pd.gprs, r ∉ x64Scratch)
    (hvs : TRel (x64Mach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    x64Mach.FallsTo x64Gpr.condReads h k c (pd.gprs ++ x64Scratch) [] clob s
      (fun s' => (∃ b : Bool, P (b, ()) ∧ x64Mach.PDstHolds s' .bool pd b ∧
          x64Mach.evalCond s' cc = b) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64Op] at hc0 hfl
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  have finishBool (want : Bool) (hp : P (want, ()))
      (hwp' : ∀ [Host] (E : Int64 → MachineData → Prop),
        _root_.Program.wp (emitClean ci)
          (fun s' => OpPostDst1 .bool pd want clob s s' ∧ cc.interp s'.status = want) E s) :
      x64Mach.FallsTo x64Gpr.condReads h k (emitClean ci) (pd.gprs ++ x64Scratch) [] clob s
        (fun s' => (∃ b : Bool, P (b, ()) ∧ x64Mach.PDstHolds s' .bool pd b ∧
            x64Mach.evalCond s' cc = b) ∧
          x64Mach.mem s' = x64Mach.mem s) post := by
    refine x64_fallsTo_of_wp fun {_} _ => Program.wp.mono (hwp' _) ?_
    rintro s' ⟨⟨hhold, hmem, hfr⟩, hcc⟩
    refine ⟨⟨⟨want, hp, hhold, hcc⟩, hmem⟩, ?_⟩
    simpa [tupDstGprs] using hfr
  cases pd with
  | vec _ | flag _ => simp [x64BoolFlagOut] at hfl
  | gpr rd =>
    cases code with
    | copy =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      exact finishBool va hwp fun {_} _ => opCopyBool_boolFlag_spec hfl hc (trel1 hvs)
    | not =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      exact finishBool (!va) hwp fun {_} _ => opBoolNot_boolFlag_spec hfl hc (trel1 hvs)
    | and | or | xor =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha, hb⟩ := trel2 hvs
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [x64OpIns] at hc
      have hcc_nz : cc = .nz ∧ clob ≠ maskNone := by
        cases pa <;> cases pb <;>
          simp [x64BoolFlagOut, opBoolBinIns, boolBinDstIns, boolBinSelfIns] at hfl hc
        all_goals
          first
          | exact ⟨hfl.symm, fun h => by
              cases hc.2.symm.trans h⟩
          | (subst hfl; refine ⟨rfl, fun h => ?_⟩
             subst h
             repeat' split at hc
             all_goals
               simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq,
                 maskAll, maskNone] at hc
             all_goals
               first
               | exact absurd hc.2 (by decide)
               | (obtain ⟨_, _, _, h2⟩ := hc; exact absurd h2 (by decide))
               | (obtain ⟨_, _, _, _, _, h2⟩ := hc; exact absurd h2 (by decide)))
      rcases hcc_nz with ⟨rfl, hcl⟩
      refine finishBool _ hwp fun {_} _ =>
        Program.wp.mono (opBoolBin_flag_spec _ _
          (by first | exact Bool.and_comm | exact Bool.or_comm | exact Bool.xor_comm)
          (fun dst src s0 _ p0 n0 j0 P0 hk => ?_) hc hdst (arg2_not_sc hargs) ha hb)
          fun _ ⟨h1, h2⟩ => ⟨h1, h2 hcl⟩
      first
      | exact fallsTo_and8 s0 dst src p0 n0 j0 P0 fun _ ⟨st, hzf, hs⟩ =>
          hk _ ⟨_, st, fun a b h1 h2 =>
            ⟨by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le],
             by cases a <;> cases b <;> simp_all⟩, hs⟩
      | exact fallsTo_or8 s0 dst src p0 n0 j0 P0 fun _ ⟨st, hzf, hs⟩ =>
          hk _ ⟨_, st, fun a b h1 h2 =>
            ⟨by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le],
             by cases a <;> cases b <;> simp_all⟩, hs⟩
      | exact fallsTo_xor8 s0 dst src p0 n0 j0 P0 fun _ ⟨st, hzf, hs⟩ =>
          hk _ ⟨_, st, fun a b h1 h2 =>
            ⟨by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le],
             by cases a <;> cases b <;> simp_all⟩, hs⟩
    | _ => simp [x64BoolFlagOut] at hfl

theorem x64Gpr_op_cmpFlags_spec {h : x64Mach.Host} {k : Nat} {co : CmpOp} {n : Nat}
    {pa pb : PArg Reg64 RegMm CondCode (.bits n)} {pd : PDst Reg64 RegMm CondCode .bool}
    {lhsFirst : Bool} {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec n} {s : MachineData} {post : MachineState → Prop}
    (hfl : x64Gpr.cmpFlagsOut? co n pa pb pd = some lhsFirst)
    (hc0 : x64Gpr.op (.cmp co (.bits n) .bool rfl) (pa, pb, ()) (pd, ()) vh = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (_hdst : ∀ r ∈ pd.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits n) pa va) (hpb : x64Mach.PArgHolds s (.bits n) pb vb) :
    x64Mach.FallsTo x64Gpr.condReads h k c (pd.gprs ++ x64Scratch) [] clob s
      (fun s' => x64Mach.PDstHolds s' .bool pd (co.evalBits va vb) ∧
        FlagCmpOk x64Mach x64Gpr s' (if lhsFirst then va else vb)
          (if lhsFirst then vb else va) false ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64Op] at hc0 hfl
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  dsimp only [x64OpIns] at hc
  refine withWidth_elim hc fun w hn hw => ?_
  subst hn
  have hargs' : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch := hargs
  refine x64_fallsTo_of_wp fun {_} _ =>
    Program.wp.mono (opCmp_flags_spec w co hfl hw hargs' hpa hpb) ?_
  rintro s' ⟨⟨hhold, hmem, hfr⟩, hcmp⟩
  refine ⟨⟨hhold, hcmp, hmem⟩, ?_⟩
  simpa [tupDstGprs] using hfr

theorem x64Gpr_op_aluZero_spec {h : x64Mach.Host} {k : Nat} {sig : List Ty} {n : Nat}
    {code : OpCode sig [.bits n]} {pas : Tup (PArg Reg64 RegMm CondCode) sig}
    {pd : PDst Reg64 RegMm CondCode (.bits n)} {eqNe : Bool} {vh : VariantHint}
    {c : List Directive} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val [.bits n] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hfl : x64Gpr.aluZeroOut? n code pd = some eqNe)
    (hcl : clob ≠ FlagMask.none)
    (hc0 : x64Gpr.op code pas (pd, ()) vh = some (c, clob))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ x64Scratch)
    (hdst : ∀ r ∈ pd.gprs, r ∉ x64Scratch)
    (hvs : TRel (x64Mach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    x64Mach.FallsTo x64Gpr.condReads h k c (pd.gprs ++ x64Scratch) [] clob s
      (fun s' => (∃ rv : BitVec n, P (rv, ()) ∧ x64Mach.PDstHolds s' (.bits n) pd rv ∧
          (∀ rd, n = 32 → pd = .gpr rd →
            x64Gpr.zeroUpper32Op code pas (.gpr rd, ()) = true →
            x64Mach.getGpr s' rd = rv.setWidth 64) ∧
          FlagCmpOk x64Mach x64Gpr s' rv 0#n eqNe) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64Op] at hc0 hfl
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  cases pd with
  | vec _ => simp [x64AluZeroOut] at hfl
  | gpr rd =>
    cases code with
    | neg =>
      simp only [x64AluZeroOut, Option.some.injEq] at hfl
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs
      dsimp only [x64OpIns] at hc
      refine withWidth_elim hc fun w hn hw => ?_
      subst hn; subst hfl
      dsimp only [OpCode.wp, Ty.hasFloat, lift1] at hwp
      refine x64_fallsTo_of_wp fun {_} _ =>
        Program.wp.mono (opNeg_aluZero_spec w hcl hw ha) ?_
      rintro s' ⟨⟨hhold, hmem, hfr⟩, hz32, hfc⟩
      refine ⟨⟨⟨-va, hwp, hhold, fun rd' hn heq _ => ?_, hfc⟩, hmem⟩, ?_⟩
      · cases heq; cases w <;> simp [Width.bits] at hn; exact hz32 rfl
      · simpa [tupDstGprs] using hfr
    | add | sub | and | or | xor =>
      simp only [x64AluZeroOut, Option.some.injEq] at hfl
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha, hb⟩ := trel2 hvs
      dsimp only [x64OpIns] at hc
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      refine withWidth_elim hc fun w hn hw => ?_
      subst hn
      refine x64_fallsTo_of_wp fun {_} _ =>
        Program.wp.mono (opBin_aluZero_spec w _ ?_ eqNe ?_ hcl hw
          (hdst rd (by simp [PDst.gprs])) (arg2_not_sc hargs) ha hb) ?_
      · decide
      · rw [← hfl]; decide
      rintro s' ⟨⟨hhold, hmem, hfr⟩, hz32, hfc⟩
      refine ⟨⟨⟨_, hwp, hhold, fun rd' hn heq _ => ?_, hfc⟩, hmem⟩, ?_⟩
      · cases heq; cases w <;> simp [Width.bits] at hn; exact hz32 rfl
      · simpa [tupDstGprs] using hfr
    | _ => simp [x64AluZeroOut] at hfl

/-- Assembled `GprTarget` proof package for `x64Gpr` over `x64Mach` and `x64Scratch`. -/
theorem x64GprSpec : GprTarget x64Mach x64Gpr x64Scratch where
  negCond_reads := x64Gpr_negCond_reads; negCond_eval := x64Gpr_negCond_eval
  clearFlags_spec := x64Gpr_clearFlags_spec; mov_spec := x64Gpr_mov_spec
  movi_spec := x64Gpr_movi_spec
  setcc_spec := x64Gpr_setcc_spec; jmp_spec := x64Gpr_jmp_spec; jcc_spec := x64Gpr_jcc_spec
  jnzGpr_spec := x64Gpr_jnzGpr_spec; op_spec := x64Gpr_op_spec
  load_spec := x64Gpr_load_spec; store_spec := x64Gpr_store_spec
  load_zero32 := fun h0 {_ _ _ _ _ _ s post v} hc hrd ha hlv =>
    x64Gpr_load_zero32 h0 (s := s) (post := post) (v := v) hc hrd ha hlv
  load_zext := fun _ {_ _ _ _ _ _ _ v s post} hc hrd ha hlv =>
    x64Gpr_load_zext (v := v) (s := s) (post := post) hc hrd ha hlv
  op_zero32 := x64Gpr_op_zero32
  testOp_spec := x64Gpr_testOp_spec
  cmpMem_spec := x64Gpr_cmpMem_spec
  testMem_spec := x64Gpr_testMem_spec
  loadSext_spec := x64Gpr_loadSext_spec
  aluMem_spec := x64Gpr_aluMem_spec
  aluMem_zero32 := x64Gpr_aluMem_zero32
  jnzMem_spec := x64Gpr_jnzMem_spec
  rmwMem_spec := x64Gpr_rmwMem_spec
  leaArith_spec := x64Gpr_leaArith_spec
  leaArith_zero32 := x64Gpr_leaArith_zero32
  jnzGprInv_spec := fun hfn => x64Gpr_jnzGprInv_spec hfn
  op_boolFlag_spec := x64Gpr_op_boolFlag_spec
  op_cmpFlags_spec := x64Gpr_op_cmpFlags_spec
  op_aluZero_spec := x64Gpr_op_aluZero_spec
  testOp_boolFlag_spec := x64Gpr_testOp_boolFlag_spec
  testMem_boolFlag_spec := x64Gpr_testMem_boolFlag_spec
  cmpMem_flags_spec := x64Gpr_cmpMem_flags_spec

end

end LeanQbe.T.Amd64
