module

public import LeanQbe.T.Amd64.IselLemmasBitcnt

/-!
# x64 Scalar `GprTarget` Proofs — Part 5 (`T8`)

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

private theorem arg2_nv {t1 t2 : Ty} {ts : List Ty} {pas : Tup (PArg Reg64 RegMm CondCode) (t1 :: t2 :: ts)}
    (h : tupArgVecs pas = []) : ∀ r, pas.2.1 ≠ .vec r := fun r he => by
  rcases pas with ⟨pa, pb, as⟩; simp only at he; subst he; cases pa <;> simp [tupArgVecs] at h

private theorem arg3_nv {t1 t2 t3 : Ty} {ts : List Ty}
    {pas : Tup (PArg Reg64 RegMm CondCode) (t1 :: t2 :: t3 :: ts)}
    (h : tupArgVecs pas = []) : ∀ r, pas.2.2.1 ≠ .vec r := fun r he => by
  rcases pas with ⟨pa, pb, pc, as⟩; simp only at he; subst he; cases pa <;> cases pb <;> simp [tupArgVecs] at h

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
        | contradiction | (change (x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n) = true; simp_all))
    | (change opSextIns m n pa _ = _ at h; unfold opSextIns at h; split at h <;> first
        | contradiction | (change (x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n) = true; simp_all))
    | (change opTruncIns m n pa _ = _ at h; unfold opTruncIns at h; split at h <;> first
        | contradiction | (change (x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (n + 1) m) = true; simp_all))
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
    next hn => have hm := width_mem _ _ h; change (x64BitWidths.contains _ && x64BitWidths.contains _) = true; rw [Bool.and_eq_true]; exact ⟨hm, hn⟩
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
    | ((unfold opBinIns; dsimp only; repeat' split) <;> rfl)

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

theorem x64SupportsScalarOp_complete {sig rs : List Ty} {code : OpCode sig rs} {u : Tup (Arg (fun _ => Unit)) sig}
    (hsup : x64Gpr.supportsScalarOp code u = true)
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    (hp : tupArgVecs pas = [])
    (hd : tupDstVecs dsts = [] ∧ (tupDstGprs dsts).length = rs.length ∧ (tupDstGprs dsts).Nodup ∧ ∀ r ∈ tupDstGprs dsts, r ∉ x64Scratch) :
    (x64Gpr.op code pas dsts .default).isSome = true := by
  dsimp only [x64Gpr, x64Op] at hsup ⊢
  simp only [emitCleanPair_isSome]
  cases code
  all_goals first | exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup | skip
  case copy t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    · have ha := arg1_nv hp; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
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
    · have ha := arg1_nv hp; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      cases pa <;> first
        | exact absurd rfl (ha _)
        | (dsimp only [x64OpIns]; simp [opBoolNotIns, boolArgTo8I] <;> rfl)
    · rename_i n; change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> cases pa <;> first
        | exact absurd rfl (ha _) | (dsimp only [x64OpIns]; simp [opNotIns] <;> rfl)
  case add t | sub t | mul t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i n; change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> exact opBinIns_isSome _ _ _ ha hb
  case and t | or t | xor t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    · have ha := arg1_nv hp; have hb := arg2_nv hp
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      cases pa <;> cases pb <;> first
        | exact absurd rfl (ha _) | exact absurd rfl (hb _)
        | (dsimp only [x64OpIns]; simp [opBoolBinIns, boolArgTo8I] <;> rfl)
    · rename_i n; change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp; have hb := arg2_nv hp
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> exact opBinIns_isSome _ _ _ ha hb
  case shl t | lshr t | ashr t | rotl t | rotr t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i n; change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> exact opShiftIns_isSome _ _ _ ha hb
  case bswap t =>
    cases t with
    | bits n =>
      change [16, 32, 64].contains n = true at hsup; have ha := arg1_nv hp
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
      rcases (by omega : n = 16 ∨ n = 32 ∨ n = 64 ∨ (n ≠ 16 ∧ n ≠ 32 ∧ n ≠ 64)) with rfl | rfl | rfl | ⟨h1, h2, h3⟩
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
    rename_i n; change x64BitWidths.contains n = true at hsup; subst hm; have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;>
      cases pa <;> cases pb <;> first
        | exact absurd rfl (ha _) | exact absurd rfl (hb _)
        | ((dsimp only [x64OpIns]; simp [withWidth, opCmpIns, cmpDirectIns]; repeat' split) <;> rfl)
  case select t =>
    cases t <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i n; change x64BitWidths.contains n = true at hsup; have hc' := arg1_nv hp; have ha := arg2_nv hp; have hb := arg3_nv hp
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;>
      exact opSelectIns_isSome _ _ hc' ha hb
  case zext m n | sext m n | trunc m n =>
    first | change (x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (m + 1) n) = true at hsup
          | change (x64BitWidths.contains m && x64BitWidths.contains n && Nat.ble (n + 1) m) = true at hsup
    simp only [Bool.and_eq_true, Nat.ble_eq] at hsup; rcases hsup with ⟨⟨hm, hn⟩, hord⟩
    have ha := arg1_nv hp; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hm with rfl | rfl | rfl | rfl <;> rcases mem_x64BitWidths hn with rfl | rfl | rfl | rfl <;> try omega
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
    change x64WideWidths.contains n = true at hsup; have ha := arg1_nv hp; have hb := arg2_nv hp; have hc' := arg3_nv hp
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64WideWidths hsup with rfl | rfl <;> exact opFunnelIns_isSome _ _ _ ha hb hc'
  case addc n | subb n =>
    change x64WideWidths.contains n = true at hsup
    rcases mem_x64WideWidths hsup with rfl | rfl <;> (
      rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; have ha : ∀ r, pa ≠ .vec r := arg1_nv hp
      have hb : ∀ r, pb ≠ .vec r := arg2_nv hp; have hc' : ∀ r, pc ≠ .vec r := arg3_nv hp
      rcases dsts with ⟨d0, d1, ⟨⟩⟩; cases d0 <;> cases d1 <;> simp [tupDstGprs, List.nodup_cons] at hd
      rename_i r0 r1; have hne : (r1 != r0) = true := by cases r0 <;> cases r1 <;> first | exact absurd rfl hd.2.1 | rfl
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
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d0, d1, ⟨⟩⟩; cases d0 <;> cases d1 <;> simp [tupDstGprs, List.nodup_cons] at hd
    rename_i rlo rhi; have hne : (rlo == rhi) = false := by cases rlo <;> cases rhi <;> first | exact absurd rfl hd.2.1 | rfl
    rcases mem_x64WideWidths hsup with rfl | rfl <;> cases pa <;> cases pb <;> first
      | exact absurd rfl (ha _) | exact absurd rfl (hb _)
      | (dsimp only [x64OpIns]; simp [withWideWidth, opMulwIns, argToBitsI, hne])
  case udiv n | sdiv n | urem n | srem n =>
    change x64BitWidths.contains n = true at hsup; have ha := arg1_nv hp; have hb := arg2_nv hp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs, x64Scratch] at hd; rename_i rd
    have h10 : (rd == .r10) = false := by cases rd <;> first | exact absurd rfl hd.2.1 | rfl
    have h11 : (rd == .r11) = false := by cases rd <;> first | exact absurd rfl hd.2.2 | rfl
    rcases mem_x64BitWidths hsup with rfl | rfl | rfl | rfl <;> cases pa <;> cases pb <;> first
      | exact absurd rfl (ha _) | exact absurd rfl (hb _)
      | (dsimp only [x64OpIns]; simp [withWidth, opDivIns, h10, h11])
  case bitcast t1 t2 hb =>
    cases t1 <;> cases t2 <;> try exact false_ne_true_of (rfl : x64SupportsScalarOp _ u = false) hsup
    rename_i m n; change (x64BitWidths.contains m && x64BitWidths.contains n) = true at hsup; simp only [Bool.and_eq_true] at hsup
    have ha := arg1_nv hp; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; cases pd <;> simp [tupDstGprs] at hd
    rcases mem_x64BitWidths hsup.1 with rfl | rfl | rfl | rfl <;>
      (dsimp only [x64OpIns]; rw [hsup.2]; exact opCopyBitsIns_isSome _ _ ha)

/-! ## 2. Unified `x64Gpr_op_spec` and `x64GprSpec` -/

private theorem arg2_not_sc {t1 t2} {pa : PArg Reg64 RegMm CondCode t1} {pb : PArg Reg64 RegMm CondCode t2}
    (h : ∀ r ∈ @tupArgGprs Reg64 RegMm CondCode [t1, t2] (pa, pb, ()), r ∉ x64Scratch) :
    ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch := fun r hr => h r (by
  cases pa <;> cases pb <;> simp [PArg.gprs, tupArgGprs] at hr ⊢ <;> grind)

private theorem arg3_not_sc {t1 t2 t3} {pa : PArg Reg64 RegMm CondCode t1}
    {pb : PArg Reg64 RegMm CondCode t2} {pc : PArg Reg64 RegMm CondCode t3}
    (h : ∀ r ∈ @tupArgGprs Reg64 RegMm CondCode [t1, t2, t3] (pa, pb, pc, ()), r ∉ x64Scratch) :
    ∀ r ∈ pa.gprs ++ pb.gprs ++ pc.gprs, r ∉ x64Scratch := fun r hr => h r (by
  cases pa <;> cases pb <;> cases pc <;> simp [PArg.gprs, tupArgGprs] at hr ⊢ <;> grind)

private theorem trel1 {R : ∀ t, PArg Reg64 RegMm CondCode t → Val t → Prop} {t}
    {pa : PArg Reg64 RegMm CondCode t} {va : Val t} (h : TRel R (as := [t]) (pa, ()) (va, ())) : R t pa va := by
  cases h with | cons a _ => exact a

private theorem trel2 {R : ∀ t, PArg Reg64 RegMm CondCode t → Val t → Prop} {t1 t2}
    {pa : PArg Reg64 RegMm CondCode t1} {pb : PArg Reg64 RegMm CondCode t2} {va : Val t1} {vb : Val t2}
    (h : TRel R (as := [t1, t2]) (pa, pb, ()) (va, vb, ())) : R t1 pa va ∧ R t2 pb vb := by
  cases h with | cons a h1 => cases h1 with | cons b _ => exact ⟨a, b⟩

private theorem trel3 {R : ∀ t, PArg Reg64 RegMm CondCode t → Val t → Prop} {t1 t2 t3}
    {pa : PArg Reg64 RegMm CondCode t1} {pb : PArg Reg64 RegMm CondCode t2} {pc : PArg Reg64 RegMm CondCode t3}
    {va : Val t1} {vb : Val t2} {vc : Val t3} (h : TRel R (as := [t1, t2, t3]) (pa, pb, pc, ()) (va, vb, vc, ())) :
    R t1 pa va ∧ R t2 pb vb ∧ R t3 pc vc := by
  cases h with | cons a h1 => cases h1 with | cons b h2 => cases h2 with | cons c _ => exact ⟨a, b, c⟩

theorem x64Gpr_op_spec {h : x64Mach.Host} {k : Nat} {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val rs → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc0 : x64Gpr.op code pas dsts vh = some (c, clob))
    (hargs : ∀ r ∈ tupArgGprs pas, r ∉ x64Scratch) (hdst : ∀ r ∈ tupDstGprs dsts, r ∉ x64Scratch)
    (hvs : TRel (x64Mach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    x64Mach.FallsTo x64Gpr.condReads h k c (tupDstGprs dsts ++ x64Scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧ x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64Op] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  cases code
  all_goals first | exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) hc | skip
  case copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    · dsimp only [x64OpIns] at hc; exact opPostDst1_fallsTo hwp fun {_} _ => opCopyBool_spec hc ha
    · (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
      dsimp only [x64OpIns] at hc
      exact withWidth_elim hc fun w hn hw => by subst hn; exact opPost1_fallsTo hwp fun {_} _ => opCopyBits_spec w hw ha
  case add t | sub t | mul t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      exact opPost1_fallsTo hwp fun {_} _ => opBin_spec w _ hw (hdst rd (by simp [tupDstGprs])) (arg2_not_sc hargs) ha hb
  case and t | or t | xor t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    · dsimp only [x64OpIns] at hc; dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      refine opPostDst1_fallsTo hwp fun {_} _ => opBoolBin_spec _ _ (fun s0 _ p0 n0 j0 P0 hk => ?_) hc ha hb (arg2_not_sc hargs)
      first
      | exact fallsTo_and8 s0 .r11 .r10 p0 n0 j0 P0 fun _ ⟨st, hs⟩ => hk _ ⟨_, st, fun a b h1 h2 => by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le], hs⟩
      | exact fallsTo_or8 s0 .r11 .r10 p0 n0 j0 P0 fun _ ⟨st, hs⟩ => hk _ ⟨_, st, fun a b h1 h2 => by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le], hs⟩
      | exact fallsTo_xor8 s0 .r11 .r10 p0 n0 j0 P0 fun _ ⟨st, hs⟩ => hk _ ⟨_, st, fun a b h1 h2 => by cases a <;> cases b <;> simp_all [replaceLow_setWidth_le], hs⟩
    · (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
      dsimp only [x64OpIns] at hc
      rename_i rd; exact withWidth_elim hc fun w hn hw => by
        subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
        exact opPost1_fallsTo hwp fun {_} _ => opBin_spec w _ hw (hdst rd (by simp [tupDstGprs])) (arg2_not_sc hargs) ha hb
  case neg t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    exact withWidth_elim hc fun w hn hw => by subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift1] at hwp; exact opPost1_fallsTo hwp fun {_} _ => opNeg_spec w hw ha
  case not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    · dsimp only [x64OpIns] at hc; exact opPostDst1_fallsTo hwp fun {_} _ => opBoolNot_spec hc ha
    · (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
      dsimp only [x64OpIns] at hc
      exact withWidth_elim hc fun w hn hw => by subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift1] at hwp; exact opPost1_fallsTo hwp fun {_} _ => opNot_spec w hw ha
  case shl t | lshr t | ashr t | rotl t | rotr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      exact opPost1_fallsTo hwp fun {_} _ => opShift_spec w _ hw (hdst rd (by simp [tupDstGprs])) (arg2_not_sc hargs) ha hb
  case fshl n | fshr n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases vs with ⟨va, vb, vc, ⟨⟩⟩; obtain ⟨ha, hb, hc'⟩ := trel3 hvs
    rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWideWidth_elim hc fun w hn hw => by
      subst hn; cases w <;> (first
        | (unfold withWideWidth at hc; contradiction)
        | exact opPost1_fallsTo hwp fun {_} _ => opFunnel_spec _ (by first | exact .inl rfl | exact .inr rfl) _ hw (hdst rd (by simp [tupDstGprs])) (arg3_not_sc hargs) ha hb hc')
  case bswap t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i n _; have hok := (@opBswap_spec _ (fun _ _ => True) n pa _ ci clob va s hc ha).1
    dsimp only [OpCode.wp, lift1] at hwp; simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwp
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
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    dsimp only [x64OpIns] at hc; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, Ty.hasFloat, liftCmp] at hwp
      exact opPostDst1_fallsTo hwp fun {_} _ => opCmp_spec w co hw (arg2_not_sc hargs) ha hb
  case select t =>
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases vs with ⟨vc, va, vb, ⟨⟩⟩; obtain ⟨hc', ha, hb⟩ := trel3 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; exact opPost1_fallsTo hwp fun {_} _ => opSelect_spec w hw (hdst rd (by simp [tupDstGprs])) (arg3_not_sc hargs) hc' ha hb
  case zext m n | sext m n | trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    exact opPost1_fallsTo hwp.2 fun {_} _ => by first | exact (opZext_spec m n hc ha).2 | exact (opSext_spec m n hc ha).2 | exact (opTrunc_spec m n hc ha).2
  case ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc; split at hc <;> try contradiction
    next hnw =>
      rcases mem_x64BitWidths hnw with rfl | rfl | rfl | rfl <;> (first
        | exact opPost1_fallsTo hwp fun {_} _ => opOfBool_spec .W8 hc ha
        | exact opPost1_fallsTo hwp fun {_} _ => opOfBool_spec .W16 hc ha
        | exact opPost1_fallsTo hwp fun {_} _ => opOfBool_spec .W32 hc ha
        | exact opPost1_fallsTo hwp fun {_} _ => opOfBool_spec .W64 hc ha)
  case addc n | subb n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases vs with ⟨va, vb, vc, ⟨⟩⟩; obtain ⟨ha, hb, hc'⟩ := trel3 hvs
    rcases dsts with ⟨d0, d1, ⟨⟩⟩; dsimp only [x64OpIns] at hc
    exact withWideWidth_elim hc fun w hn hw => by
      subst hn; cases w <;> (first
        | (unfold withWideWidth at hc; contradiction)
        | exact opPost2_fallsTo hwp fun {_} _ => opAddc_spec _ (by first | exact .inl rfl | exact .inr rfl) hw (arg3_not_sc hargs) hdst ha hb hc'
        | exact opPost2_fallsTo hwp fun {_} _ => opSubb_spec _ (by first | exact .inl rfl | exact .inr rfl) hw (arg3_not_sc hargs) hdst ha hb hc')
  case umulw n | smulw n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; obtain ⟨ha, hb⟩ := trel2 hvs
    rcases dsts with ⟨d0, d1, ⟨⟩⟩; dsimp only [x64OpIns] at hc
    exact withWideWidth_elim hc fun w hn hw => by
      subst hn; cases w <;> (first
        | (unfold withWideWidth at hc; contradiction)
        | exact opPost2_fallsTo hwp fun {_} _ => opMulw_spec _ (by first | exact .inl rfl | exact .inr rfl) _ hw (arg2_not_sc hargs) hdst ha hb)
  case udiv n | sdiv n | urem n | srem n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩; obtain ⟨ha, hb⟩ := trel2 hvs; rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc
    rename_i rd; exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp] at hwp
      exact opPost1_fallsTo hwp.2 fun {_} _ => opDiv_spec w _ _ hw (hdst rd (by simp [tupDstGprs])) (arg2_not_sc hargs) ha hb hwp.1
  case bitcast t1 t2 hb =>
    cases t1 <;> cases t2 <;> try exact none_ne_some (rfl : x64OpIns _ pas dsts vh = none) hc
    rename_i m n; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact none_ne_some (rfl : x64OpIns _ _ _ _ = none) hc)
    dsimp only [x64OpIns] at hc; split at hc <;> try contradiction
    rcases vs with ⟨va, ⟨⟩⟩; have ha := trel1 hvs; have hmn : m = n := hb; subst hmn
    exact withWidth_elim hc fun w hn hw => by
      subst hn; dsimp only [OpCode.wp, toBits, ofBits, BitVec.cast] at hwp; exact opPost1_fallsTo hwp fun {_} _ => opCopyBits_spec w hw ha

/-- Assembled `GprTarget` proof package for `x64Gpr` over `x64Mach` and `x64Scratch`. -/
theorem x64GprSpec : GprTarget x64Mach x64Gpr x64Scratch where
  negCond_reads := x64Gpr_negCond_reads; negCond_eval := x64Gpr_negCond_eval
  clearFlags_spec := x64Gpr_clearFlags_spec; mov_spec := x64Gpr_mov_spec; movi_spec := x64Gpr_movi_spec
  setcc_spec := x64Gpr_setcc_spec; jmp_spec := x64Gpr_jmp_spec; jcc_spec := x64Gpr_jcc_spec
  jnzGpr_spec := x64Gpr_jnzGpr_spec; op_spec := x64Gpr_op_spec
  load_spec := x64Gpr_load_spec; store_spec := x64Gpr_store_spec

end

end LeanQbe.T.Amd64
