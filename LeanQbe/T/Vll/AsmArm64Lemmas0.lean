module

public import LeanQbe.T.Vll.Sem
public import LeanQbe.T.Vll.AsmArm64
import LeanQbe.T.Arm64.IselLemmas1
import LeanQbe.T.Arm64.FrameLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import Kraken.AArch64.WP.Control

/-!
# AArch64 `BedrockMach` L1 Assembler Simulation Base (`Vll.AsmArm64Lemmas0`)

Foundational definitions and lemmas for `LeanQbe.T.Vll.AsmArm64Lemmas`:

* `hostSymAddr`, `instrListClobFlags`, `ExecBodyOk`.
* Label-index map `ρ` (`asmArm64Offset`) preservation: `asmArm64_noLab`, `asmArm64List_append`,
  `asmArm64Offset_{zero,succ,mono}`, `asmArm64List_infixAt`, `asmArm64List_label_getElem?`,
  `asmArm64List_definedLabels`, `asmArm64List_labelsUnique`, `asmArm64List_label_addr`.
* State-relation / frame helpers & sub-word 8/16-bit exact NZCV flag lemmas.
* Direct operand, total `AddrArg`, load/store, and stack-frame `Program.wp` lemmas.
* Generic `.native d` state-agreement simulation (`asmNative_fallsTo_wp`, `asmNative_jump_run`).

Strictly AArch64 only (zero `Amd64`/`Kraken.X64` imports, zero `@[expose]` on theorems/lemmas).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open LeanQbe.T.Arm64

/-! ## 1. Host Symbol Map, `ExecBodyOk`, and Label-Map `ρ` Preservation -/

/-- VLL symbol-to-address map induced by a Kraken AArch64 `Host`. -/
@[expose] def hostSymAddr (h : Host) : Sym → BitVec 64 :=
  fun l => (armMach.labelAddr h l).toBitVec

/-- Combined flag clobber mask of a straight-line VLL instruction list. -/
@[expose] def instrListClobFlags (is : List (Instr arm64Arch)) : FlagMask :=
  is.foldr (fun i m => i.clobFlags ||| m) maskNone

/-- Straight-line VLL execution where every step satisfies `arm64InstrOk`. -/
inductive ExecBodyOk (symAddr : Sym → BitVec 64) :
    List (Instr arm64Arch) → MachSt arm64Arch → MachSt arm64Arch → Prop where
  | nil {s} : ExecBodyOk symAddr [] s s
  | cons {i is s s₁ s'} :
      arm64InstrOk i s →
      instrRel arm64Arch symAddr 0#64 i s (.fall s₁) →
      ExecBodyOk symAddr is s₁ s' →
      ExecBodyOk symAddr (i :: is) s s'

private theorem labelsOfSymAddr_hostSymAddr [h : Host] :
    labelsOfSymAddr (hostSymAddr h) = (inferInstance : Labels) := by
  have hfn : (labelsOfSymAddr (hostSymAddr h)).label = (inferInstance : Labels).label := by
    funext l
    exact Int64.ofBitVec_toBitVec (Labels.label l)
  cases h1 : labelsOfSymAddr (hostSymAddr h)
  cases h2 : (inferInstance : Labels)
  rw [h1, h2] at hfn
  exact congrArg Labels.mk hfn

theorem asmArm64_noLab (i : Instr arm64Arch) (l : Sym)
    (hnotLab : i ≠ .label l) (hnotNat : ∀ d, i = .native d → d ≠ .label l) :
    Kraken.Directive.label l ∉ asmArm64 i := by
  cases i with
  | label s =>
    simp only [asmArm64, List.mem_singleton, Kraken.Directive.label.injEq]
    intro h; exact hnotLab (h ▸ rfl)
  | mov _ _ _ | alu _ _ _ _ _ _ | cmp _ _ _ | test _ _ _ | load _ _ _ _ | store _ _ _
  | jnzGpr _ _ =>
    exact emitClean_noLab _ l
  | movi _ _ => exact armMovi_noLab _ _ l
  | clearFlags => exact armClearFlags_noLab l
  | setcc _ _ => exact armSetcc_noLab _ _ l
  | slotSt _ _ => exact armSlotSt_noLab _ _ l
  | slotLd _ _ => exact armSlotLd_noLab _ _ l
  | prologue _ => exact armPrologue_noLab _ l
  | epilogue _ => exact armEpilogue_noLab _ l
  | canonAbi _ _ => exact armCanonAbi_noLab _ _ l
  | jmp _ => exact armJmp_noLab _ l
  | jcc _ _ => exact armJcc_noLab _ _ l
  | call _ => exact armCall_noLab _ l
  | ret => exact armRet_noLab l
  | exitJmp _ => exact armExitJmp_noLab _ l
  | icall r =>
    cases r with | reg x => exact armCallReg_noLab (.reg x) l | SP => simp [asmArm64]
  | tailJmpR r | ijmp r =>
    cases r with | reg x => exact armJmpReg_noLab (.reg x) l | SP => simp [asmArm64]
  | symAddr sym rd =>
    cases rd with
    | reg x => exact armSymAddrReg_noLab sym (.reg x) l
    | SP => simp [asmArm64, armSymAddr]
  | pad _ => simp [asmArm64]
  | native d =>
    simp only [asmArm64, List.mem_singleton]
    intro h; exact hnotNat d rfl h.symm

theorem asmArm64List_append (xs ys : List (Instr arm64Arch)) :
    asmArm64List (xs ++ ys) = asmArm64List xs ++ asmArm64List ys :=
  List.flatMap_append

theorem asmArm64Offset_zero (prog : List (Instr arm64Arch)) :
    asmArm64Offset prog 0 = 0 := rfl

theorem asmArm64Offset_succ {prog : List (Instr arm64Arch)} {k : Nat} {i : Instr arm64Arch}
    (hk : prog[k]? = some i) :
    asmArm64Offset prog (k + 1) = asmArm64Offset prog k + (asmArm64 i).length := by
  dsimp only [asmArm64Offset]
  rw [List.take_add_one, hk, Option.toList_some, asmArm64List_append, List.length_append]
  simp [asmArm64List]

theorem asmArm64Offset_mono {prog : List (Instr arm64Arch)} {j k : Nat} (h : j ≤ k) :
    asmArm64Offset prog j ≤ asmArm64Offset prog k := by
  have htake : prog.take k = prog.take j ++ (prog.drop j).take (k - j) := by
    rw [← List.take_add, Nat.add_sub_cancel' h]
  simp only [asmArm64Offset, htake, asmArm64List_append, List.length_append]
  omega

theorem asmArm64List_infixAt {prog : List (Instr arm64Arch)} {k : Nat} {i : Instr arm64Arch}
    (hk : prog[k]? = some i) :
    (asmArm64 i).IsInfixAt (asmArm64List prog) (asmArm64Offset prog k) := by
  have hlen : k < prog.length := (List.getElem?_eq_some_iff.mp hk).1
  have hsplit : prog = prog.take k ++ i :: prog.drop (k + 1) := by
    have h1 := (List.take_append_drop k prog).symm
    have h2 : prog.drop k = i :: prog.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hlen]
      have hget : prog[k] = i := Option.some.inj (by rw [← List.getElem?_eq_getElem hlen, hk])
      rw [hget]
    rw [h2] at h1
    exact h1
  refine ⟨asmArm64List (prog.drop (k + 1)), ?_⟩
  rw [asmArm64Offset]
  conv => rhs; arg 2; rw [hsplit]
  rw [asmArm64List_append, List.drop_left]
  rfl

theorem asmArm64List_label_getElem? {prog : List (Instr arm64Arch)} {k : Nat} {l : Sym}
    (hk : prog[k]? = some (.label l)) :
    (asmArm64List prog)[asmArm64Offset prog k]? = some (.label l) :=
  List.isInfixAt_singleton.mp (asmArm64List_infixAt hk)

private theorem definedLabels_eq_nil_of_noLab {ds : List _root_.Directive}
    (h : ∀ l, Kraken.Directive.label l ∉ ds) :
    _root_.Program.definedLabels ds = [] := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | label l => exact absurd List.mem_cons_self (h l)
    | instr _ | byteArray _ | word _ _ =>
      simpa [_root_.Program.definedLabels] using
        ih (fun l hm => h l (List.mem_cons_of_mem _ hm))

theorem asmArm64List_definedLabels (prog : List (Instr arm64Arch))
    (hnoNatLab : ∀ d, Instr.native d ∈ prog → ∀ l, d ≠ .label l) :
    _root_.Program.definedLabels (asmArm64List prog) = prog.filterMap Instr.label? := by
  induction prog with
  | nil => rfl
  | cons i rest ih =>
    have hrest : ∀ d, Instr.native d ∈ rest → ∀ l, d ≠ .label l :=
      fun d hm => hnoNatLab d (List.mem_cons_of_mem _ hm)
    have hcons : asmArm64List (i :: rest) = asmArm64 i ++ asmArm64List rest := rfl
    rw [hcons]
    have hdef : _root_.Program.definedLabels (asmArm64 i ++ asmArm64List rest) =
        _root_.Program.definedLabels (asmArm64 i) ++
          _root_.Program.definedLabels (asmArm64List rest) :=
      List.filterMap_append
    rw [hdef, ih hrest]
    by_cases hlab : ∃ l, i = .label l
    · rcases hlab with ⟨l, rfl⟩
      simp [asmArm64, _root_.Program.definedLabels, Instr.label?]
    · have hnol : ∀ l, i ≠ .label l := fun l e => hlab ⟨l, e⟩
      have h0 : _root_.Program.definedLabels (asmArm64 i) = [] :=
        definedLabels_eq_nil_of_noLab fun l => asmArm64_noLab i l (hnol l)
          (fun d hd => hnoNatLab d (hd ▸ List.mem_cons_self) l)
      have hil : i.label? = none := by
        cases i with
        | label l => exact absurd rfl (hnol l)
        | _ => rfl
      rw [h0, List.nil_append]; simp [hil]

theorem asmArm64List_labelsUnique [Host] (prog : List (Instr arm64Arch))
    (hprog : Host.prog = asmArm64List prog)
    (hnoNatLab : ∀ d, Instr.native d ∈ prog → ∀ l, d ≠ .label l)
    (hnodup : (prog.filterMap Instr.label?).Nodup) :
    Host.LabelsUnique := by
  apply Host.labelsUnique_of_nodup
  rw [hprog, asmArm64List_definedLabels prog hnoNatLab]
  exact hnodup

theorem asmArm64List_label_addr [Host] (prog : List (Instr arm64Arch)) {k : Nat} {l : Sym}
    (hprog : Host.prog = asmArm64List prog)
    (huniq : Host.LabelsUnique)
    (hk : prog[k]? = some (.label l)) :
    Labels.label l = Host.addrOf (asmArm64Offset prog k) :=
  Host.label_eq_addrOf_of_unique huniq (by rw [hprog]; exact asmArm64List_label_getElem? hk)

/-! ## 2. State-Agreement, Framing, and Sub-Word BitVec / NZCV Flag Lemmas -/

theorem Reg64s_getXReg_setSP (regs : Reg64s) (v : UInt64) (x : XReg) :
    ({ regs with SP := v } : Reg64s).getXReg x = regs.getXReg x := by
  cases x <;> rfl

theorem armFrame_trans_or {s₁ s₂ s₃ : MachineData} {g₁ g₂ : List Arm64.Reg} {f₁ f₂ : FlagMask}
    (h1 : armMach.Frame armCondReads s₁ s₂ g₁ [] f₁)
    (h2 : armMach.Frame armCondReads s₂ s₃ g₂ [] f₂) :
    armMach.Frame armCondReads s₁ s₃ (g₁ ++ g₂) [] (f₁ ||| f₂) := by
  refine ⟨fun r hr => ?_, fun v => v.elim, fun c hc => ?_⟩
  · rw [List.mem_append, not_or] at hr
    exact (h2.1 r hr.2).trans (h1.1 r hr.1)
  · have h12 : FlagMask.disjoint (armCondReads c) f₁ = true ∧
        FlagMask.disjoint (armCondReads c) f₂ = true := by
      simp only [FlagMask.disjoint, beq_iff_eq] at hc ⊢
      have hdist : (armCondReads c &&& f₁) ||| (armCondReads c &&& f₂) = 0#8 := by
        rw [← BitVec.and_or_distrib_left]; exact hc
      constructor <;> (
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        have hb := congrArg (fun x : BitVec 8 => x.getLsbD i) hdist
        simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.or_eq_false_iff] at hb
        first | simpa using hb.1 | simpa using hb.2)
    exact (h2.2.2 c h12.2).trans (h1.2.2 c h12.1)

theorem armFrame_weaken_clob {s s' : MachineData} {g₁ g₂ : List Arm64.Reg} {f₁ f₂ : FlagMask}
    (h : armMach.Frame armCondReads s s' g₁ [] f₁)
    (hg : ∀ r ∈ g₁, r ∈ g₂) (hf : f₁ = f₂ ∨ f₂ = maskAll ∨ f₂ = maskNZCV) :
    armMach.Frame armCondReads s s' g₂ [] f₂ := by
  refine ⟨fun r hr => h.1 r (fun hm => hr (hg r hm)), fun v => v.elim, fun c hc => ?_⟩
  rcases hf with rfl | rfl | rfl
  · exact h.2.2 c hc
  · cases c <;>
      simp [FlagMask.disjoint, armCondReads, maskAll, maskN, maskZ, maskC, maskV] at hc
  · cases c <;>
      simp [FlagMask.disjoint, armCondReads, maskNZCV, maskN, maskZ, maskC, maskV] at hc

theorem stateRel_updGpr {sv : MachSt arm64Arch} {sm sm' : MachineData}
    (hrel : arm64StateRel sv sm) (rd : Arm64.Reg) (v : BitVec 64)
    (hrd : Arm64.get sm' rd = v)
    (hkeep : ∀ r, r ≠ rd → r ∉ armScratch → Arm64.get sm' r = Arm64.get sm r)
    (hst : sm'.status = sm.status) (hmem : sm'.dmem = sm.dmem) :
    arm64StateRel (sv.setGpr rd v) sm' ∧
    armMach.Frame armCondReads sm sm' (rd :: armScratch) [] maskNone := by
  refine ⟨⟨fun r hr => ?_, hst.trans hrel.2.1, hmem.trans hrel.2.2⟩,
    armFrame_status_eq (fun r hr => ?_) hst⟩
  · by_cases heq : r = rd
    · subst heq; simp [hrd]
    · rw [hkeep r heq hr, hrel.1 r hr, MachSt.gpr_setGpr_ne sv v heq]
  · rw [List.mem_cons, not_or] at hr; exact hkeep r hr.1 hr.2

theorem stateRel_updGprFlags {sv : MachSt arm64Arch} {sm sm' : MachineData}
    (hrel : arm64StateRel sv sm) (rd : Arm64.Reg) (v : BitVec 64) (f' : StatusFlags)
    (fClob : FlagMask) (hrd : Arm64.get sm' rd = v)
    (hkeep : ∀ r, r ≠ rd → r ∉ armScratch → Arm64.get sm' r = Arm64.get sm r)
    (hst : sm'.status = f')
    (hfOk : f' = sm.status ∨ fClob = maskNZCV ∨ fClob = maskAll)
    (hmem : sm'.dmem = sm.dmem) :
    arm64StateRel ((sv.setGpr rd v).setFlags f') sm' ∧
    armMach.Frame armCondReads sm sm' (rd :: armScratch) [] fClob := by
  refine ⟨⟨fun r hr => ?_, hst, hmem.trans hrel.2.2⟩, ?_⟩
  · by_cases heq : r = rd
    · subst heq; simp [hrd]
    · rw [hkeep r heq hr, hrel.1 r hr, MachSt.gpr_setFlags, MachSt.gpr_setGpr_ne sv v heq]
  · have hk : ∀ r, r ∉ rd :: armScratch → Arm64.get sm' r = Arm64.get sm r := fun r hr => by
      rw [List.mem_cons, not_or] at hr; exact hkeep r hr.1 hr.2
    rcases hfOk with heq | rfl | rfl
    · exact armFrame_status_eq hk (hst.trans heq)
    · exact armFrame_nzcv hk
    · exact armFrame_upd_regs hk (Or.inl rfl)

theorem stateRel_updFlags {sv : MachSt arm64Arch} {sm sm' : MachineData}
    (hrel : arm64StateRel sv sm) (f' : StatusFlags) (fClob : FlagMask)
    (hkeep : ∀ r, r ∉ armScratch → Arm64.get sm' r = Arm64.get sm r)
    (hst : sm'.status = f')
    (hfOk : f' = sm.status ∨ fClob = maskNZCV ∨ fClob = maskAll)
    (hmem : sm'.dmem = sm.dmem) :
    arm64StateRel (sv.setFlags f') sm' ∧
    armMach.Frame armCondReads sm sm' armScratch [] fClob := by
  refine ⟨⟨fun r hr => (hkeep r hr).trans (hrel.1 r hr), hst, hmem.trans hrel.2.2⟩, ?_⟩
  rcases hfOk with heq | rfl | rfl
  · exact armFrame_status_eq hkeep (hst.trans heq)
  · exact armFrame_nzcv hkeep
  · exact armFrame_upd_regs hkeep (Or.inl rfl)

theorem evalUBFM_shl_subword {n : Nat} (hn : n = 8 ∨ n = 16) (x : BitVec 32) :
    evalUBFM (w := .W32) x n (n - 1) = (x.setWidth n).setWidth 32 <<< (32 - n) := by
  rcases hn with rfl | rfl <;>
    simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] <;>
    ext i hi <;> grind

theorem evalUBFM_shr_subword {n : Nat} (hn : n = 8 ∨ n = 16) (r : BitVec n) :
    evalUBFM (w := .W32) (r.setWidth 32 <<< (32 - n)) (32 - n) 31 = r.setWidth 32 := by
  rcases hn with rfl | rfl <;>
    simp only [evalUBFM, RegWidth.bits, MemWidth.bits, BitVec.take, BitVec.zeroExtend] <;>
    ext i hi <;> grind

theorem shl_subword_add {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    (a.setWidth 32 <<< (32 - n)) + (b.setWidth 32 <<< (32 - n)) =
      (a + b).setWidth 32 <<< (32 - n) := by
  rcases hn with rfl | rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_add, BitVec.toNat_shiftLeft] <;> omega

theorem shl_subword_sub {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    (a.setWidth 32 <<< (32 - n)) - (b.setWidth 32 <<< (32 - n)) =
      (a - b).setWidth 32 <<< (32 - n) := by
  rcases hn with rfl | rfl <;> apply BitVec.eq_of_toNat_eq <;>
    simp [BitVec.toNat_sub, BitVec.toNat_shiftLeft] <;> omega

theorem shl_subword_and {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    (a.setWidth 32 <<< (32 - n)) &&& (b.setWidth 32 <<< (32 - n)) =
      (a &&& b).setWidth 32 <<< (32 - n) := by
  rcases hn with rfl | rfl <;> ext i hi <;> grind

private theorem shl_subword_toNat {n : Nat} (hn : n = 8 ∨ n = 16) (a : BitVec n) :
    (a.setWidth 32 <<< (32 - n)).toNat = a.toNat * 2 ^ (32 - n) := by
  rcases hn with rfl | rfl <;> (simp [BitVec.toNat_shiftLeft]; omega)

private theorem shl_subword_toInt {n : Nat} (hn : n = 8 ∨ n = 16) (a : BitVec n) :
    (a.setWidth 32 <<< (32 - n)).toInt = a.toInt * (2 ^ (32 - n) : Int) := by
  have hnat := shl_subword_toNat hn a
  have h1 := BitVec.toInt_eq_toNat_cond (a.setWidth 32 <<< (32 - n))
  have h2 := BitVec.toInt_eq_toNat_cond a
  have ha := a.isLt
  rcases hn with rfl | rfl <;> (simp only [hnat] at h1; split at h1 <;> split at h2 <;> omega)

private theorem shl_subword_msb {n : Nat} (hn : n = 8 ∨ n = 16) (a : BitVec n) :
    (a.setWidth 32 <<< (32 - n)).msb = a.msb := by
  rcases hn with rfl | rfl <;> simp [BitVec.msb_eq_getLsbD_last]

private theorem shl_subword_eq_zero {n : Nat} (hn : n = 8 ∨ n = 16) (a : BitVec n) :
    (a.setWidth 32 <<< (32 - n) == BitVec.zero 32) = (a == BitVec.zero n) := by
  have hnat := shl_subword_toNat hn a
  cases ha : (a == BitVec.zero n)
  · have hne : a.toNat ≠ 0 := fun h => by
      have : a = BitVec.zero n := BitVec.eq_of_toNat_eq (by simpa [BitVec.zero] using h)
      simp [this] at ha
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have h0 := congrArg BitVec.toNat heq
    rw [hnat] at h0
    rcases hn with rfl | rfl <;> simp [BitVec.zero] at h0 <;> omega
  · have heq : a = BitVec.zero n := beq_iff_eq.mp ha
    subst heq; rcases hn with rfl | rfl <;> decide

theorem from_result_shl_subword {n : Nat} (hn : n = 8 ∨ n = 16) (a : BitVec n)
    (f : StatusFlags.from_result.Remaining) :
    StatusFlags.from_result (a.setWidth 32 <<< (32 - n)) f = StatusFlags.from_result a f := by
  simp only [StatusFlags.from_result, shl_subword_msb hn, shl_subword_eq_zero hn]

private theorem int_mul_bne_eq {k : Int} (hk : k > 0) (x y : Int) :
    (x * k != y * k) = (x != y) := by
  by_cases h : x = y
  · subst h; simp
  · have h' : x * k ≠ y * k := fun e => h (Int.eq_of_mul_eq_mul_right (by omega) e)
    simp only [bne, beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

private theorem int_mul_beq_eq {k : Int} (hk : k > 0) (x y : Int) :
    (x * k == y * k) = (x == y) := by
  by_cases h : x = y
  · subst h; simp
  · have h' : x * k ≠ y * k := fun e => h (Int.eq_of_mul_eq_mul_right (by omega) e)
    simp only [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

theorem adds_shl_subword {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    StatusFlags.adds ((a.setWidth 32 <<< (32 - n)) + (b.setWidth 32 <<< (32 - n)))
      (a.setWidth 32 <<< (32 - n)) (b.setWidth 32 <<< (32 - n)) =
    StatusFlags.adds (a + b) a b := by
  rw [shl_subword_add hn]
  simp only [StatusFlags.adds, from_result_shl_subword hn, BitVec.unsigned, BitVec.signed,
    shl_subword_toNat hn, shl_subword_toInt hn]
  congr 1; congr 1
  · push_cast
    rw [← Int.add_mul]
    exact int_mul_bne_eq (by rcases hn with rfl | rfl <;> decide) _ _
  · rw [← Int.add_mul]
    exact int_mul_bne_eq (by rcases hn with rfl | rfl <;> decide) _ _

theorem subs_shl_subword {n : Nat} (hn : n = 8 ∨ n = 16) (a b : BitVec n) :
    StatusFlags.subs ((a.setWidth 32 <<< (32 - n)) - (b.setWidth 32 <<< (32 - n)))
      (a.setWidth 32 <<< (32 - n)) (b.setWidth 32 <<< (32 - n)) =
    StatusFlags.subs (a - b) a b := by
  rw [shl_subword_sub hn]
  simp only [StatusFlags.subs, from_result_shl_subword hn, BitVec.unsigned, BitVec.signed,
    shl_subword_toNat hn, shl_subword_toInt hn]
  congr 1; congr 1
  · push_cast
    rw [← Int.sub_mul]
    exact int_mul_beq_eq (by rcases hn with rfl | rfl <;> decide) _ _
  · rw [← Int.sub_mul]
    exact int_mul_bne_eq (by rcases hn with rfl | rfl <;> decide) _ _

theorem setWidth_add_of_le {n w : Nat} (hle : n ≤ w) (x y : BitVec w) :
    (x + y).setWidth n = x.setWidth n + y.setWidth n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hle), Nat.add_mod]

theorem setWidth_and_of_le {n w : Nat} (x y : BitVec w) :
    (x &&& y).setWidth n = x.setWidth n &&& y.setWidth n := by ext i hi; simp

theorem setWidth_or_of_le {n w : Nat} (x y : BitVec w) :
    (x ||| y).setWidth n = x.setWidth n ||| y.setWidth n := by ext i hi; simp

theorem setWidth_xor_of_le {n w : Nat} (x y : BitVec w) :
    (x ^^^ y).setWidth n = x.setWidth n ^^^ y.setWidth n := by ext i hi; simp

theorem int64_ofInt_setWidth {w : RegWidth} (v : BitVec w.bits) :
    BitVec.ofInt w.bits (Int64.toInt (Int64.ofBitVec (v.setWidth 64))) = v := by
  rw [← Int64.toInt_toBitVec, Int64.toBitVec_ofBitVec]
  cases w with
  | W64 => simp
  | W32 =>
    have hpow : (2 ^ 32 : Nat) < 2 ^ 64 := by decide
    have hlt : v.toNat < 2 ^ 32 := v.isLt
    have hti : (v.setWidth 64).toInt = (v.toNat : Int) := by
      have hc := BitVec.toInt_eq_toNat_cond (v.setWidth 64)
      have hnat : (v.setWidth 64).toNat = v.toNat := by
        simp [Nat.mod_eq_of_lt (Nat.lt_trans hlt hpow)]
      rw [hnat] at hc; split at hc <;> omega
    rw [hti, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ubfm_low_w32_eq {n : Nat} (hn : n = 8 ∨ n = 16) (v : BitVec 64) :
    ((v.setWidth 32).setWidth n).setWidth 32 = (v.setWidth n).setWidth 32 := by
  rcases hn with rfl | rfl <;> rw [BitVec.setWidth_setWidth_of_le v (by decide)]

theorem sbfm_low_w32_eq {n : Nat} (hn : n = 8 ∨ n = 16) (v : BitVec 64) :
    ((v.setWidth 32).setWidth n).signExtend 32 = (v.setWidth n).signExtend 32 := by
  rcases hn with rfl | rfl <;> rw [BitVec.setWidth_setWidth_of_le v (by decide)]

/-! ## 3. Operand Materialization, Total `AddrArg`, Load/Store, and Direct Frame WP -/

theorem armSrcToX_wp [Host] (tmp : XReg) (r : Arm64.Reg) (hr : r ∉ armScratch) (s : MachineData) :
    let p := armSrcToXIns tmp r
    (∀ o, o ≠ tmp → (o = .X16 ∨ o = .X17) → p.2 ≠ o) ∧
    _root_.Program.wp (emitClean p.1)
      (fun s' => Arm64.get s' (.reg p.2) = Arm64.get s r ∧
        (∀ q, q ≠ .reg tmp → Arm64.get s' q = Arm64.get s q) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  cases r with
  | reg x =>
    have hx := xreg_ne_scratch_of_not_mem hr
    refine ⟨fun o _ ho => ?_, armWp_nil ⟨rfl, fun _ _ => rfl, rfl, rfl⟩⟩
    rcases ho with rfl | rfl
    · exact hx.1
    · exact hx.2
  | SP =>
    refine ⟨fun o ho _ => ho.symm, ?_⟩
    simp only [armSrcToXIns, emitClean_cons, emitClean_nil]
    refine armWp_mono (armMovToX_wp tmp .SP s) ?_
    rintro _ rfl
    exact ⟨get_wr_same s tmp _, fun q hq => get_wr_of_ne s tmp _ q hq, rfl, rfl⟩

theorem armRhsToX_wp [Host] (w : Width) (rhs : Src arm64Arch)
    (hrhs : ∀ r ∈ rhs.regs, r ∉ armScratch) (s : MachineData) :
    let p := armRhsToXIns .X17 w rhs
    p.2 ≠ .X16 ∧
    _root_.Program.wp (emitClean p.1)
      (fun s' => (Arm64.get s' (.reg p.2)).setWidth w.bits = rhs.evalW w (Arm64.get s) ∧
        (∀ q, q ≠ .reg .X17 → Arm64.get s' q = Arm64.get s q) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  cases rhs with
  | reg r =>
    have hr : r ∉ armScratch := hrhs r List.mem_cons_self
    cases r with
    | reg x =>
      exact ⟨(xreg_ne_scratch_of_not_mem hr).1, armWp_nil ⟨rfl, fun _ _ => rfl, rfl, rfl⟩⟩
    | SP =>
      refine ⟨by dsimp only [armRhsToXIns]; decide, ?_⟩
      simp only [armRhsToXIns, emitClean_cons, emitClean_nil]
      refine armWp_mono (armMovToX_wp .X17 .SP s) ?_
      rintro _ rfl
      exact ⟨by simp [Src.evalW, Src.eval], fun q hq => get_wr_of_ne s .X17 _ q hq, rfl, rfl⟩
  | imm v =>
    refine ⟨by dsimp only [armRhsToXIns]; decide, ?_⟩
    dsimp only [armRhsToXIns]
    refine armWp_mono (armMovImm_wp .X17 ((v.setWidth w.bits).setWidth 64) s) ?_
    rintro _ rfl
    have hle : w.bits ≤ 64 := by cases w <;> decide
    refine ⟨?_, fun q hq => get_wr_of_ne s .X17 _ q hq, rfl, rfl⟩
    rw [get_wr_same, BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq]; rfl

theorem armSetupAddrTotal_wp [Host] (scale : Nat) (a : AddrArg Arm64.Reg)
    (s : MachineData) (haregs : ∀ r ∈ a.regs, r ∉ armScratch) :
    let p := armSetupAddrTotalIns scale a
    (∃ rx, p.2.base = .low (.reg rx) .W64 ∧ rx ≠ .X17) ∧
    (match p.2.off with | .imm i => i.index = none | .reg er => er.reg.reg.base ≠ .reg .X17) ∧
    _root_.Program.wp (emitClean p.1)
      (fun s' =>
        (∀ [Labels] pos, p.2.eval s' pos = (a.eval (Arm64.get s), s')) ∧
        (∀ r, r ∉ armScratch → Arm64.get s' r = Arm64.get s r) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  dsimp only [armSetupAddrTotalIns]
  by_cases hva : armAddrValid scale a = true
  · simp only [hva, ↓reduceIte]
    have h := armSetupAddr_wp scale a s haregs hva
    have hbase : ∃ rx, (armSetupAddrIns scale a).2.base = .low (.reg rx) .W64 ∧ rx ≠ .X17 := by
      cases a with
      | imm _ => exact ⟨.X16, rfl, by decide⟩
      | baseDisp base disp =>
        cases base with
        | SP =>
          dsimp only [armSetupAddrIns]
          split
          · exact ⟨.X16, rfl, by decide⟩
          · split <;> exact ⟨.X16, rfl, by decide⟩
        | reg rb =>
          have hrb17 : rb ≠ .X17 :=
            (xreg_ne_scratch_of_not_mem (haregs (.reg rb) (by simp [AddrArg.regs]))).2
          dsimp only [armSetupAddrIns]
          split
          · exact ⟨rb, rfl, hrb17⟩
          · split <;> exact ⟨rb, rfl, hrb17⟩
      | baseIdxDisp base idx sc disp =>
        cases base with
        | SP => simp [armAddrValid] at hva
        | reg rb =>
          cases idx with
          | SP => simp [armAddrValid] at hva
          | reg ri =>
            have hrb17 : rb ≠ .X17 :=
              (xreg_ne_scratch_of_not_mem (haregs (.reg rb) (by simp [AddrArg.regs]))).2
            dsimp only [armSetupAddrIns, armSetupIdxDispIns]
            split
            · exact ⟨rb, rfl, hrb17⟩
            · split
              · exact ⟨.X16, rfl, by decide⟩
              · split <;> exact ⟨.X16, rfl, by decide⟩
    have hoff : match (armSetupAddrIns scale a).2.off with
        | .imm i => i.index = none | .reg er => er.reg.reg.base ≠ .reg .X17 := by
      generalize ho : (armSetupAddrIns scale a).2.off = o
      cases a with
      | imm _ => subst ho; rfl
      | baseDisp base disp =>
        cases base with
        | SP =>
          dsimp only [armSetupAddrIns] at ho
          split at ho
          · subst ho; rfl
          · split at ho <;> (subst ho; rfl)
        | reg rb =>
          dsimp only [armSetupAddrIns] at ho
          split at ho
          · subst ho; rfl
          · split at ho
            · subst ho; rfl
            · subst ho; dsimp only [armAtIdx]; decide
      | baseIdxDisp base idx sc disp =>
        cases base with
        | SP => simp [armAddrValid] at hva
        | reg rb =>
          cases idx with
          | SP => simp [armAddrValid] at hva
          | reg ri =>
            have hri17 : ri ≠ .X17 :=
              (xreg_ne_scratch_of_not_mem (haregs (.reg ri) (by simp [AddrArg.regs]))).2
            dsimp only [armSetupAddrIns, armSetupIdxDispIns] at ho
            split at ho
            · subst ho; intro e; exact hri17 (XRegOrXzr.reg.inj e)
            · split at ho
              · subst ho; rfl
              · split at ho
                · subst ho; intro e; exact hri17 (XRegOrXzr.reg.inj e)
                · subst ho; rfl
    refine ⟨hbase, hoff, armWp_mono h.2 ?_⟩
    rintro s' ⟨heval, hx, hsp, hdmem, hst, _⟩
    refine ⟨heval, fun r hr => ?_, hst, hdmem⟩
    cases r with
    | SP => simp [get_sp, hsp]
    | reg x => exact congrArg UInt64.toBitVec (hx x (xreg_ne_scratch_of_not_mem hr).1)
  · simp only [hva, Bool.false_eq_true, ↓reduceIte]
    cases a with
    | imm _ | baseDisp _ _ => simp [armAddrValid] at hva
    | baseIdxDisp base idx sc disp =>
      have hrbOk : base ∉ armScratch := haregs base (by simp [AddrArg.regs])
      have hriOk : idx ∉ armScratch := haregs idx (by simp [AddrArg.regs])
      refine ⟨⟨.X16, rfl, by decide⟩, rfl, ?_⟩
      simp only [emitClean_append, emitClean_cons,
        List.append_assoc, List.cons_append, List.nil_append]
      have h1 := armSrcToX_wp .X16 base hrbOk s
      refine armWp_append h1.2 ?_
      rintro s₁ ⟨hrb1, hk1, hst1, hd1⟩
      have h2 := armSrcToX_wp .X17 idx hriOk s₁
      refine armWp_append h2.2 ?_
      rintro s₂ ⟨hri2, hk2, hst2, hd2⟩
      have hrbNe17 : (armSrcToXIns .X16 base).2 ≠ .X17 := h1.1 .X17 (by decide) (Or.inr rfl)
      have hrb2 : Arm64.get s₂ (.reg (armSrcToXIns .X16 base).2) = Arm64.get s base := by
        rw [hk2 _ (fun e => hrbNe17 (XRegOrSp.reg.inj e)), hrb1]
      have hri2' : Arm64.get s₂ (.reg (armSrcToXIns .X17 idx).2) = Arm64.get s idx := by
        rw [hri2, hk1 idx (fun e => hriOk (by simp [e, armScratch]))]
      have haddIdx : _root_.Program.wp
          [ins (.ADD_s (zr .X16 .W64) (zr (armSrcToXIns .X16 base).2 .W64)
            { reg := zr (armSrcToXIns .X17 idx).2 .W64,
              amount := Int64.ofNat sc.shift, shift := .LSL })]
          (fun s' => s' = wr s₂ .X16 (Arm64.get s base + (Arm64.get s idx <<< sc.shift)))
          (fun _ _ => False) s₂ :=
        armDirFallsTo_wp fun {_} pos _ _ _ hk => by
          simp only [t_step_simp, RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq]
          rw [show (Int64.ofNat sc.shift).toInt.toNat = sc.shift by cases sc <;> decide,
            ← get_reg, ← get_reg, hrb2, hri2']
          exact hk _ rfl
      refine armWp_cons haddIdx ?_
      rintro _ rfl
      have hkeep3 : ∀ r, r ∉ armScratch → Arm64.get (wr s₂ .X16
          (Arm64.get s base + (Arm64.get s idx <<< sc.shift))) r = Arm64.get s r := by
        intro r hr
        have hns := ne_of_not_mem_armScratch hr
        rw [get_wr_of_ne _ _ _ _ hns.1, hk2 r hns.2, hk1 r hns.1]
      split
      · rename_i hd0
        have hdisp0 : disp.toBitVec = 0#64 := by have := beq_iff_eq.mp hd0; subst this; rfl
        refine armWp_nil ⟨fun {_} pos => ?_, hkeep3, hst2.trans hst1, hd2.trans hd1⟩
        simp only [AddrExpr.eval, ConstExpr.interp, Int64.toInt_zero, Reg64s.getRegOrSp_reg64,
          BitVec.signed, Int.add_zero, BitVec.ofInt_toInt, Reg64s.getXReg_setXReg_same,
          UInt64.toBitVec_ofBitVec, AddrArg.eval, hdisp0, BitVec.add_zero]
      · rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append (armMovImm_wp .X17 disp.toBitVec _) ?_
        rintro _ rfl
        refine armWp_mono (armDirFallsTo_wp
          (Q := fun s' => s' = wr (wr (wr s₂ .X16
              (Arm64.get s base + (Arm64.get s idx <<< sc.shift))) .X17 disp.toBitVec) .X16
            (Arm64.get s base + (Arm64.get s idx <<< sc.shift) + disp.toBitVec))
          fun {_} pos _ _ _ hk => by
            dsimp only [sh]
            simp only [t_step_simp, Int64.toInt_zero, Int.toNat_zero, BitVec.shiftLeft_zero,
              RegWidth.bits, MemWidth.bits, BitVec.setWidth_eq, Reg64s.getXReg_setXReg_same,
              Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X17 ≠ XReg.X16),
              UInt64.toBitVec_ofBitVec]
            exact hk _ rfl) ?_
        rintro _ rfl
        refine ⟨fun {_} pos => ?_, fun r hr => ?_, hst2.trans hst1, hd2.trans hd1⟩
        · simp only [AddrExpr.eval, ConstExpr.interp, Int64.toInt_zero, Reg64s.getRegOrSp_reg64,
            BitVec.signed, Int.add_zero, BitVec.ofInt_toInt, Reg64s.getXReg_setXReg_same,
            UInt64.toBitVec_ofBitVec, AddrArg.eval]
        · have hns := ne_of_not_mem_armScratch hr
          rw [get_wr_of_ne _ _ _ _ hns.1, get_wr_of_ne _ _ _ _ hns.2]
          exact hkeep3 r hr

theorem addrExpr_eval_wr_x17 [Labels] {addr : AddrExpr} {rx : XReg} {a : BitVec 64}
    {s : MachineData} (hbase : addr.base = .low (.reg rx) .W64) (hrx17 : rx ≠ .X17)
    (hoff : match addr.off with | .imm i => i.index = none | .reg er => er.reg.reg.base ≠ .reg .X17)
    (heval : ∀ [Labels] pos, addr.eval s pos = (a, s)) (v : BitVec 64) (pos : Std.Rco Int64) :
    addr.eval (wr s .X17 v) pos = (a, wr s .X17 v) := by
  have h1 := heval pos
  cases addr with
  | mk base off =>
    dsimp only at hbase hoff
    subst hbase
    cases off with
    | imm i =>
      simp only [AddrExpr.eval, hoff, Reg64s.getRegOrSp_reg64,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrx17.symm] at h1 ⊢
      have hfst : BitVec.ofInt 64 ((s.regs.getXReg rx).toBitVec.signed +
          Int64.toInt (i.imm.interp pos)) = a := congrArg Prod.fst h1
      rw [hfst]
    | reg er =>
      simp only [AddrExpr.eval, MemExtRegExpr.interp, Reg64s.getRegOrSp_reg64,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hrx17.symm] at h1 ⊢
      have hregEq : (wr s .X17 v).regs.getRegOrZr64 er.reg.reg.base =
          s.regs.getRegOrZr64 er.reg.reg.base := by
        cases hrb : er.reg.reg.base with
        | XZR => rfl
        | reg x =>
          have hx : x ≠ .X17 := fun e => hoff (by rw [hrb, e])
          simp [Reg64s.getRegOrZr64, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm]
      have hfst : BitVec.ofInt 64 ((s.regs.getXReg rx).toBitVec.signed +
          (s.regs.getRegOrZr64 er.reg.reg.base).apply_mem_extend er.ext) = a :=
        congrArg Prod.fst h1
      rw [hregEq, hfst]

theorem asmLoadDir_wp [Host] (w : Width) (ext : LoadExt) (d : XReg) (addr : AddrExpr)
    (a : BitVec 64) (v : BitVec w.bits) (s : MachineData)
    (hnoSp : ∃ rx, addr.base = .low (.reg rx) .W64)
    (heval : ∀ [Labels] pos, addr.eval s pos = (a, s))
    (hload : loadVal s.dmem w.toTy a = some v) :
    _root_.Program.wp [.instr (asmLoadDirI w ext d addr)]
      (fun s' => s' = wr s d (ext.apply arm64Arch w (Arm64.get s (.reg d)) v))
      (fun _ _ => False) s := by
  obtain ⟨rx, hrx⟩ := hnoSp
  simp only [loadVal, Option.bind_eq_some_iff] at hload
  rcases hload with ⟨i, hi, hv⟩
  cases ext <;> cases w <;> (
    simp only [Width.toTy, Width.bits, Ty.bytes, Ty.size, Nat.reduceAdd, Nat.reduceDiv,
      ofBits, Option.some.injEq] at hi hv
    subst hv
    refine armDirFallsTo_wp fun {_} pos _ _ _ hk => by
      dsimp only [asmLoadDirI]
      simp only [Directive.interp, Instr.interp, Operation.interp]
      try simp only [AddrOrLit.interpLoad]
      simp only [AddrExpr.interpLoad, AddrExpr.checkSPAlignment, hrx, heval pos,
        MachineData.load, MemWidth.bytes, Effects.All]
      rw [hi]
      simp only [MachineData.setRegOrZr, setRegOrZr_zr, MemWidth.bits]
      refine hk _ ?_
      simp only [LoadExt.apply, writeSubZeroExtend, Width.bits, BitVec.zeroExtend,
        BitVec.signExtend_eq, BitVec.setWidth_eq]
      try rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
      try rfl)

theorem asmStoreDir_wp [Host] (w : Width) (rx : XReg) (addr : AddrExpr) (a : BitVec 64)
    (s : MachineData) (hnoSp : ∃ r, addr.base = .low (.reg r) .W64)
    (heval : ∀ [Labels] pos, addr.eval s pos = (a, s))
    (hok : storeOk s.dmem w.toTy a) :
    _root_.Program.wp [.instr (asmStoreDirI w rx addr)]
      (fun s' => s' = { s with
        dmem := storeMem s.dmem w.toTy a ((Arm64.get s (.reg rx)).setWidth w.bits) })
      (fun _ _ => False) s := by
  obtain ⟨r, hr⟩ := hnoSp
  rcases hok with ⟨i, hi⟩
  have htake : ∀ {k : Nat}, k ≤ 32 →
      ((s.regs.getXReg rx).toBitVec.setWidth 32).take k = (s.regs.getXReg rx).toBitVec.setWidth k :=
    fun hk => by ext j hj; simp [BitVec.take, show (j : Nat) < 32 by omega]
  cases w <;> (
    simp only [Width.bits, Ty.bytes, Ty.size, Nat.reduceAdd, Nat.reduceDiv] at hi
    refine armDirFallsTo_wp fun {_} pos _ _ _ hk => by
      dsimp only [asmStoreDirI]
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
        AddrExpr.checkSPAlignment, hr, heval pos, MachineData.store, MemWidth.bytes,
        getRegOrZr_zr, RegWidth.bits, Effects.All]
      rw [hi]
      refine hk _ ?_
      simp only [storeMem, Width.toTy, Width.bits, Ty.bytes, Ty.size, toBits, get_reg]
      try rw [htake (by decide)]
      try rw [BitVec.setWidth_eq]
      try rfl)

theorem armSpOp_wp_direct [Host] (isSub : Bool) (n : Nat) (s : MachineData) :
    _root_.Program.wp (if isSub then armSubSp n else armAddSp n)
      (fun s' => s'.regs.SP = UInt64.ofBitVec
          (if isSub then Arm64.get s .SP - BitVec.ofNat 64 n
           else Arm64.get s .SP + BitVec.ofNat 64 n) ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  cases isSub <;> (
    simp only [↓reduceIte, Bool.false_eq_true, armSubSp, armSubSpIns, armAddSp, armAddSpIns,
      emitClean_ite]
    split
    · refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits]
        rw [ofInt_toInt_ofNat]; exact hk _ rfl) ?_
      rintro _ rfl; exact ⟨rfl, fun _ _ => rfl, rfl, rfl⟩
    · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 n) s) ?_
      rintro _ rfl
      refine armWp_mono (armDirFallsTo_wp fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, Reg64s.setRegOrSp_sp64, Reg64s.getRegOrSp_sp64, RegWidth.bits,
          ExtRegExpr.interp, BitVec.apply_extend, BitVec.unsigned, Reg64s.getRegOrZr64,
          RegOrZr.base]
        rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]; exact hk _ rfl) ?_
      rintro _ rfl
      refine ⟨by simp [get_sp], fun x hx => ?_, rfl, rfl⟩
      dsimp only; rw [Reg64s_getXReg_setSP, Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm])

theorem armStSpXReg_wp_direct [Host] (r : XReg) (o : Nat) (s : MachineData)
    (hr : r ≠ .X16) (hal : (Arm64.get s .SP).toNat % 16 = 0)
    (hok : storeOk s.dmem i64 (Arm64.get s .SP + BitVec.ofNat 64 o)) :
    _root_.Program.wp (armStSpXReg r o)
      (fun s' => s'.regs.SP = s.regs.SP ∧
        (∀ x, x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧
        s'.dmem = storeMem s.dmem i64 (Arm64.get s .SP + BitVec.ofNat 64 o)
          (Arm64.get s (.reg r)))
      (fun _ _ => False) s := by
  rcases hok with ⟨i, hi⟩
  have hi' : Mem.loadInt s.dmem (Arm64.get s .SP + BitVec.ofNat 64 o) 8 = some i := hi
  dsimp only [armStSpXReg, armStSpXRegIns]
  simp only [emitClean_ite]
  split
  · refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
        AddrExpr.checkSPAlignment, armCheckSP_eq_false s hal, Bool.false_eq_true, ↓reduceIte,
        armAtSp_eval, ← get_sp, MachineData.store, MemWidth.bytes, Effects.All]
      rw [hi']
      simp only [getRegOrZr_zr, RegWidth.bits, BitVec.setWidth_eq]
      exact hk _ ⟨rfl, fun _ _ => rfl, rfl, rfl⟩) (fun _ h => h)
  · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 o) s) ?_
    rintro _ rfl
    have hsp16 : (Arm64.get (wr s .X16 (BitVec.ofNat 64 o)) .SP).toNat % 16 = 0 := by
      simpa [get_sp] using hal
    refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrExpr.interpStore,
        AddrExpr.checkSPAlignment, armCheckSP_eq_false (wr s .X16 (BitVec.ofNat 64 o)) hsp16,
        Bool.false_eq_true, ↓reduceIte, armAtSpIdx_eval, Reg64s.SP_setXReg,
        Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, ← get_sp, MachineData.store,
        MemWidth.bytes, dmem_wr, Effects.All]
      rw [hi']
      simp only [getRegOrZr_zr, RegWidth.bits, BitVec.setWidth_eq,
        Reg64s.getXReg_setXReg_of_ne _ _ _ _ hr.symm]
      exact hk _ ⟨rfl, fun x hx => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl, rfl⟩)
      (fun _ h => h)

theorem armLdSpXReg_wp_direct [Host] (rd : XReg) (o : Nat) (v : BitVec 64)
    (s : MachineData) (hal : (Arm64.get s .SP).toNat % 16 = 0)
    (hld : loadVal s.dmem i64 (Arm64.get s .SP + BitVec.ofNat 64 o) = some v) :
    _root_.Program.wp (armLdSpXReg rd o)
      (fun s' => s'.regs.SP = s.regs.SP ∧ s'.regs.getXReg rd = UInt64.ofBitVec v ∧
        (∀ x, x ≠ rd → x ≠ .X16 → s'.regs.getXReg x = s.regs.getXReg x) ∧
        s'.status = s.status ∧ s'.dmem = s.dmem)
      (fun _ _ => False) s := by
  simp only [loadVal, Option.bind_eq_some_iff, ofBits, Option.some.injEq] at hld
  rcases hld with ⟨i, hi, rfl⟩
  have hi' : Mem.loadInt s.dmem (Arm64.get s .SP + BitVec.ofNat 64 o) 8 = some i := hi
  dsimp only [armLdSpXReg, armLdSpXRegIns]
  simp only [emitClean_ite]
  split
  · refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrOrLit.interpLoad,
        AddrExpr.interpLoad, AddrExpr.checkSPAlignment, armCheckSP_eq_false s hal,
        Bool.false_eq_true, ↓reduceIte, armAtSp_eval, ← get_sp, MachineData.load,
        MemWidth.bytes, Effects.All]
      rw [hi']
      simp only [MachineData.setRegOrZr, setRegOrZr_zr, MemWidth.bits, BitVec.setWidth_eq]
      exact hk _ rfl) ?_
    rintro _ rfl
    exact ⟨Reg64s.SP_setXReg _ _ _, Reg64s.getXReg_setXReg_same _ _ _,
      fun _ hx _ => Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx.symm, rfl, rfl⟩
  · refine armWp_cons (armLdrPoolBv_wp .X16 (BitVec.ofNat 64 o) s) ?_
    rintro _ rfl
    have hsp16 : (Arm64.get (wr s .X16 (BitVec.ofNat 64 o)) .SP).toNat % 16 = 0 := by
      simpa [get_sp] using hal
    refine armWp_mono (armDirFallsTo_wp fun {_} pos _ _ _ hk => by
      simp only [Directive.interp, Instr.interp, Operation.interp, AddrOrLit.interpLoad,
        AddrExpr.interpLoad, AddrExpr.checkSPAlignment,
        armCheckSP_eq_false (wr s .X16 (BitVec.ofNat 64 o)) hsp16, Bool.false_eq_true, ↓reduceIte,
        armAtSpIdx_eval, Reg64s.SP_setXReg, Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
        ← get_sp, MachineData.load, MemWidth.bytes, dmem_wr, Effects.All]
      rw [hi']
      simp only [MachineData.setRegOrZr, setRegOrZr_zr, MemWidth.bits, BitVec.setWidth_eq]
      exact hk _ rfl) ?_
    rintro _ rfl
    refine ⟨by simp, Reg64s.getXReg_setXReg_same _ _ _, fun x hxrd hx16 => ?_, rfl, rfl⟩
    rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hxrd.symm,
      Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx16.symm]

/-! ## 4. Generic `.native d` State-Agreement Simulation -/

private def AgreeNonScratch (s₁ s₂ : MachineData) : Prop :=
  (∀ r : Arm64.Reg, r ∉ armScratch → Arm64.get s₁ r = Arm64.get s₂ r) ∧
  s₁.status = s₂.status ∧ s₁.dmem = s₂.dmem

private theorem agreeNonScratch_of_stateRel {sv : MachSt arm64Arch} {sm : MachineData}
    (h : arm64StateRel sv sm) : AgreeNonScratch (vllToMachData sv) sm :=
  ⟨fun r hr => (get_vllToMachData sv r).trans (h.1 r hr).symm, h.2.1.symm, h.2.2.symm⟩

private theorem stateRel_of_agreeNonScratch {sv_m sm : MachineData}
    (h : AgreeNonScratch sv_m sm) : arm64StateRel (machDataToVll sv_m) sm :=
  ⟨fun r hr => (h.1 r hr).symm, h.2.1.symm, h.2.2.symm⟩

private theorem agree_getZr {w : RegWidth} {s₁ s₂ : MachineData} (ha : AgreeNonScratch s₁ s₂)
    (r : RegOrZr w) (hr : ∀ q ∈ regOfZr r, q ∉ armScratch) :
    s₁.regs.getRegOrZr r = s₂.regs.getRegOrZr r := by
  cases r with
  | low xr w' =>
    cases xr with
    | XZR => rfl
    | reg x =>
      have h := ha.1 (.reg x) (hr (.reg x) List.mem_cons_self)
      simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, ← get_reg, h]

private theorem agree_getSp {w : RegWidth} {s₁ s₂ : MachineData} (ha : AgreeNonScratch s₁ s₂)
    (r : RegOrSp w) (hr : ∀ q ∈ regOfSp r, q ∉ armScratch) :
    s₁.regs.getRegOrSp r = s₂.regs.getRegOrSp r := by
  have h := ha.1 r.base (hr r.base List.mem_cons_self)
  dsimp only [Arm64.get] at h
  simp only [Reg64s.getRegOrSp, h]

private theorem agree_setZr {w : RegWidth} {s₁ s₂ : MachineData} (ha : AgreeNonScratch s₁ s₂)
    (dst : RegOrZr w) (v : w.type) :
    AgreeNonScratch { s₁ with regs := s₁.regs.setRegOrZr dst v }
      { s₂ with regs := s₂.regs.setRegOrZr dst v } := by
  refine ⟨fun r hr => ?_, ha.2.1, ha.2.2⟩
  cases dst with
  | low xr _ =>
    cases xr with
    | XZR => cases w <;> exact ha.1 r hr
    | reg xd =>
      by_cases heq : r = .reg xd
      · subst heq; cases w <;>
          simp [Arm64.get, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrSp64]
      · cases w <;> (
          dsimp only [Reg64s.setRegOrZr, Reg64s.setRegOrZr64]
          change Arm64.get (wr s₁ xd _) r = Arm64.get (wr s₂ xd _) r
          rw [get_wr_of_ne _ _ _ r heq, get_wr_of_ne _ _ _ r heq]
          exact ha.1 r hr)

private theorem agree_setSp {w : RegWidth} {s₁ s₂ : MachineData} (ha : AgreeNonScratch s₁ s₂)
    (dst : RegOrSp w) (v : w.type) :
    AgreeNonScratch { s₁ with regs := s₁.regs.setRegOrSp dst v }
      { s₂ with regs := s₂.regs.setRegOrSp dst v } := by
  refine ⟨fun r hr => ?_, ha.2.1, ha.2.2⟩
  cases dst with
  | low xs _ =>
    by_cases heq : r = xs
    · subst heq; cases r <;> cases w <;>
        simp [Arm64.get, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64]
    · cases xs with
      | SP =>
        cases r with
        | SP => exact absurd rfl heq
        | reg xr =>
          cases w <;> (
            simp only [Arm64.get, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64,
              Reg64s_getXReg_setSP]
            exact ha.1 (.reg xr) hr)
      | reg xd =>
        cases w <;> (
          dsimp only [Reg64s.setRegOrSp, Reg64s.setRegOrSp64]
          change Arm64.get (wr s₁ xd _) r = Arm64.get (wr s₂ xd _) r
          rw [get_wr_of_ne _ _ _ r heq, get_wr_of_ne _ _ _ r heq]
          exact ha.1 r hr)

private theorem agree_extOrImm [Labels] {w : RegWidth} {s₁ s₂ : MachineData}
    (ha : AgreeNonScratch s₁ s₂) (e : ExtOrImmReg) (he : ∀ r ∈ extOrImmUses e, r ∉ armScratch)
    (p : Std.Rco Int64) : e.interp (w := w) s₁.regs p = e.interp (w := w) s₂.regs p := by
  cases e with
  | imm _ => rfl
  | ext er =>
    simp only [ExtOrImmReg.interp, ExtRegExpr.interp]
    cases hb : er.reg.reg.base with
    | XZR => simp [Reg64s.getRegOrZr64]
    | reg x =>
      have h := ha.1 (.reg x) (he (.reg x) (by simp [extOrImmUses, hb, regOfXzr]))
      simp [Reg64s.getRegOrZr64, ← get_reg, h]

private theorem agree_shiftReg {w : RegWidth} {s₁ s₂ : MachineData}
    (ha : AgreeNonScratch s₁ s₂) (sr : ShiftRegExpr w)
    (hsr : ∀ r ∈ shiftRegUses sr, r ∉ armScratch) (p : Std.Rco Int64) :
    sr.interp s₁.regs p = sr.interp s₂.regs p := by
  simp only [ShiftRegExpr.interp, agree_getZr ha sr.reg hsr]

private theorem agree_addrEval [Labels] {s₁ s₂ : MachineData} (ha : AgreeNonScratch s₁ s₂)
    (a : AddrExpr) (huse : ∀ r ∈ addrExprUses a, r ∉ armScratch) (p : Std.Rco Int64) :
    (a.eval s₁ p).1 = (a.eval s₂ p).1 ∧ AgreeNonScratch (a.eval s₁ p).2 (a.eval s₂ p).2 := by
  have hb : s₁.regs.getRegOrSp a.base = s₂.regs.getRegOrSp a.base :=
    agree_getSp ha a.base fun q hq => huse q (by
      simp only [regOfSp, List.mem_singleton] at hq; subst hq; exact List.mem_cons_self)
  cases a with
  | mk base off =>
    cases off with
    | reg er =>
      have hidx : s₁.regs.getRegOrZr64 er.reg.reg.base = s₂.regs.getRegOrZr64 er.reg.reg.base := by
        cases hrb : er.reg.reg.base with
        | XZR => rfl
        | reg x =>
          have h := ha.1 (.reg x) (huse (.reg x) (by simp [addrExprUses, hrb, regOfXzr]))
          simpa [Reg64s.getRegOrZr64, ← get_reg] using h
      simp only [AddrExpr.eval, MemExtRegExpr.interp, hb, hidx]
      exact ⟨trivial, ha⟩
    | imm i =>
      cases hi : i.index with
      | none => simp only [AddrExpr.eval, hi, hb]; exact ⟨trivial, ha⟩
      | some idx => simp only [AddrExpr.eval, hi, hb]; exact ⟨trivial, agree_setSp ha base _⟩

private theorem agree_frame_addrEval [Labels] (a : AddrExpr) (s : MachineData) (p : Std.Rco Int64)
    {gClob : List Arm64.Reg} (hsub : ∀ r ∈ addrExprClob a, r ∈ gClob) :
    armMach.Frame armCondReads s (a.eval s p).2 gClob [] maskNone := by
  cases a with
  | mk base off =>
    cases off with
    | reg _ => exact Machine.Frame.refl (M := armMach) armCondReads s gClob [] maskNone
    | imm i =>
      cases hi : i.index with
      | none =>
        simp only [AddrExpr.eval, hi]
        exact Machine.Frame.refl (M := armMach) armCondReads s gClob [] maskNone
      | some _ =>
        simp only [AddrExpr.eval, hi]
        refine armFrame_status_eq (fun r hr => ?_) rfl
        have hne : r ≠ base.base := fun e => hr (hsub r (by simp [addrExprClob, hi, e]))
        cases base with
        | low xs _ =>
          cases xs with
          | SP =>
            cases r with | SP => exact absurd rfl hne | reg xr =>
              simp [get_reg, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s_getXReg_setSP]
          | reg xd => exact get_wr_of_ne s xd _ r hne

private theorem agree_frame_setZr {w : RegWidth} (dst : RegOrZr w) (v : w.type)
    (s : MachineData) {gClob : List Arm64.Reg} (hsub : ∀ r ∈ regOfZr dst, r ∈ gClob) :
    armMach.Frame armCondReads s { s with regs := s.regs.setRegOrZr dst v } gClob [] maskNone := by
  refine armFrame_status_eq (fun r hr => ?_) rfl
  cases dst with
  | low xr _ =>
    cases xr with
    | XZR => cases w <;> rfl
    | reg xd =>
      have hne : r ≠ .reg xd := fun e => hr (hsub r (e ▸ List.mem_cons_self))
      cases w <;> exact get_wr_of_ne s xd _ r hne

private theorem agree_frame_setZr_nzcv {w : RegWidth} (dst : RegOrZr w) (v : w.type)
    (st : StatusFlags) (s : MachineData) {gClob : List Arm64.Reg}
    (hsub : ∀ r ∈ regOfZr dst, r ∈ gClob) :
    armMach.Frame armCondReads s
      { regs := s.regs.setRegOrZr dst v, status := st, dmem := s.dmem } gClob [] maskNZCV := by
  refine armFrame_nzcv fun r hr => ?_
  cases dst with
  | low xr _ =>
    cases xr with
    | XZR => cases w <;> rfl
    | reg xd =>
      have hne : r ≠ .reg xd := fun e => hr (hsub r (e ▸ List.mem_cons_self))
      cases w <;> exact get_wr_of_ne s xd _ r hne

private theorem agree_frame_setSp {w : RegWidth} (dst : RegOrSp w) (v : w.type)
    (s : MachineData) {gClob : List Arm64.Reg} (hsub : ∀ r ∈ regOfSp dst, r ∈ gClob) :
    armMach.Frame armCondReads s { s with regs := s.regs.setRegOrSp dst v } gClob [] maskNone := by
  refine armFrame_status_eq (fun r hr => ?_) rfl
  cases dst with
  | low xs _ =>
    have hne : r ≠ xs := fun e => hr (hsub r (e ▸ List.mem_cons_self))
    cases xs with
    | SP =>
      cases r with | SP => exact absurd rfl hne | reg xr =>
        cases w <;> simp [get_reg, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, Reg64s_getXReg_setSP]
    | reg xd => cases w <;> exact get_wr_of_ne s xd _ r hne

private theorem agree_checkSP {a : AddrExpr} {s₁ s₂ : MachineData} (ha : AgreeNonScratch s₁ s₂)
    {ok₁ ok₂ : Unit → Effects} {P₁ P₂ : MachineState → Prop}
    (h : (a.checkSPAlignment s₁ ok₁).All P₁) (hk : (ok₁ ()).All P₁ → (ok₂ ()).All P₂) :
    (a.checkSPAlignment s₂ ok₂).All P₂ := by
  have hsp : s₁.regs.getRegOrSp RegOrSp.SP = s₂.regs.getRegOrSp RegOrSp.SP :=
    agree_getSp ha RegOrSp.SP (by simp [regOfSp, RegOrSp.base, armScratch])
  dsimp only [AddrExpr.checkSPAlignment] at h ⊢
  cases hbase : a.base with
  | low xs _ =>
    simp only [hbase] at h ⊢
    cases xs with
    | reg _ => exact hk h
    | SP =>
      dsimp only at h ⊢
      rw [← hsp]
      split
      · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; cases h
      · rename_i hc; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; exact hk h

private theorem agree_uCheckSP {a : UnscaledAddrExpr} {s₁ s₂ : MachineData}
    (ha : AgreeNonScratch s₁ s₂) {ok₁ ok₂ : Unit → Effects} {P₁ P₂ : MachineState → Prop}
    (h : (a.checkSPAlignment s₁ ok₁).All P₁) (hk : (ok₁ ()).All P₁ → (ok₂ ()).All P₂) :
    (a.checkSPAlignment s₂ ok₂).All P₂ := by
  have hsp : s₁.regs.getRegOrSp RegOrSp.SP = s₂.regs.getRegOrSp RegOrSp.SP :=
    agree_getSp ha RegOrSp.SP (by simp [regOfSp, RegOrSp.base, armScratch])
  dsimp only [UnscaledAddrExpr.checkSPAlignment] at h ⊢
  cases hbase : a.base with
  | low xs _ =>
    simp only [hbase] at h ⊢
    cases xs with
    | reg _ => exact hk h
    | SP =>
      dsimp only at h ⊢
      rw [← hsp]
      split
      · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; cases h
      · rename_i hc; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; exact hk h

private theorem agree_load {s₁ s₂ : MachineData} {addr : BitVec 64} {w : MemWidth}
    (hmem : s₁.dmem = s₂.dmem) {ret₁ ret₂ : w.type → MachineData → Effects}
    {P₁ P₂ : MachineState → Prop}
    (h : (s₁.load addr w ret₁).All P₁)
    (hk : ∀ v, (ret₁ v s₁).All P₁ → (ret₂ v s₂).All P₂) :
    (s₂.load addr w ret₂).All P₂ := by
  dsimp only [MachineData.load, Effects.All] at h ⊢
  rw [← hmem]
  cases hm : Mem.loadInt s₁.dmem addr w.bytes with
  | none => rw [hm] at h; cases h
  | some i => rw [hm] at h; exact hk _ h

private theorem agree_store {s₁ s₂ : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    (ha : AgreeNonScratch s₁ s₂) {ret₁ ret₂ : MachineData → Effects}
    {P₁ P₂ : MachineState → Prop}
    (h : (s₁.store addr v ret₁).All P₁)
    (hk : ∀ m', AgreeNonScratch { s₁ with dmem := m' } { s₂ with dmem := m' } →
      (ret₁ { s₁ with dmem := m' }).All P₁ → (ret₂ { s₂ with dmem := m' }).All P₂) :
    (s₂.store addr v ret₂).All P₂ := by
  dsimp only [MachineData.store, Effects.All] at h ⊢
  rw [← ha.2.2]
  cases hm : Mem.loadInt s₁.dmem addr w.bytes with
  | none => rw [hm] at h; cases h
  | some _ => rw [hm] at h; exact hk _ ⟨ha.1, ha.2.1, rfl⟩ h

private theorem agree_addrLoad [Labels] {s₁ s₂ : MachineData} {a : AddrExpr} {w : MemWidth}
    {p : Std.Rco Int64} {gClob : List Arm64.Reg}
    (ha : AgreeNonScratch s₁ s₂) (huse : ∀ r ∈ addrExprUses a, r ∉ armScratch)
    (hclob : ∀ r ∈ addrExprClob a, r ∈ gClob)
    {ret₁ ret₂ : w.type → MachineData → Effects} {P₁ P₂ : MachineState → Prop}
    (h : (a.interpLoad (w := w) s₁ p ret₁).All P₁)
    (hk : ∀ v s₁' s₂', AgreeNonScratch s₁' s₂' →
      armMach.Frame armCondReads s₂ s₂' gClob [] maskNone →
      (ret₁ v s₁').All P₁ → (ret₂ v s₂').All P₂) :
    (a.interpLoad (w := w) s₂ p ret₂).All P₂ := by
  dsimp only [AddrExpr.interpLoad] at h ⊢
  refine agree_checkSP ha h fun h1 => ?_
  have ⟨haddr, hst⟩ := agree_addrEval ha a huse p
  rw [← haddr]
  exact agree_load hst.2.2 h1 fun v hv =>
    hk v (a.eval s₁ p).2 (a.eval s₂ p).2 hst (agree_frame_addrEval a s₂ p hclob) hv

private theorem agree_aolLoad [Labels] {s₁ s₂ : MachineData} {a : AddrOrLit} {w : MemWidth}
    {p : Std.Rco Int64} {gClob : List Arm64.Reg}
    (ha : AgreeNonScratch s₁ s₂) (huse : ∀ r ∈ addrOrLitUses a, r ∉ armScratch)
    (hclob : ∀ r ∈ addrOrLitClob a, r ∈ gClob)
    {ret₁ ret₂ : w.type → MachineData → Effects} {P₁ P₂ : MachineState → Prop}
    (h : (a.interpLoad (w := w) s₁ p ret₁).All P₁)
    (hk : ∀ v s₁' s₂', AgreeNonScratch s₁' s₂' →
      armMach.Frame armCondReads s₂ s₂' gClob [] maskNone →
      (ret₁ v s₁').All P₁ → (ret₂ v s₂').All P₂) :
    (a.interpLoad (w := w) s₂ p ret₂).All P₂ := by
  cases a with
  | addr ae => exact agree_addrLoad ha huse hclob h hk
  | lit lit =>
    cases lit with
    | addr _ =>
      exact agree_load ha.2.2 h fun v hv =>
        hk v s₁ s₂ ha (Machine.Frame.refl (M := armMach) armCondReads s₂ gClob [] maskNone) hv
    | pool _ =>
      exact hk _ s₁ s₂ ha (Machine.Frame.refl (M := armMach) armCondReads s₂ gClob [] maskNone) h

private theorem op_interp_agree [Labels] {w : RegWidth} (op : Operation w)
    (s₁ s₂ : MachineData) (p : Std.Rco Int64)
    (next₁ next₂ : MachineData → Effects) (jmp₁ jmp₂ : Int64 → MachineData → Effects)
    (P₁ P₂ : MachineState → Prop) (ha : AgreeNonScratch s₁ s₂)
    (huse : ∀ r ∈ (opNativeEffect op).gUses, r ∉ armScratch)
    (hnext : ∀ s₁' s₂', AgreeNonScratch s₁' s₂' →
      armMach.Frame armCondReads s₂ s₂' ((opNativeEffect op).gClob ++ armScratch) []
        (opNativeEffect op).fClob →
      (next₁ s₁').All P₁ → (next₂ s₂').All P₂)
    (hjmp : ∀ a s₁' s₂', AgreeNonScratch s₁' s₂' →
      armMach.Frame armCondReads s₂ s₂' ((opNativeEffect op).gClob ++ armScratch) []
        (opNativeEffect op).fClob →
      (jmp₁ a s₁').All P₁ → (jmp₂ a s₂').All P₂)
    (h : (op.interp p s₁ next₁ jmp₁).All P₁) :
    (op.interp p s₂ next₂ jmp₂).All P₂ := by
  have uL : ∀ {xs ys : List Arm64.Reg}, (∀ r ∈ xs ++ ys, r ∉ armScratch) →
      ∀ r ∈ xs, r ∉ armScratch := fun h r hr => h r (List.mem_append_left _ hr)
  have uR : ∀ {xs ys : List Arm64.Reg}, (∀ r ∈ xs ++ ys, r ∉ armScratch) →
      ∀ r ∈ ys, r ∉ armScratch := fun h r hr => h r (List.mem_append_right _ hr)
  have hst : ∀ st, AgreeNonScratch { s₁ with status := st } { s₂ with status := st } :=
    fun _ => ⟨ha.1, rfl, ha.2.2⟩
  have frRefl := Machine.Frame.refl (M := armMach) armCondReads s₂
    ((opNativeEffect op).gClob ++ armScratch) [] (opNativeEffect op).fClob
  cases op with
  | LDR dst src | LDRSW dst src =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    refine agree_aolLoad (gClob := (regOfZr dst ++ addrOrLitClob src) ++ armScratch) ha huse
      (fun _ hr => List.mem_append_left _ (List.mem_append_right _ hr))
      h fun v s₁' s₂' ha' hfr' hv => ?_
    refine hnext _ _ (agree_setZr ha' dst _) ?_ hv
    exact armFrame_weaken_clob (armFrame_trans_or hfr' (agree_frame_setZr dst _ s₂'
      (gClob := (regOfZr dst ++ addrOrLitClob src) ++ armScratch) (fun _ hr =>
      List.mem_append_left _ (List.mem_append_left _ hr))))
      (fun _ hm => by rcases List.mem_append.mp hm with h1 | h1 <;> exact h1) (Or.inl rfl)
  | LDRB dst src | LDRSB dst src | LDRH dst src | LDRSH dst src =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    refine agree_addrLoad (gClob := (regOfZr dst ++ addrExprClob src) ++ armScratch) ha huse
      (fun _ hr => List.mem_append_left _ (List.mem_append_right _ hr))
      h fun v s₁' s₂' ha' hfr' hv => ?_
    refine hnext _ _ (agree_setZr ha' dst _) ?_ hv
    exact armFrame_weaken_clob (armFrame_trans_or hfr' (agree_frame_setZr dst _ s₂'
      (gClob := (regOfZr dst ++ addrExprClob src) ++ armScratch) (fun _ hr =>
      List.mem_append_left _ (List.mem_append_left _ hr))))
      (fun _ hm => by rcases List.mem_append.mp hm with h1 | h1 <;> exact h1) (Or.inl rfl)
  | LDP d1 d2 src | LDPSW d1 d2 src =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    refine agree_checkSP ha h fun h1 => ?_
    have ⟨haddr, ha'⟩ := agree_addrEval ha src huse p
    have hfrE := agree_frame_addrEval src s₂ p (gClob :=
      (regOfZr d1 ++ regOfZr d2 ++ addrExprClob src) ++ armScratch) (fun _ hr => by simp [hr])
    rw [← haddr]
    refine agree_load ha'.2.2 h1 fun v1 h2 => agree_load ha'.2.2 h2 fun v2 h3 => ?_
    refine hnext _ _ (agree_setZr (agree_setZr ha' d1 _) d2 _) ?_ h3
    exact armFrame_weaken_clob (armFrame_trans_or hfrE
      (armFrame_trans_or
        (agree_frame_setZr d1 _ (src.eval s₂ p).2 (gClob :=
          (regOfZr d1 ++ regOfZr d2 ++ addrExprClob src) ++ armScratch) (fun _ hr => by simp [hr]))
        (agree_frame_setZr d2 _ _ (gClob :=
          (regOfZr d1 ++ regOfZr d2 ++ addrExprClob src) ++ armScratch)
          (fun _ hr => by simp [hr]))))
      (fun _ hm => by
        rcases List.mem_append.mp hm with h1 | h1
        · exact h1
        · rcases List.mem_append.mp h1 with h2 | h2 <;> exact h2) (Or.inl rfl)
  | LDUR dst src | LDURB dst src | LDURSB dst src
  | LDURH dst src | LDURSH dst src | LDURSW dst src =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    have hb : s₁.regs.getRegOrSp src.base = s₂.regs.getRegOrSp src.base :=
      agree_getSp ha src.base huse
    refine agree_uCheckSP ha h fun h1 => ?_
    simp only [UnscaledAddrExpr.eval, hb] at h1 ⊢
    exact agree_load ha.2.2 h1 fun v hv => hnext _ _ (agree_setZr ha dst _)
      (agree_frame_setZr dst _ s₂ (fun _ hr => List.mem_append_left _ hr)) hv
  | STR src dst | STRB src dst | STRH src dst =>
    dsimp only [Operation.interp, opNativeEffect, AddrExpr.interpStore] at h huse hnext ⊢
    have hsrc : s₁.regs.getRegOrZr src = s₂.regs.getRegOrZr src := agree_getZr ha src (uL huse)
    refine agree_checkSP ha h fun h1 => ?_
    have ⟨haddr, ha'⟩ := agree_addrEval ha dst (uR huse) p
    have hfrE := agree_frame_addrEval dst s₂ p (gClob := addrExprClob dst ++ armScratch)
      (fun _ hr => List.mem_append_left _ hr)
    rw [← haddr, ← hsrc]
    exact agree_store ha' h1 fun m' ha'' hm' => hnext _ _ ha'' hfrE hm'
  | STP src1 src2 dst =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    have hs1 : s₁.regs.getRegOrZr src1 = s₂.regs.getRegOrZr src1 :=
      agree_getZr ha src1 (uL (uL huse))
    have hs2 : s₁.regs.getRegOrZr src2 = s₂.regs.getRegOrZr src2 :=
      agree_getZr ha src2 (uR (uL huse))
    refine agree_checkSP ha h fun h1 => ?_
    have ⟨haddr, ha'⟩ := agree_addrEval ha dst (uR huse) p
    have hfrE := agree_frame_addrEval dst s₂ p (gClob := addrExprClob dst ++ armScratch)
      (fun _ hr => List.mem_append_left _ hr)
    rw [← haddr, ← hs1, ← hs2]
    exact agree_store ha' h1 fun m1 ha1 h2 => agree_store ha1 h2 fun m2 ha2 h3 =>
      hnext _ _ ha2 hfrE h3
  | STUR src dst | STURB src dst | STURH src dst =>
    dsimp only [Operation.interp, opNativeEffect, UnscaledAddrExpr.interpStore] at h huse hnext ⊢
    have hsrc : s₁.regs.getRegOrZr src = s₂.regs.getRegOrZr src := agree_getZr ha src (uL huse)
    have hb : s₁.regs.getRegOrSp dst.base = s₂.regs.getRegOrSp dst.base :=
      agree_getSp ha dst.base (uR huse)
    refine agree_uCheckSP ha h fun h1 => ?_
    simp only [UnscaledAddrExpr.eval, hb, hsrc] at h1 ⊢
    exact agree_store ha h1 fun m' ha' hm' => hnext _ _ ha' frRefl hm'
  | ADD_e dst s1 s2 | SUB_e dst s1 s2 =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getSp ha s1 (uL huse), ← agree_extOrImm ha s2 (uR huse) p]
    exact hnext _ _ (agree_setSp ha dst _) (agree_frame_setSp dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | ADDS_e dst s1 s2 | SUBS_e dst s1 s2 =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getSp ha s1 (uL huse), ← agree_extOrImm ha s2 (uR huse) p]
    exact hnext _ _ (agree_setZr (hst _) dst _)
      (agree_frame_setZr_nzcv dst _ _ s₂ (fun _ hr => List.mem_append_left _ hr)) h
  | ADD_s dst s1 s2 | SUB_s dst s1 s2 | AND_s dst s1 s2 | ORR_s dst s1 s2
  | ORN_s dst s1 s2 | EOR_s dst s1 s2 | EON_s dst s1 s2 | BIC_s dst s1 s2 =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 (uL huse), ← agree_shiftReg ha s2 (uR huse) p]
    exact hnext _ _ (agree_setZr ha dst _) (agree_frame_setZr dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | ADDS_s dst s1 s2 | SUBS_s dst s1 s2 | ANDS_s dst s1 s2 | BICS_s dst s1 s2 =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 (uL huse), ← agree_shiftReg ha s2 (uR huse) p]
    exact hnext _ _ (agree_setZr (hst _) dst _)
      (agree_frame_setZr_nzcv dst _ _ s₂ (fun _ hr => List.mem_append_left _ hr)) h
  | AND_i dst s1 _ | ORR_i dst s1 _ | EOR_i dst s1 _ =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 huse]
    exact hnext _ _ (agree_setSp ha dst _) (agree_frame_setSp dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | ANDS_i dst s1 _ =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 huse]
    exact hnext _ _ (agree_setZr (hst _) dst _)
      (agree_frame_setZr_nzcv dst _ _ s₂ (fun _ hr => List.mem_append_left _ hr)) h
  | SDIV dst s1 s2 | UDIV dst s1 s2 | SMULH dst s1 s2 | UMULH dst s1 s2
  | EXTR dst s1 s2 _ | LSLV dst s1 s2 | LSRV dst s1 s2 | ASRV dst s1 s2 | RORV dst s1 s2 =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 (uL huse), ← agree_getZr ha s2 (uR huse)]
    exact hnext _ _ (agree_setZr ha dst _) (agree_frame_setZr dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | ADC dst s1 s2 | SBC dst s1 s2
  | CSEL dst s1 s2 _ | CSINC dst s1 s2 _ | CSINV dst s1 s2 _ | CSNEG dst s1 s2 _ =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 (uL huse), ← agree_getZr ha s2 (uR huse), ← ha.2.1]
    exact hnext _ _ (agree_setZr ha dst _) (agree_frame_setZr dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | ADCS dst s1 s2 | SBCS dst s1 s2 =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 (uL huse), ← agree_getZr ha s2 (uR huse), ← ha.2.1]
    exact hnext _ _ (agree_setZr (hst _) dst _)
      (agree_frame_setZr_nzcv dst _ _ s₂ (fun _ hr => List.mem_append_left _ hr)) h
  | MADD dst s1 s2 s3 | MSUB dst s1 s2 s3
  | SMADDL dst s1 s2 s3 | UMADDL dst s1 s2 s3
  | SMSUBL dst s1 s2 s3 | UMSUBL dst s1 s2 s3 =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 (uL (uL huse)), ← agree_getZr ha s2 (uR (uL huse)),
      ← agree_getZr ha s3 (uR huse)]
    exact hnext _ _ (agree_setZr ha dst _) (agree_frame_setZr dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | SBFM dst src _ _ | UBFM dst src _ _
  | CLZ dst src | CLS dst src | RBIT dst src
  | REV dst src | REV16 dst src | REV32 dst src =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha src huse]
    exact hnext _ _ (agree_setZr ha dst _) (agree_frame_setZr dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | BFM dst src _ _ =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha dst (uL huse), ← agree_getZr ha src (uR huse)]
    exact hnext _ _ (agree_setZr ha dst _) (agree_frame_setZr dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | MOVZ dst _ _ | MOVN dst _ _ | ADR dst _ | ADRP dst _ =>
    dsimp only [Operation.interp, opNativeEffect] at h hnext ⊢
    exact hnext _ _ (agree_setZr ha dst _) (agree_frame_setZr dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | MOVK dst _ _ =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha dst huse]
    exact hnext _ _ (agree_setZr ha dst _) (agree_frame_setZr dst _ s₂
      (fun _ hr => List.mem_append_left _ hr)) h
  | CCMP_reg s1 s2 _ _ | CCMN_reg s1 s2 _ _ =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 (uL huse), ← agree_getZr ha s2 (uR huse), ← ha.2.1]
    exact hnext _ _ (hst _) (armFrame_nzcv fun _ _ => rfl) h
  | CCMP_imm s1 _ _ _ | CCMN_imm s1 _ _ _ =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext ⊢
    rw [← agree_getZr ha s1 huse, ← ha.2.1]
    exact hnext _ _ (hst _) (armFrame_nzcv fun _ _ => rfl) h
  | B _ => exact hjmp _ _ _ ha frRefl h
  | BL _ =>
    exact hjmp _ _ _ (agree_setZr ha RegOrZr.X30 _)
      (agree_frame_setZr RegOrZr.X30 _ s₂ (fun _ hr => List.mem_append_left _ hr)) h
  | BLR tgt =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hjmp ⊢
    rw [← agree_getZr ha tgt huse]
    exact hjmp _ _ _ (agree_setZr ha RegOrZr.X30 _)
      (agree_frame_setZr RegOrZr.X30 _ s₂ (fun _ hr => List.mem_append_left _ hr)) h
  | BR tgt | RET tgt =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hjmp ⊢
    rw [← agree_getZr ha tgt huse]
    exact hjmp _ _ _ ha frRefl h
  | B_cond _ _ =>
    dsimp only [Operation.interp] at h ⊢
    rw [← ha.2.1]
    split
    · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact hjmp _ _ _ ha frRefl h
    · rename_i hc; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; exact hnext _ _ ha frRefl h
  | CBZ tgt _ | CBNZ tgt _ | TBZ tgt _ _ | TBNZ tgt _ _ =>
    dsimp only [Operation.interp, opNativeEffect] at h huse hnext hjmp ⊢
    rw [← agree_getZr ha tgt huse]
    split
    · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact hjmp _ _ _ ha frRefl h
    · rename_i hc; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; exact hnext _ _ ha frRefl h
  | NOP => exact hnext _ _ ha frRefl h

private theorem directive_interp_agree [Labels] (d : _root_.Directive)
    (s₁ s₂ : MachineData) (p : Std.Rco Int64)
    (next₁ next₂ : MachineData → Effects) (jmp₁ jmp₂ : Int64 → MachineData → Effects)
    (P₁ P₂ : MachineState → Prop) (ha : AgreeNonScratch s₁ s₂)
    (huse : ∀ r ∈ (arm64NativeEffect d).gUses, r ∉ armScratch)
    (hnext : ∀ s₁' s₂', AgreeNonScratch s₁' s₂' →
      armMach.Frame armCondReads s₂ s₂' ((arm64NativeEffect d).gClob ++ armScratch) []
        (arm64NativeEffect d).fClob →
      (next₁ s₁').All P₁ → (next₂ s₂').All P₂)
    (hjmp : ∀ a s₁' s₂', AgreeNonScratch s₁' s₂' →
      armMach.Frame armCondReads s₂ s₂' ((arm64NativeEffect d).gClob ++ armScratch) []
        (arm64NativeEffect d).fClob →
      (jmp₁ a s₁').All P₁ → (jmp₂ a s₂').All P₂)
    (h : (d.interp s₁ p next₁ jmp₁).All P₁) :
    (d.interp s₂ p next₂ jmp₂).All P₂ := by
  have frRefl := Machine.Frame.refl (M := armMach) armCondReads s₂
    ((arm64NativeEffect d).gClob ++ armScratch) [] (arm64NativeEffect d).fClob
  cases d with
  | label _ => exact hnext s₁ s₂ ha frRefl h
  | instr i =>
    exact op_interp_agree i.operation s₁ s₂ p next₁ next₂ jmp₁ jmp₂ P₁ P₂ ha huse hnext hjmp h
  | byteArray bs =>
    dsimp only [Directive.interp] at h ⊢
    split
    · rename_i hc; rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; exact hnext s₁ s₂ ha frRefl h
    · rename_i hc; rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h
  | word bytes _ =>
    cases bytes with | zero => exact hnext s₁ s₂ ha frRefl h | succ _ => cases h

theorem asmNative_fallsTo_wp [h : Host] {d : _root_.Directive} {sv sv' : MachSt arm64Arch}
    {sm : MachineData} (huses : ∀ r ∈ (arm64NativeEffect d).gUses, r ∉ armScratch)
    (hrel : arm64StateRel sv sm) (hst : arm64NativeStep d (hostSymAddr h) sv (.fall sv')) :
    _root_.Program.wp [d]
      (fun sm' => arm64StateRel sv' sm' ∧
        armMach.Frame armCondReads sm sm' ((arm64NativeEffect d).gClob ++ armScratch) []
          (arm64NativeEffect d).fClob)
      (fun _ _ => False) sm := by
  refine _root_.Program.wp_singleton fun k _ => ?_
  have hdStep := hst ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
  rw [labelsOfSymAddr_hostSymAddr] at hdStep
  refine directive_interp_agree d (vllToMachData sv) sm ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
    _ _ _ _ _ _ (agreeNonScratch_of_stateRel hrel) huses ?_ ?_ hdStep
  · intro sv_m' sm' ha' hfr' hEq'
    dsimp only [Effects.All] at hEq' ⊢
    have hEq'' : machDataToVll sv_m' = sv' := hEq'
    subst hEq''
    exact Or.inl ⟨rfl, stateRel_of_agreeNonScratch ha', hfr'⟩
  · intro _ _ _ _ _ hf; cases hf

theorem asmNative_jump_run {h : Host} {k : Nat} {d : _root_.Directive}
    {sv sv' : MachSt arm64Arch} {pc' : BitVec 64} {sm : MachineData}
    {post : MachineState → Prop} (hc : [d].IsInfixAt (armMach.prog h) k)
    (huses : ∀ r ∈ (arm64NativeEffect d).gUses, r ∉ armScratch)
    (hrel : arm64StateRel sv sm) (hst : arm64NativeStep d (hostSymAddr h) sv (.jump pc' sv'))
    (hcont : ∀ sm', arm64StateRel sv' sm' →
      armMach.Frame armCondReads sm sm' ((arm64NativeEffect d).gClob ++ armScratch) []
        (arm64NativeEffect d).fClob →
      Eventually (armMach.step h) post ⟨sm', Int64.ofBitVec pc'⟩) :
    armMach.Run h k sm post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  have hdStep := hst ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
  rw [labelsOfSymAddr_hostSymAddr] at hdStep
  refine directive_interp_agree d (vllToMachData sv) sm ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
    _ _ _ _ _ _ (agreeNonScratch_of_stateRel hrel) huses ?_ ?_ hdStep
  · intro _ _ _ _ hf; cases hf
  · intro a sv_m' sm' ha' hfr' hPair
    dsimp only [Effects.All] at hPair ⊢
    have haEq : a = Int64.ofBitVec pc' := by rw [← hPair.1, Int64.ofBitVec_toBitVec]
    have hsEq : machDataToVll sv_m' = sv' := hPair.2
    subst hsEq; rw [haEq]
    exact hcont sm' (stateRel_of_agreeNonScratch ha') hfr'

end LeanQbe.T.Vll
