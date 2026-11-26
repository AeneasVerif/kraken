module

public import LeanQbe.T.Vll.FromWordLemmas
public import LeanQbe.T.Arm64.VllAsmArm64Lemmas
public import LeanQbe.T.Arm64.Isel
public import LeanQbeTest.T.BedrockCfgStage2Test
public import LeanQbeTest.T.XcapBridgeArm64Test
import LeanQbe.T.Vll.FromWordLemmas0
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Arm64.IselLemmas1
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.AbiLemmas
import Kraken.AArch64.Parser
import Kraken.Mem
import Kraken.Separation
public meta import Lean
public meta import LeanQbe.T.Vll.FromWord
public meta import LeanQbe.T.Vll.FromWordLemmas
public meta import LeanQbe.T.Arm64.VllArm64
public meta import LeanQbe.T.Arm64.VllAsmArm64
public meta import LeanQbeTest.T.BedrockCfgStage2Test
public meta import LeanQbeTest.T.XcapBridgeArm64Test

/-!
# Verification Suite for `Vll.FromWord` on AArch64 (`VllFromWordTest`)

Instantiates the arch-free `LeanQbe.T.Vll.FromWord` + `FromWordLemmas` pipeline on concrete
`arm64Arch` / `asmArm64` (`LeanQbe.T.Arm64.VllArm64` / `AsmArm64`):

1. `armWordBind : WordRegBind arm64Arch` (`x0..x5` AAPCS64 GPR binding, `x9` dual-ret flag,
   `x10..x12` scratch, `x13..x15` temp pool, `.btiJC` pads, `Arm64.armCmpCond`) + `armWordBind_wf`.
2. Generic `VllHost arm64Arch` & `VllCodeMap.Hosted` builder (`mkFlatHost`, `mkFlatHost_hosted`).
3. **Example 1 (`cmEx1`):** open `fromWord` → `asmArm64CodeMap`, `padsOk`, `fromWord_wp_sound`,
   and concrete small-step `fromWord_hosted_vllStep` execution (`ex1_cm_wp_fast`).
4. **Example 2b (`cmEx2b`):** Stage-1 dual-return `rp + 8` contification emitting hardware
   `bl`/`ret` + `jnzGpr` (`ex2b_contified_spec`, `fromWordContify_wp_sound`,
   `fromWordContify_hosted_vllStep`).
5. **Example 6 (`cmEx6`, `ex6Wit`):** `whileM` loop calling `.contified false` `ex6_raw_step`
   + mutual `even`/`odd` (`fromWordContify_wp_sound`, `fromWordContify_adequacy`).
6. **`PrivFrameCfg` (`numSlots := 1`):** promoted `[sp - 8#64]` slot lowered to `.slotSt` /
   `.slotLd` (`str`/`ldr [sp, #0]`) and verified end-to-end.
7. **`Xcap.Bridge` Interop:** `fromWord_open_cptr_with_fnSpec` linking an open L0 caller with
   compiled `armSelf_doubleAddTen_cptr`, plus `vll_cptr_to_target_fnSpec` and MetaM/axiom audits.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.VllFromWordTest

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Vll
open LeanQbe.T.BedrockWord LeanQbe.T.Unified LeanQbe.T.ProofKit
open LeanQbeTest.T.BedrockCfgStage2Test LeanQbeTest.T.XcapBridgeTest
open LeanQbeTest.T.XcapBridgeArm64Test

/-! ## §1. AAPCS64 `armWordBind : WordRegBind arm64Arch` & Soundness -/

/-- Canonical AAPCS64 6-register L0 word binding onto `x0..x5` with dual-return flag `x9`,
work registers `x10..x12`, fast temps `x13..x15`, `.btiJC` pads, and `Arm64.armCmpCond`. -/
@[expose] def armWordBind : WordRegBind arm64Arch where
  sp := .reg .X0
  rp := .reg .X1
  rv := .reg .X2
  r1 := .reg .X3
  r2 := .reg .X4
  r3 := .reg .X5
  altRet := .reg .X9
  w0 := .reg .X10
  w1 := .reg .X11
  w2 := .reg .X12
  tmps := [.reg .X13, .reg .X14, .reg .X15]
  padKind := .btiJC
  condOfCmp? := fun o => some (armCmpCond o)

theorem armWordBind_wf : armWordBind.Wf := by
  refine WordRegBind.checkStruct_wf armWordBind (by decide) ?_
  intro o c w x y f hcc
  cases hcc
  cases w with
  | w8 =>
    simp only [arm64CmpFlags, armCmpCond, ArmCond.interp, ArmCond.toKraken,
      CondCode.interp, StatusFlags.subs, StatusFlags.from_result, CmpOp.evalBits,
      BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle]
    cases o <;> grind [BitVec.unsigned, BitVec.signed]
  | w16 =>
    simp only [arm64CmpFlags, armCmpCond, ArmCond.interp, ArmCond.toKraken,
      CondCode.interp, StatusFlags.subs, StatusFlags.from_result, CmpOp.evalBits,
      BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle]
    cases o <;> grind [BitVec.unsigned, BitVec.signed]
  | w32 => exact armCmpCond_subs (Or.inl rfl) o x y
  | w64 => exact armCmpCond_subs (Or.inr rfl) o x y

/-! ## §2. `VllHost` & `VllCodeMap.Hosted` Builder for Concrete Flattened Programs -/

@[expose] def isOkBool {α β : Type} : Except α β → Bool
  | .ok _ => true
  | .error _ => false

@[expose] def unwrapVcm (res : Except String (VllCodeMap arm64Arch)) : VllCodeMap arm64Arch :=
  match res with
  | .ok v => v
  | .error _ => ⟨[], fun _ => 0#64, []⟩

private theorem except_ok_of_isOkBool {res : Except String (VllCodeMap arm64Arch)}
    (h : isOkBool res = true) : res = .ok (unwrapVcm res) := by
  cases res with
  | ok _ => rfl
  | error _ => simp [isOkBool] at h

@[expose] def lowerContRegionFast {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) (pcs : List (BitVec 64)) (ns : Nat) (nf : Bool) :
    LowerM (List (Block A)) := do
  let pfx := (if nf then [.prologue ns] else []) ++
    emitPrivFrameInit b cr.privFrame.numSlots
  let entryBlk : Block A :=
    { label := cr.name, pad? := some b.padKind, body := pfx,
      term := .fall (innerLabel cr cr.entryPc) }
  let innerLists ← pcs.mapM fun pc => do
    let some ceBlock := cm.lookupAddr pc | liftEx (.error s!"FromWord: missing pc {pc}")
    lowerContBlock b cm cr pc (regionSpillBase cr) ns nf (innerLabel cr pc)
      [] 6 [] ContSymState.init ceBlock
  pure (entryBlk :: innerLists.flatten)

@[expose] def rawFromWordContify {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (wit : ContifyWitness)
    (items : List (ContifyRegion × List (BitVec 64) × Nat × Bool)) :
    Except String (VllCodeMap A) := do
  let (regs, _) ← (items.mapM fun x =>
    lowerContRegionFast b cm x.1 x.2.1 x.2.2.1 x.2.2.2).run 0
  let blocks := regs.flatten
  let symAddr := buildVllSymAddr
    (wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++ cm.map fun e => (e.name, e.addr))
    blocks
  pure { blocks := blocks, symAddr := symAddr, addrTaken := wit.regions.map (·.name) }

@[expose] def rawContVcm (b : WordRegBind arm64Arch) (cm : CodeMap)
    (wit : ContifyWitness)
    (items : List (ContifyRegion × List (BitVec 64) × Nat × Bool)) :
    VllCodeMap arm64Arch :=
  unwrapVcm (rawFromWordContify b cm wit items)

@[expose] def fastFromWordContify {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (wit : ContifyWitness)
    (items : List (ContifyRegion × List (BitVec 64) × Nat × Bool)) :
    Except String (VllCodeMap A) := do
  let vcm ← rawFromWordContify b cm wit items
  finalizeVllCodeMap vcm

theorem lowerContRegion_eq_fast {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) {pcs : List (BitVec 64)} {ns : Nat} {nf : Bool}
    (hpcs : cr.allPcs = pcs) (hns : regionFrameSlots b cm cr = ns)
    (hnf : regionNeedFrame b cm cr = nf) :
    lowerContRegion b cm cr = lowerContRegionFast b cm cr pcs ns nf := by
  subst hpcs hns hnf
  dsimp only [lowerContRegion, lowerContRegionFast]
  congr 1

theorem mapM_lowerContRegion_eq_fast {A : Arch} (b : WordRegBind A) (cm : CodeMap) :
    ∀ (items : List (ContifyRegion × List (BitVec 64) × Nat × Bool)),
      (∀ x ∈ items, x.1.allPcs = x.2.1 ∧ regionFrameSlots b cm x.1 = x.2.2.1 ∧
        regionNeedFrame b cm x.1 = x.2.2.2) →
      (items.map Prod.fst).mapM (lowerContRegion b cm) =
        items.mapM (fun x => lowerContRegionFast b cm x.1 x.2.1 x.2.2.1 x.2.2.2)
  | [], _ => rfl
  | x :: xs, h => by
    obtain ⟨hp, hns, hnf⟩ := h x List.mem_cons_self
    have htl := mapM_lowerContRegion_eq_fast b cm xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, List.mapM_cons]
    rw [lowerContRegion_eq_fast b cm x.1 hp hns hnf, htl]

theorem fromWordContify_eq_fast {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (wit : ContifyWitness)
    (items : List (ContifyRegion × List (BitVec 64) × Nat × Bool))
    (hRegs : wit.regions = items.map Prod.fst)
    (hwf : cm.checkWf = true) (hchk : wit.check cm = true)
    (hres : residualContifyCodeMap cm wit = [])
    (hItems : ∀ x ∈ items, x.1.allPcs = x.2.1 ∧ regionFrameSlots b cm x.1 = x.2.2.1 ∧
      regionNeedFrame b cm x.1 = x.2.2.2) :
    fromWordContify b cm wit = fastFromWordContify b cm wit items := by
  dsimp only [fromWordContify, fastFromWordContify, rawFromWordContify]
  have hMap : wit.regions.mapM (lowerContRegion b cm) =
      items.mapM (fun x => lowerContRegionFast b cm x.1 x.2.1 x.2.2.1 x.2.2.2) := by
    rw [hRegs]; exact mapM_lowerContRegion_eq_fast b cm items hItems
  rw [hwf, hchk, hres, hMap]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.mapM_nil, List.append_nil,
    List.map_nil]
  cases (items.mapM fun x =>
      lowerContRegionFast b cm x.1 x.2.1 x.2.2.1 x.2.2.2).run 0 with
  | error _ => rfl
  | ok _ => simp [StateT.run, StateT.pure, Pure.pure, Except.pure, Bind.bind, Except.bind]

private theorem nat_repr_inj {m n : Nat} (h : Nat.repr m = Nat.repr n) : m = n := by
  have hl : (Nat.repr m).toList = (Nat.repr n).toList := congrArg String.toList h
  rw [Nat.toList_repr, Nat.toList_repr] at hl
  have hp := congrArg (fun ds => Nat.ofDigitChars 10 ds 0) hl
  rwa [Nat.ofDigitChars_ten_toDigits, Nat.ofDigitChars_ten_toDigits] at hp

inductive TagLbl where
  | raw (s : String)
  | pc (s : String) (n : Nat)
  | aux (s : String) (n : Nat)
  deriving DecidableEq

@[expose] def TagLbl.toStr : TagLbl → String
  | .raw s => s
  | .pc s n => s!"{s}__pc_{n}"
  | .aux s n => s!"{s}__aux_{n}"

@[expose] def noDblUnder : List Char → Bool
  | [] => true
  | '_' :: '_' :: _ => false
  | _ :: xs => noDblUnder xs

@[expose] def TagLbl.pfx : TagLbl → String
  | .raw s => s
  | .pc s _ => s
  | .aux s _ => s

@[expose] def TagLbl.pfxOk (t : TagLbl) : Bool :=
  noDblUnder t.pfx.toList && (t.pfx.toList.getLast? != some '_')

private theorem noDblUnder_tail {x : Char} {xs : List Char}
    (h : noDblUnder (x :: xs) = true) : noDblUnder xs = true := by
  cases xs with
  | nil => rfl
  | cons y ys =>
    by_cases hx : x = '_' <;> by_cases hy : y = '_' <;> simp_all [noDblUnder]

private theorem noDblUnder_not_append_dbl {xs ys : List Char}
    (h : noDblUnder xs = true) : noDblUnder (xs ++ '_' :: '_' :: ys) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil =>
      by_cases hx : x = '_'
      · subst hx; rfl
      · simp [noDblUnder, hx]
    | cons z zs =>
      have ih' := ih (noDblUnder_tail h)
      by_cases hx : x = '_'
      · subst hx
        have hz : z ≠ '_' := fun hze => by subst hze; simp [noDblUnder] at h
        simpa [noDblUnder, hz] using ih'
      · simpa [noDblUnder, hx] using ih'

private theorem noDblUnder_split_dbl :
    ∀ {xs₁ xs₂ ys₁ ys₂ : List Char},
      noDblUnder xs₁ = true → xs₁.getLast? ≠ some '_' →
      noDblUnder xs₂ = true → xs₂.getLast? ≠ some '_' →
      ∀ {c₁ c₂ : Char}, c₁ ≠ '_' → c₂ ≠ '_' →
      xs₁ ++ '_' :: '_' :: c₁ :: ys₁ = xs₂ ++ '_' :: '_' :: c₂ :: ys₂ →
      xs₁ = xs₂ ∧ c₁ :: ys₁ = c₂ :: ys₂
  | [], [], _, _, _, _, _, _, _, _, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | [], [_], _, _, _, _, _, hl2, _, _, _, _, h => by
    simp only [List.nil_append, List.singleton_append, List.cons.injEq] at h
    simp only [List.getLast?_singleton, ne_eq, Option.some.injEq] at hl2
    exact absurd h.1.symm hl2
  | [], _ :: _ :: _, _, _, _, _, h2, _, _, _, _, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    have h2' := h2; rw [← h.1, ← h.2.1] at h2'; simp [noDblUnder] at h2'
  | [_], [], _, _, _, hl1, _, _, _, _, _, _, h => by
    simp only [List.nil_append, List.singleton_append, List.cons.injEq] at h
    simp only [List.getLast?_singleton, ne_eq, Option.some.injEq] at hl1
    exact absurd h.1 hl1
  | _ :: _ :: _, [], _, _, h1, _, _, _, _, _, _, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    have h1' := h1; rw [h.1, h.2.1] at h1'; simp [noDblUnder] at h1'
  | x :: xs₁, _ :: xs₂, ys₁, ys₂, h1, hl1, h2, hl2, c₁, c₂, hc1, hc2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases h with ⟨rfl, htail⟩
    have hl1' : xs₁.getLast? ≠ some '_' := by
      cases xs₁ with | nil => simp | cons a as => simpa [List.getLast?_cons_cons] using hl1
    have hl2' : xs₂.getLast? ≠ some '_' := by
      cases xs₂ with | nil => simp | cons a as => simpa [List.getLast?_cons_cons] using hl2
    obtain ⟨hxs, hys⟩ := noDblUnder_split_dbl (noDblUnder_tail h1) hl1'
      (noDblUnder_tail h2) hl2' hc1 hc2 htail
    exact ⟨congrArg (x :: ·) hxs, hys⟩

private theorem tagLbl_toStr_ne_raw {s₁ : String} (h1 : noDblUnder s₁.toList = true)
    {s₂ : String} (h2 : noDblUnder s₂.toList = true) {mid : List Char}
    (heq : s₁.toList = s₂.toList ++ '_' :: '_' :: mid) : False := by
  have hfalse : noDblUnder s₁.toList = false := by
    rw [heq]; exact noDblUnder_not_append_dbl h2
  rw [h1] at hfalse; cases hfalse

private theorem pc_str_toList (s : String) (n : Nat) :
    (s!"{s}__pc_{n}").toList =
      s.toList ++ '_' :: '_' :: 'p' :: 'c' :: '_' :: (Nat.repr n).toList := by
  have hp : ("__pc_" : String).toList = ['_', '_', 'p', 'c', '_'] := by decide
  change (s ++ "__pc_" ++ Nat.repr n).toList = _
  rw [String.toList_append, String.toList_append, hp, List.append_assoc]; rfl

private theorem aux_str_toList (s : String) (n : Nat) :
    (s!"{s}__aux_{n}").toList =
      s.toList ++ '_' :: '_' :: 'a' :: 'u' :: 'x' :: '_' :: (Nat.repr n).toList := by
  have ha : ("__aux_" : String).toList = ['_', '_', 'a', 'u', 'x', '_'] := by decide
  change (s ++ "__aux_" ++ Nat.repr n).toList = _
  rw [String.toList_append, String.toList_append, ha, List.append_assoc]; rfl

private theorem tagLbl_toStr_inj {t₁ t₂ : TagLbl}
    (h1 : t₁.pfxOk = true) (h2 : t₂.pfxOk = true) (heq : t₁.toStr = t₂.toStr) : t₁ = t₂ := by
  have hp1 : noDblUnder t₁.pfx.toList = true ∧ t₁.pfx.toList.getLast? ≠ some '_' := by
    simpa [TagLbl.pfxOk, Bool.and_eq_true, bne_iff_ne] using h1
  have hp2 : noDblUnder t₂.pfx.toList = true ∧ t₂.pfx.toList.getLast? ≠ some '_' := by
    simpa [TagLbl.pfxOk, Bool.and_eq_true, bne_iff_ne] using h2
  have hl := congrArg String.toList heq
  cases t₁ <;> cases t₂
  case raw.raw => exact congrArg TagLbl.raw heq
  case raw.pc s₁ s₂ n₂ =>
    dsimp only [TagLbl.toStr] at hl; rw [pc_str_toList] at hl
    exact absurd hl (fun e => tagLbl_toStr_ne_raw hp1.1 hp2.1 e)
  case raw.aux s₁ s₂ n₂ =>
    dsimp only [TagLbl.toStr] at hl; rw [aux_str_toList] at hl
    exact absurd hl (fun e => tagLbl_toStr_ne_raw hp1.1 hp2.1 e)
  case pc.raw s₁ n₁ s₂ =>
    dsimp only [TagLbl.toStr] at hl; rw [pc_str_toList] at hl
    exact absurd hl.symm (fun e => tagLbl_toStr_ne_raw hp2.1 hp1.1 e)
  case aux.raw s₁ n₁ s₂ =>
    dsimp only [TagLbl.toStr] at hl; rw [aux_str_toList] at hl
    exact absurd hl.symm (fun e => tagLbl_toStr_ne_raw hp2.1 hp1.1 e)
  case pc.pc s₁ n₁ s₂ n₂ =>
    dsimp only [TagLbl.toStr] at hl; rw [pc_str_toList, pc_str_toList] at hl
    obtain ⟨hs, hn⟩ := noDblUnder_split_dbl hp1.1 hp1.2 hp2.1 hp2.2
      (by decide : 'p' ≠ '_') (by decide : 'p' ≠ '_') hl
    simp only [List.cons.injEq, true_and] at hn
    have hs' : s₁ = s₂ := String.ext hs
    have hn' : n₁ = n₂ := nat_repr_inj (String.ext hn)
    subst hs'; subst hn'; rfl
  case pc.aux s₁ n₁ s₂ n₂ =>
    dsimp only [TagLbl.toStr] at hl; rw [pc_str_toList, aux_str_toList] at hl
    obtain ⟨_, hn⟩ := noDblUnder_split_dbl hp1.1 hp1.2 hp2.1 hp2.2
      (by decide : 'p' ≠ '_') (by decide : 'a' ≠ '_') hl
    cases hn
  case aux.pc s₁ n₁ s₂ n₂ =>
    dsimp only [TagLbl.toStr] at hl; rw [aux_str_toList, pc_str_toList] at hl
    obtain ⟨_, hn⟩ := noDblUnder_split_dbl hp1.1 hp1.2 hp2.1 hp2.2
      (by decide : 'a' ≠ '_') (by decide : 'p' ≠ '_') hl
    cases hn
  case aux.aux s₁ n₁ s₂ n₂ =>
    dsimp only [TagLbl.toStr] at hl; rw [aux_str_toList, aux_str_toList] at hl
    obtain ⟨hs, hn⟩ := noDblUnder_split_dbl hp1.1 hp1.2 hp2.1 hp2.2
      (by decide : 'a' ≠ '_') (by decide : 'a' ≠ '_') hl
    simp only [List.cons.injEq, true_and] at hn
    have hs' : s₁ = s₂ := String.ext hs
    have hn' : n₁ = n₂ := nat_repr_inj (String.ext hn)
    subst hs'; subst hn'; rfl

private theorem labelsUnique_go_of_nodup :
    ∀ {xs : List Sym}, xs.Nodup → VllCodeMap.labelsUnique.go xs = true
  | [], _ => rfl
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    dsimp only [VllCodeMap.labelsUnique.go]
    rw [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, labelsUnique_go_of_nodup hnd.2⟩
    cases hc : xs.contains x with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.mp hc) hnd.1

private theorem addrsUnique_go_of_nodup :
    ∀ {xs : List (BitVec 64)}, xs.Nodup → VllCodeMap.addrsUnique.go xs = true
  | [], _ => rfl
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    dsimp only [VllCodeMap.addrsUnique.go]
    rw [Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨?_, addrsUnique_go_of_nodup hnd.2⟩
    cases hc : xs.contains x with
    | false => rfl
    | true => exact absurd (List.contains_iff_mem.mp hc) hnd.1

private theorem nodup_map_of_inj {α β : Type} {f : α → β} :
    ∀ {xs : List α}, xs.Nodup → (∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) →
      (xs.map f).Nodup
  | [], _, _ => .nil
  | x :: xs, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, nodup_map_of_inj hnd.2 fun a ha b hb =>
      hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
    intro hm
    obtain ⟨y, hy, heq⟩ := List.mem_map.mp hm
    have := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self heq
    subst this; exact hnd.1 hy

private theorem foldl_max_le :
    ∀ (xs : List (BitVec 64)) (acc : Nat),
      acc ≤ xs.foldl (fun m a => Nat.max m a.toNat) acc ∧
      ∀ a ∈ xs, a.toNat ≤ xs.foldl (fun m a => Nat.max m a.toNat) acc
  | [], acc => ⟨Nat.le_refl _, fun _ ha => by cases ha⟩
  | x :: xs, acc => by
    have ih := foldl_max_le xs (Nat.max acc x.toNat)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) ih.1, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | htail
    · exact Nat.le_trans (Nat.le_max_right _ _) ih.1
    · exact ih.2 a htail

private theorem findFreshAddrAux_fresh (used : List (BitVec 64)) (cand : BitVec 64)
    (fuel : Nat) (hnot : cand ∉ used) :
    findFreshAddrAux used cand (fuel + 1) = cand := by
  dsimp only [findFreshAddrAux]
  have hf : used.contains cand = false := Bool.eq_false_iff.mpr fun hc =>
    hnot (List.contains_iff_mem.mp hc)
  rw [hf]; rfl

private structure BuildStepInv (base : List (Sym × BitVec 64)) (startNat : Nat)
    (seen : List Sym) (rem : Nat)
    (st : BitVec 64 × List (BitVec 64) × List (Sym × BitVec 64)) : Prop where
  le_cand : startNat ≤ st.1.toNat
  bound : st.1.toNat + 8 * (rem + 1) < 2 ^ 64
  used_lt : ∀ u ∈ st.2.1, u.toNat < st.1.toNat
  keys_nd : (st.2.2.map Prod.fst).Nodup
  vals_nd : (st.2.2.map Prod.snd).Nodup
  pairs_ok : ∀ p ∈ st.2.2,
    lookupSymAddr base p.1 = none ∧ startNat ≤ p.2.toNat ∧ p.2 ∈ st.2.1
  keys_sub : ∀ p ∈ st.2.2, p.1 ∈ seen
  covered : ∀ l ∈ seen, lookupSymAddr base l = none → ∃ a, (l, a) ∈ st.2.2

private theorem buildStep_foldl {A : Arch} (base : List (Sym × BitVec 64))
    (startNat : Nat) :
    ∀ (remBlocks : List (Block A)) (seen : List Sym)
      (st : BitVec 64 × List (BitVec 64) × List (Sym × BitVec 64)),
      (seen ++ remBlocks.map Block.label).Nodup →
      BuildStepInv base startNat seen remBlocks.length st →
      BuildStepInv base startNat (seen ++ remBlocks.map Block.label) 0
        (remBlocks.foldl
          (fun (st : BitVec 64 × List (BitVec 64) × List (Sym × BitVec 64)) blk =>
            let (cand, used, pairs) := st
            match lookupSymAddr base blk.label with
            | some _ => st
            | none =>
              let a := findFreshAddrAux used cand (used.length + 1)
              (a + 8#64, a :: used, (blk.label, a) :: pairs)) st)
  | [], seen, st, _, hinv => by simpa using hinv
  | blk :: rest, seen, ⟨cand, used, pairs⟩, hnd, hinv => by
    dsimp only [List.foldl_cons]
    have hnd' : ((seen ++ [blk.label]) ++ rest.map Block.label).Nodup := by
      simpa [List.append_assoc] using hnd
    have hlbl_not_seen : blk.label ∉ seen := by
      intro hm
      have hnd1 : (seen ++ blk.label :: rest.map Block.label).Nodup := by simpa using hnd
      exact (List.nodup_append.mp hnd1).2.2 blk.label hm blk.label List.mem_cons_self rfl
    cases hlu : lookupSymAddr base blk.label with
    | some v =>
      dsimp only
      have hinvNext : BuildStepInv base startNat (seen ++ [blk.label]) rest.length
          ⟨cand, used, pairs⟩ :=
        { le_cand := hinv.le_cand
          bound := by have := hinv.bound; simp at this ⊢; omega
          used_lt := hinv.used_lt
          keys_nd := hinv.keys_nd
          vals_nd := hinv.vals_nd
          pairs_ok := hinv.pairs_ok
          keys_sub := fun p hp => List.mem_append_left _ (hinv.keys_sub p hp)
          covered := fun l hl hnone => by
            rcases List.mem_append.mp hl with hlS | hlB
            · exact hinv.covered l hlS hnone
            · simp only [List.mem_singleton] at hlB; subst hlB
              rw [hlu] at hnone; cases hnone }
      simpa [List.append_assoc] using
        buildStep_foldl base startNat rest (seen ++ [blk.label])
          ⟨cand, used, pairs⟩ hnd' hinvNext
    | none =>
      have hnot_used : cand ∉ used := fun hm => Nat.lt_irrefl _ (hinv.used_lt cand hm)
      have ha : findFreshAddrAux used cand (used.length + 1) = cand :=
        findFreshAddrAux_fresh used cand used.length hnot_used
      dsimp only at ha ⊢
      rw [ha]
      have hle0 : startNat ≤ cand.toNat := hinv.le_cand
      have hbound0 : cand.toNat + 8 * (rest.length + 1 + 1) < 2 ^ 64 := hinv.bound
      have hused0 : ∀ u ∈ used, u.toNat < cand.toNat := hinv.used_lt
      have hinv' : BuildStepInv base startNat (seen ++ [blk.label]) rest.length
          (cand + 8#64, cand :: used, (blk.label, cand) :: pairs) :=
        { le_cand := by dsimp; omega
          bound := by dsimp; omega
          used_lt := fun u hu => by
            dsimp at hu ⊢
            rcases List.mem_cons.mp hu with rfl | htail
            · omega
            · have := hused0 u htail; omega
          keys_nd := by
            dsimp; rw [List.map_cons, List.nodup_cons]
            exact ⟨fun hm => hlbl_not_seen (by
              obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hm
              dsimp at hpeq
              exact hpeq ▸ hinv.keys_sub p hp), hinv.keys_nd⟩
          vals_nd := by
            dsimp; rw [List.map_cons, List.nodup_cons]
            exact ⟨fun hm => by
              obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hm
              dsimp at hpeq
              have hlt := hused0 p.2 (hinv.pairs_ok p hp).2.2
              exact Nat.lt_irrefl _ (hpeq ▸ hlt), hinv.vals_nd⟩
          pairs_ok := fun p hp => by
            dsimp at hp ⊢
            rcases List.mem_cons.mp hp with rfl | htail
            · exact ⟨hlu, hle0, List.mem_cons_self⟩
            · obtain ⟨h1, h2, h3⟩ := hinv.pairs_ok p htail
              exact ⟨h1, h2, List.mem_cons_of_mem _ h3⟩
          keys_sub := fun p hp => by
            dsimp at hp
            rcases List.mem_cons.mp hp with rfl | htail
            · simp
            · exact List.mem_append_left _ (hinv.keys_sub p htail)
          covered := fun l hl hnone => by
            dsimp
            rcases List.mem_append.mp hl with hlS | hlB
            · obtain ⟨a, ha⟩ := hinv.covered l hlS hnone
              exact ⟨a, List.mem_cons_of_mem _ ha⟩
            · simp only [List.mem_singleton] at hlB; subst hlB
              exact ⟨cand, List.mem_cons_self⟩ }
      simpa [List.append_assoc] using
        buildStep_foldl base startNat rest (seen ++ [blk.label]) _ hnd' hinv'

private theorem lookupSymAddr_nonRaw_none (base : List (Sym × BitVec 64))
    (hBase : ∀ k ∈ base.map Prod.fst, noDblUnder k.toList = true)
    (t : TagLbl) (ht : noDblUnder t.pfx.toList = true) (hNR : ∀ s, t ≠ .raw s) :
    lookupSymAddr base t.toStr = none := by
  induction base with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨k, v⟩
    have hk := hBase k List.mem_cons_self
    have hps : ∀ k' ∈ ps.map Prod.fst, noDblUnder k'.toList = true :=
      fun k' hk' => hBase k' (List.mem_cons_of_mem _ hk')
    dsimp only [lookupSymAddr]
    have hne : k ≠ t.toStr := by
      intro heq
      have hl := congrArg String.toList heq
      cases t with
      | raw s => exact hNR s rfl
      | pc s n =>
        dsimp only [TagLbl.toStr] at hl; rw [pc_str_toList] at hl
        exact tagLbl_toStr_ne_raw hk ht hl
      | aux s n =>
        dsimp only [TagLbl.toStr] at hl; rw [aux_str_toList] at hl
        exact tagLbl_toStr_ne_raw hk ht hl
    simp [beq_false_of_ne hne, ih hps]

theorem nodup_of_listNodup {α : Type} [DecidableEq α] :
    ∀ {xs : List α}, listNodup xs = true → xs.Nodup
  | [], _ => .nil
  | x :: xs, h => by
    simp only [listNodup, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr
      ⟨fun hm => Bool.false_ne_true (h.1.symm.trans (List.contains_iff_mem.mpr hm)),
       nodup_of_listNodup h.2⟩

private theorem contains_of_mem_beq {α : Type} [BEq α] {x d : α} :
    ∀ {xs : List α}, x ∈ xs → (d == x) = true → xs.contains d = true
  | [], hx, _ => by cases hx
  | y :: ys, hx, he => by
    dsimp only [List.contains, List.elem]
    rcases List.mem_cons.mp hx with rfl | htail
    · simp [he]
    · cases hdy : d == y
      · exact contains_of_mem_beq htail he
      · rfl

private theorem nodup_getElem_inj {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} (hi : i < xs.length) (hj : j < xs.length),
      xs[i] = xs[j] → i = j
  | [], _, _, _, _, hi, _ => by cases hi
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, _, hj, he => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at he
    exact absurd (he ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)) hnd.1
  | x :: xs, hnd, i + 1, 0, hi, _, he => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at he
    exact absurd (he.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)) hnd.1
  | _ :: xs, hnd, i + 1, j + 1, hi, hj, he => by
    rw [List.nodup_cons] at hnd
    exact congrArg Nat.succ
      (nodup_getElem_inj hnd.2 (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) he)

private theorem nodup_of_map {α β : Type} (f : α → β) :
    ∀ {xs : List α}, (xs.map f).Nodup → xs.Nodup
  | [], _ => .nil
  | x :: xs, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    exact List.nodup_cons.mpr ⟨fun hm => hnd.1 (List.mem_map.mpr ⟨x, hm, rfl⟩),
      nodup_of_map f hnd.2⟩

private theorem lookupSymAddr_memL {pairs : List (Sym × BitVec 64)} {s : Sym} {a : BitVec 64}
    (hn : (pairs.map Prod.fst).Nodup) (hm : (s, a) ∈ pairs) :
    lookupSymAddr pairs s = some a := by
  induction pairs with
  | nil => cases hm
  | cons p ps ih =>
    rcases p with ⟨k, v⟩
    rw [List.map_cons, List.nodup_cons] at hn
    dsimp only [lookupSymAddr]
    rcases List.mem_cons.mp hm with hEq | hTail
    · cases hEq; simp
    · have hne : k ≠ s := fun e => hn.1 (e ▸ List.mem_map.mpr ⟨(s, a), hTail, rfl⟩)
      simp [beq_false_of_ne hne, ih hn.2 hTail]

private theorem lookupSymAddr_appendL (p₁ p₂ : List (Sym × BitVec 64)) (s : Sym) :
    lookupSymAddr (p₁ ++ p₂) s = (lookupSymAddr p₁ s).orElse fun _ => lookupSymAddr p₂ s := by
  induction p₁ with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨k, v⟩
    dsimp only [List.cons_append, lookupSymAddr]
    cases h : k == s <;> simp [ih]

private theorem rawVcm_finalize_ok {cm : CodeMap} {wit : ContifyWitness}
    (blks : List (Block arm64Arch)) (ts : List TagLbl)
    (hLbls : blks.map Block.label = ts.map TagLbl.toStr)
    (hOk : ts.all TagLbl.pfxOk = true) (hNd : ts.Nodup)
    (hRaw : ∀ t ∈ ts, ∀ s, t = .raw s → s ∈ wit.regions.map (fun cr => cr.name))
    (hBaseOk : (wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++
        cm.map fun e => (e.name, e.addr)).all
        (fun p => noDblUnder p.1.toList) = true)
    (hRegAddrs : (wit.regions.map (fun cr => cr.entryPc)).Nodup)
    (hRegNames : (wit.regions.map (fun cr => cr.name)).Nodup)
    (hBound : ((((wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++
        cm.map fun e => (e.name, e.addr)).map Prod.snd).foldl
        (fun m a => Nat.max m a.toNat) 0 + 64 + 7) / 8) * 8 +
        8 * (blks.length + 1) < 2 ^ 64)
    (hPads : (VllCodeMap.mk blks
        (buildVllSymAddr
          (wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++
            (cm.map fun e => (e.name, e.addr))) blks)
        (wit.regions.map (fun cr => cr.name))).padsOk = true) :
    let base := wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++
      (cm.map fun e => (e.name, e.addr))
    let vcm : VllCodeMap arm64Arch :=
      VllCodeMap.mk blks (buildVllSymAddr base blks) (wit.regions.map (fun cr => cr.name))
    finalizeVllCodeMap vcm = .ok vcm := by
  intro base vcm
  have hLblNd : (blks.map Block.label).Nodup := by
    rw [hLbls]
    refine nodup_map_of_inj hNd fun t₁ ht1 t₂ ht2 he =>
      tagLbl_toStr_inj (List.all_eq_true.mp hOk t₁ ht1)
        (List.all_eq_true.mp hOk t₂ ht2) he
  have hLU : vcm.labelsUnique = true := labelsUnique_go_of_nodup hLblNd
  have hBaseFst : ∀ k ∈ base.map Prod.fst, noDblUnder k.toList = true := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
    exact List.all_eq_true.mp hBaseOk p hp
  let usedInit := base.map Prod.snd
  let maxNat := usedInit.foldl (fun m a => Nat.max m a.toNat) 0
  let startNat := ((maxNat + 64 + 7) / 8) * 8
  have hStartLt : startNat < 2 ^ 64 := by
    dsimp [startNat, maxNat, usedInit, base]
    omega
  have hCandToNat : (BitVec.ofNat 64 startNat).toNat = startNat := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hStartLt
  have hUsedLt : ∀ u ∈ usedInit, u.toNat < (BitVec.ofNat 64 startNat).toNat := fun u hu => by
    rw [hCandToNat]
    have hle := (foldl_max_le usedInit 0).2 u hu
    change u.toNat ≤ maxNat at hle
    dsimp [startNat]; omega
  have hInit : BuildStepInv base startNat [] blks.length
      (BitVec.ofNat 64 startNat, usedInit, []) :=
    { le_cand := by dsimp; rw [hCandToNat]; exact Nat.le_refl _
      bound := by dsimp; rw [hCandToNat]; exact hBound
      used_lt := hUsedLt
      keys_nd := .nil
      vals_nd := .nil
      pairs_ok := fun _ h => by cases h
      keys_sub := fun _ h => by cases h
      covered := fun _ h _ => by cases h }
  have hDone := buildStep_foldl base startNat blks []
    (BitVec.ofNat 64 startNat, usedInit, []) (by simpa using hLblNd) hInit
  let stepRes := blks.foldl
    (fun (st : BitVec 64 × List (BitVec 64) × List (Sym × BitVec 64)) blk =>
      let (cand, used, pairs) := st
      match lookupSymAddr base blk.label with
      | some _ => st
      | none =>
        let a := findFreshAddrAux used cand (used.length + 1)
        (a + 8#64, a :: used, (blk.label, a) :: pairs))
    (BitVec.ofNat 64 startNat, usedInit, [])
  change BuildStepInv base startNat ([] ++ blks.map Block.label) 0 stepRes at hDone
  have hBaseMapNonRaw : ∀ b ∈ blks, ∀ a, lookupSymAddr base b.label = some a →
      ∃ cr ∈ wit.regions, b.label = cr.name ∧ a = cr.entryPc := by
    intro blk hb a hlu
    have hlmem : blk.label ∈ ts.map TagLbl.toStr := by
      rw [← hLbls]; exact List.mem_map.mpr ⟨blk, hb, rfl⟩
    obtain ⟨t, ht, hteq⟩ := List.mem_map.mp hlmem
    cases t with
    | raw s =>
      have hs : s ∈ wit.regions.map (fun cr => cr.name) := hRaw (.raw s) ht s rfl
      obtain ⟨cr, hcr, hcrNm⟩ := List.mem_map.mp hs
      have hLookReg : lookupSymAddr (wit.regions.map fun c => (c.name, c.entryPc)) cr.name =
          some cr.entryPc :=
        lookupSymAddr_memL (by simpa [Function.comp_def] using hRegNames)
          (List.mem_map.mpr ⟨cr, hcr, rfl⟩)
      have hBaseEq : lookupSymAddr base cr.name = some cr.entryPc := by
        dsimp only [base]
        rw [lookupSymAddr_appendL, hLookReg]
        rfl
      dsimp only [TagLbl.toStr] at hteq
      rw [← hteq, ← hcrNm, hBaseEq] at hlu
      cases hlu
      exact ⟨cr, hcr, hteq.symm.trans hcrNm.symm, rfl⟩
    | pc s n =>
      have htOk := List.all_eq_true.mp hOk (.pc s n) ht
      rw [TagLbl.pfxOk, Bool.and_eq_true] at htOk
      rw [← hteq, lookupSymAddr_nonRaw_none base hBaseFst (.pc s n) htOk.1
        (fun _ h => by cases h)] at hlu
      cases hlu
    | aux s n =>
      have htOk := List.all_eq_true.mp hOk (.aux s n) ht
      rw [TagLbl.pfxOk, Bool.and_eq_true] at htOk
      rw [← hteq, lookupSymAddr_nonRaw_none base hBaseFst (.aux s n) htOk.1
        (fun _ h => by cases h)] at hlu
      cases hlu
  have hSymInj : ∀ b₁ ∈ blks, ∀ b₂ ∈ blks,
      vcm.symAddr b₁.label = vcm.symAddr b₂.label → b₁ = b₂ := by
    intro b₁ hb1 b₂ hb2 heq
    have hlblEq : b₁.label = b₂.label := by
      dsimp only [vcm, buildVllSymAddr] at heq
      cases h1 : lookupSymAddr base b₁.label with
      | some a₁ =>
        cases h2 : lookupSymAddr base b₂.label with
        | some a₂ =>
          rw [h1, h2] at heq
          obtain ⟨cr₁, hcr1, hl1, ha1⟩ := hBaseMapNonRaw b₁ hb1 a₁ h1
          obtain ⟨cr₂, hcr2, hl2, ha2⟩ := hBaseMapNonRaw b₂ hb2 a₂ h2
          subst ha1; subst ha2
          obtain ⟨i₁, hi1, rfl⟩ := List.getElem_of_mem hcr1
          obtain ⟨i₂, hi2, rfl⟩ := List.getElem_of_mem hcr2
          have hii : i₁ = i₂ := nodup_getElem_inj hRegAddrs (by simp [hi1]) (by simp [hi2])
            (by simpa using heq)
          subst hii; exact hl1.trans hl2.symm
        | none =>
          rw [h1, h2] at heq
          obtain ⟨a₂, ha2⟩ := hDone.covered b₂.label
            (List.mem_append_right _ (List.mem_map.mpr ⟨b₂, hb2, rfl⟩)) h2
          have hlku2 := lookupSymAddr_memL hDone.keys_nd ha2
          change _ = Option.getD (lookupSymAddr stepRes.2.2 b₂.label) 0#64 at heq
          rw [hlku2] at heq
          dsimp only [Option.getD] at heq
          have ha1Lt : a₁.toNat < startNat := by
            obtain ⟨cr₁, hcr1, _, ha1⟩ := hBaseMapNonRaw b₁ hb1 a₁ h1
            have hmU : cr₁.entryPc ∈ usedInit := List.mem_map.mpr
              ⟨(cr₁.name, cr₁.entryPc),
                List.mem_append_left _ (List.mem_map.mpr ⟨cr₁, hcr1, rfl⟩), rfl⟩
            have := hUsedLt cr₁.entryPc hmU
            rw [hCandToNat] at this; exact ha1 ▸ this
          have ha2Ge := (hDone.pairs_ok _ ha2).2.1
          dsimp only at ha2Ge
          rw [heq] at ha1Lt; omega
      | none =>
        cases h2 : lookupSymAddr base b₂.label with
        | some a₂ =>
          rw [h1, h2] at heq
          obtain ⟨a₁, ha1⟩ := hDone.covered b₁.label
            (List.mem_append_right _ (List.mem_map.mpr ⟨b₁, hb1, rfl⟩)) h1
          have hlku1 := lookupSymAddr_memL hDone.keys_nd ha1
          change Option.getD (lookupSymAddr stepRes.2.2 b₁.label) 0#64 = _ at heq
          rw [hlku1] at heq
          dsimp only [Option.getD] at heq
          have ha2Lt : a₂.toNat < startNat := by
            obtain ⟨cr₂, hcr2, _, ha2⟩ := hBaseMapNonRaw b₂ hb2 a₂ h2
            have hmU : cr₂.entryPc ∈ usedInit := List.mem_map.mpr
              ⟨(cr₂.name, cr₂.entryPc),
                List.mem_append_left _ (List.mem_map.mpr ⟨cr₂, hcr2, rfl⟩), rfl⟩
            have := hUsedLt cr₂.entryPc hmU
            rw [hCandToNat] at this; exact ha2 ▸ this
          have ha1Ge := (hDone.pairs_ok _ ha1).2.1
          dsimp only at ha1Ge
          rw [← heq] at ha2Lt; omega
        | none =>
          rw [h1, h2] at heq
          obtain ⟨a₁, ha1⟩ := hDone.covered b₁.label
            (List.mem_append_right _ (List.mem_map.mpr ⟨b₁, hb1, rfl⟩)) h1
          obtain ⟨a₂, ha2⟩ := hDone.covered b₂.label
            (List.mem_append_right _ (List.mem_map.mpr ⟨b₂, hb2, rfl⟩)) h2
          change Option.getD (lookupSymAddr stepRes.2.2 b₁.label) 0#64 =
            Option.getD (lookupSymAddr stepRes.2.2 b₂.label) 0#64 at heq
          rw [lookupSymAddr_memL hDone.keys_nd ha1, lookupSymAddr_memL hDone.keys_nd ha2] at heq
          dsimp only [Option.getD] at heq
          subst heq
          obtain ⟨i₁, hi1, he1⟩ := List.getElem_of_mem ha1
          obtain ⟨i₂, hi2, he2⟩ := List.getElem_of_mem ha2
          have hii : i₁ = i₂ := nodup_getElem_inj hDone.vals_nd (by simp [hi1]) (by simp [hi2])
            (by simp [he1, he2])
          have hpEq : stepRes.2.2[i₁] = stepRes.2.2[i₂] := by subst hii; rfl
          rw [he1, he2] at hpEq
          exact (Prod.mk.inj hpEq).1
    obtain ⟨i₁, hi1, he1⟩ := List.getElem_of_mem hb1
    obtain ⟨i₂, hi2, he2⟩ := List.getElem_of_mem hb2
    have hii : i₁ = i₂ := nodup_getElem_inj hLblNd (by simp [hi1]) (by simp [hi2])
      (by simp [he1, he2, hlblEq])
    subst hii; exact he1.symm.trans he2
  have hANd : (vcm.blocks.map fun blk => vcm.symAddr blk.label).Nodup :=
    nodup_map_of_inj (nodup_of_map Block.label hLblNd)
      (fun b₁ hb1 b₂ hb2 heq => hSymInj b₁ hb1 b₂ hb2 heq)
  have hAU : vcm.addrsUnique = true := addrsUnique_go_of_nodup hANd
  dsimp only [finalizeVllCodeMap]
  rw [hLU, hAU, hPads]
  rfl

private theorem rawContVcm_ok {cm : CodeMap} {wit : ContifyWitness}
    {items : List (ContifyRegion × List (BitVec 64) × Nat × Bool)}
    (hOkRun : isOkBool ((items.mapM fun x =>
      lowerContRegionFast armWordBind cm x.1 x.2.1 x.2.2.1 x.2.2.2).run 0) = true)
    (ts : List TagLbl)
    (hLbls : (rawContVcm armWordBind cm wit items).blocks.map Block.label = ts.map TagLbl.toStr)
    (hOk : ts.all TagLbl.pfxOk = true) (hNd : listNodup ts = true)
    (hRaw : ts.all (fun t => match t with
      | .raw s => (wit.regions.map (fun cr => cr.name)).contains s | _ => true) = true)
    (hBaseOk : (wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++
        cm.map fun e => (e.name, e.addr)).all
        (fun p => noDblUnder p.1.toList) = true)
    (hRegAddrs : listNodup (wit.regions.map (fun cr => cr.entryPc)) = true)
    (hRegNames : listNodup (wit.regions.map (fun cr => cr.name)) = true)
    (maxPc nBlocks : Nat)
    (hMaxEq : (((wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++
        cm.map fun e => (e.name, e.addr)).map Prod.snd).foldl
        (fun m a => Nat.max m a.toNat) 0) = maxPc)
    (hLenEq : (rawContVcm armWordBind cm wit items).blocks.length = nBlocks)
    (hBound : ((maxPc + 64 + 7) / 8) * 8 + 8 * (nBlocks + 1) < 2 ^ 64)
    (hPads : (rawContVcm armWordBind cm wit items).padsOk = true) :
    fastFromWordContify armWordBind cm wit items =
      .ok (rawContVcm armWordBind cm wit items) := by
  have hRaw' : ∀ t ∈ ts, ∀ s, t = .raw s → s ∈ wit.regions.map (fun cr => cr.name) := by
    intro t ht s hteq
    have h1 := List.all_eq_true.mp hRaw t ht
    rw [hteq] at h1
    exact List.contains_iff_mem.mp h1
  have hBound' : ((((wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++
      cm.map fun e => (e.name, e.addr)).map Prod.snd).foldl
      (fun m a => Nat.max m a.toNat) 0 + 64 + 7) / 8) * 8 +
      8 * ((rawContVcm armWordBind cm wit items).blocks.length + 1) < 2 ^ 64 := by
    rw [hMaxEq, hLenEq]; exact hBound
  cases hRun : (items.mapM fun x =>
      lowerContRegionFast armWordBind cm x.1 x.2.1 x.2.2.1 x.2.2.2).run 0 with
  | error e => simp [hRun, isOkBool] at hOkRun
  | ok p =>
    dsimp only [fastFromWordContify, rawContVcm, rawFromWordContify, unwrapVcm] at *
    rw [hRun] at hLbls hBound' hPads ⊢
    dsimp only [Except.bind, Bind.bind, Pure.pure, Except.pure] at hLbls hBound' hPads ⊢
    exact rawVcm_finalize_ok p.1.flatten ts hLbls hOk (nodup_of_listNodup hNd) hRaw'
      hBaseOk (nodup_of_listNodup hRegAddrs) (nodup_of_listNodup hRegNames) hBound' hPads

private theorem block_mem_flattenBlocks_toInstrs {A : Arch} :
    ∀ (bs : List (Block A)) {b : Block A},
      b ∈ bs → ∃ nl?, ∀ i ∈ b.toInstrs nl?, i ∈ flattenBlocks bs
  | [], _, hb => nomatch hb
  | b0 :: rest, b, hb => by
    cases rest with
    | nil =>
      simp only [List.mem_singleton] at hb; subst hb
      exact ⟨none, fun i hi => by simpa [flattenBlocks] using hi⟩
    | cons bNext rs =>
      rcases List.mem_cons.mp hb with rfl | htail
      · exact ⟨some bNext.label, fun i hi => by
          rw [flattenBlocks]; exact List.mem_append_left _ hi⟩
      · obtain ⟨nl?, hmem⟩ := block_mem_flattenBlocks_toInstrs (bNext :: rs) htail
        exact ⟨nl?, fun i hi => by
          rw [flattenBlocks]; exact List.mem_append_right _ (hmem i hi)⟩

private theorem mem_flattenBlocks_body {A : Arch} {bs : List (Block A)} {b : Block A}
    (hb : b ∈ bs) {i : Instr A} (hi : i ∈ b.body) : i ∈ flattenBlocks bs := by
  obtain ⟨nl?, hmem⟩ := block_mem_flattenBlocks_toInstrs bs hb
  refine hmem i ?_
  cases hpad : b.pad? <;> simp [Block.toInstrs, hpad, hi]

private theorem call_mem_flattenBlocks {A : Arch} {bs : List (Block A)} {b : Block A}
    (hb : b ∈ bs) {sym retL : Sym} (ht : b.term = .call sym retL) :
    .call sym ∈ flattenBlocks bs := by
  obtain ⟨nl?, hmem⟩ := block_mem_flattenBlocks_toInstrs bs hb
  refine hmem _ ?_
  cases hpad : b.pad? <;> simp [Block.toInstrs, hpad, ht, Term.toInstrs]

private theorem ret_mem_flattenBlocks {A : Arch} {bs : List (Block A)} {b : Block A}
    (hb : b ∈ bs) (ht : b.term = .ret) :
    .ret ∈ flattenBlocks bs := by
  obtain ⟨nl?, hmem⟩ := block_mem_flattenBlocks_toInstrs bs hb
  refine hmem _ ?_
  cases hpad : b.pad? <;> simp [Block.toInstrs, hpad, ht, Term.toInstrs]

@[expose] def flatAddrOf {A : Arch} (vcm : VllCodeMap A) (k : Nat) : BitVec 64 :=
  match vcm.flatten[k]? with
  | some (.label l) => vcm.symAddr l
  | _ => 0xF000_0000#64 + BitVec.ofNat 64 k

@[expose] def checkFlattenStep {A : Arch} : List (Block A) → Bool
  | [] => true
  | [b] =>
    b.body.all (fun i => !i.isControl && !i.isNative) &&
    match b.term with | .call _ _ | .icall _ _ | .nativeTerm _ => false | _ => true
  | b :: bNext :: rest =>
    b.body.all (fun i => !i.isControl && !i.isNative) &&
    (match b.term with
     | .call _ retL | .icall _ retL => bNext.label == retL
     | .nativeTerm _ => false
     | _ => true) &&
    checkFlattenStep (bNext :: rest)

theorem nodup_getElem?_inj' {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j : Nat} {a : α},
      xs[i]? = some a → xs[j]? = some a → i = j
  | [], _, _, _, _, hi, _ => by simp at hi
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, a, hi, hj => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    simp only [List.getElem?_cons_succ] at hj
    subst hi; exact absurd (List.mem_of_getElem? hj) hnd.1
  | x :: xs, hnd, i + 1, 0, a, hi, hj => by
    rw [List.nodup_cons] at hnd
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
    simp only [List.getElem?_cons_succ] at hi
    subst hj; exact absurd (List.mem_of_getElem? hi) hnd.1
  | _ :: xs, hnd, i + 1, j + 1, a, hi, hj => by
    rw [List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_getElem?_inj' hnd.2 hi hj)

theorem map_range_getElem? {α : Type} (f : Nat → α) :
    ∀ (n k : Nat), k < n → ((List.range n).map f)[k]? = some (f k) := by
  intro n k hk
  simp [List.getElem?_range hk]

private theorem infixAt_head_eq {α : Type} {xs ys : List α} {k : Nat} {a : α}
    (hinf : xs.IsInfixAt ys k) (hx : xs[0]? = some a) : ys[k]? = some a := by
  rcases xs with _ | ⟨x, _⟩
  · cases hx
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx
    exact (List.IsInfixAt.cons hinf).1

private theorem flattenBlocks_head? {A : Arch} (b : Block A) (rs : List (Block A)) :
    (flattenBlocks (b :: rs))[0]? = some (.label b.label) := by
  cases rs <;> simp [flattenBlocks, Block.toInstrs]

private theorem block_toInstrs_len {A : Arch} (b : Block A) (nl? : Option Sym) :
    (b.toInstrs nl?).length =
      1 + (if b.pad?.isSome then 1 else 0) + b.body.length + (b.term.toInstrs nl?).length := by
  cases h : b.pad? <;> simp [Block.toInstrs, h, List.length_append] <;> omega

private theorem flattenBlocks_mem_hosted {A : Arch} (vcm : VllCodeMap A) (addrOf : Nat → BitVec 64)
    (hLbl : ∀ k l, vcm.flatten[k]? = some (.label l) → addrOf k = vcm.symAddr l) :
    ∀ (bs : List (Block A)) (base : Nat),
      (flattenBlocks bs).IsInfixAt vcm.flatten base →
      checkFlattenStep bs = true →
      ∀ b ∈ bs,
        (∀ i ∈ b.body, !i.isControl && !i.isNative = true) ∧
        ∃ k nl?, addrOf k = vcm.symAddr b.label ∧ (b.toInstrs nl?).IsInfixAt vcm.flatten k ∧
          (let kTerm := k + 1 + (if b.pad?.isSome then 1 else 0) + b.body.length
           match b.term with
           | .fall n => nl? = some n → addrOf kTerm = vcm.symAddr n
           | .jmp l => nl? = some l → addrOf kTerm = vcm.symAddr l
           | .jcc _ _ f | .jnzGpr _ _ f => nl? = some f → addrOf (kTerm + 1) = vcm.symAddr f
           | .call _ retL | .icall _ retL =>
             nl? = some retL ∧ addrOf (kTerm + 1) = vcm.symAddr retL
           | .nativeTerm _ => False
           | _ => True)
  | [], _, _, _, _, hb => nomatch hb
  | b0 :: rest, base, hinf, hchk, b, hb => by
    cases rest with
    | nil =>
      simp only [List.mem_singleton] at hb; subst hb
      simp only [checkFlattenStep, Bool.and_eq_true] at hchk
      have hBody : ∀ i ∈ b.body, !i.isControl && !i.isNative = true :=
        List.all_eq_true.mp hchk.1
      have hinf0 : (b.toInstrs none).IsInfixAt vcm.flatten base := by
        simpa [flattenBlocks] using hinf
      obtain ⟨hl0, _⟩ := List.IsInfixAt.cons (by simpa [Block.toInstrs] using hinf0)
      refine ⟨hBody, base, none, hLbl base b.label hl0, hinf0, ?_⟩
      cases ht : b.term <;> simp only [ht] at hchk <;> simp <;> cases hchk.2
    | cons bNext rs =>
      simp only [checkFlattenStep, Bool.and_eq_true] at hchk
      have hBody0 : ∀ i ∈ b0.body, !i.isControl && !i.isNative = true :=
        List.all_eq_true.mp hchk.1.1
      have hinfCat : (b0.toInstrs (some bNext.label) ++
          flattenBlocks (bNext :: rs)).IsInfixAt vcm.flatten base := by
        simpa [flattenBlocks] using hinf
      obtain ⟨hinfB, hinfRest⟩ := List.IsInfixAt.append hinfCat
      rcases List.mem_cons.mp hb with hbEq | hbTail
      · have hB0Res : (∀ i ∈ b0.body, !i.isControl && !i.isNative = true) ∧
          ∃ k nl?, addrOf k = vcm.symAddr b0.label ∧
            (b0.toInstrs nl?).IsInfixAt vcm.flatten k ∧
            (let kTerm := k + 1 + (if b0.pad?.isSome then 1 else 0) + b0.body.length
             match b0.term with
             | .fall n => nl? = some n → addrOf kTerm = vcm.symAddr n
             | .jmp l => nl? = some l → addrOf kTerm = vcm.symAddr l
             | .jcc _ _ f | .jnzGpr _ _ f => nl? = some f → addrOf (kTerm + 1) = vcm.symAddr f
             | .call _ retL | .icall _ retL =>
               nl? = some retL ∧ addrOf (kTerm + 1) = vcm.symAddr retL
             | .nativeTerm _ => False
             | _ => True) := by
          obtain ⟨hl0, _⟩ := List.IsInfixAt.cons (by simpa [Block.toInstrs] using hinfB)
          have hNextLbl : vcm.flatten[base + (b0.toInstrs (some bNext.label)).length]? =
              some (.label bNext.label) :=
            infixAt_head_eq hinfRest (flattenBlocks_head? bNext rs)
          have hNextAddr : addrOf (base + (b0.toInstrs (some bNext.label)).length) =
              vcm.symAddr bNext.label := hLbl _ _ hNextLbl
          refine ⟨hBody0, base, some bNext.label, hLbl base b0.label hl0, hinfB, ?_⟩
          dsimp only
          have hLen := block_toInstrs_len b0 (some bNext.label)
          cases ht : b0.term with
          | fall n =>
            intro hn; cases hn
            simp [ht, Term.toInstrs] at hLen
            rw [show base + 1 + (if b0.pad?.isSome then 1 else 0) + b0.body.length =
              base + (b0.toInstrs (some bNext.label)).length by omega]
            exact hNextAddr
          | jmp l =>
            intro hl; cases hl
            simp [ht, Term.toInstrs] at hLen
            rw [show base + 1 + (if b0.pad?.isSome then 1 else 0) + b0.body.length =
              base + (b0.toInstrs (some bNext.label)).length by omega]
            exact hNextAddr
          | jcc c t f =>
            intro hf; cases hf
            simp [ht, Term.toInstrs] at hLen
            rw [show base + 1 + (if b0.pad?.isSome then 1 else 0) + b0.body.length + 1 =
              base + (b0.toInstrs (some bNext.label)).length by omega]
            exact hNextAddr
          | jnzGpr r t f =>
            intro hf; cases hf
            simp [ht, Term.toInstrs] at hLen
            rw [show base + 1 + (if b0.pad?.isSome then 1 else 0) + b0.body.length + 1 =
              base + (b0.toInstrs (some bNext.label)).length by omega]
            exact hNextAddr
          | call sym retL =>
            rw [ht] at hchk
            have hEqL : bNext.label = retL := beq_iff_eq.mp hchk.1.2
            subst hEqL
            simp [ht, Term.toInstrs] at hLen
            refine ⟨rfl, ?_⟩
            rw [show base + 1 + (if b0.pad?.isSome then 1 else 0) + b0.body.length + 1 =
              base + (b0.toInstrs (some bNext.label)).length by omega]
            exact hNextAddr
          | icall r retL =>
            rw [ht] at hchk
            have hEqL : bNext.label = retL := beq_iff_eq.mp hchk.1.2
            subst hEqL
            simp [ht, Term.toInstrs] at hLen
            refine ⟨rfl, ?_⟩
            rw [show base + 1 + (if b0.pad?.isSome then 1 else 0) + b0.body.length + 1 =
              base + (b0.toInstrs (some bNext.label)).length by omega]
            exact hNextAddr
          | nativeTerm _ => simp [ht] at hchk
          | ret | exitJmp _ | tailJmpR _ | ijmp _ | halt _ => trivial
        exact hbEq ▸ hB0Res
      · exact flattenBlocks_mem_hosted vcm addrOf hLbl (bNext :: rs)
          (base + (b0.toInstrs (some bNext.label)).length) hinfRest hchk.2 b hbTail

@[expose] def mkFlatHost (vcm : VllCodeMap arm64Arch)
    (hInj : ((List.range vcm.flatten.length).map (flatAddrOf vcm)).Nodup) :
    VllHost arm64Arch where
  prog := vcm.flatten
  addrOf := flatAddrOf vcm
  labelAddr := vcm.symAddr
  addrOf_inj {i j} hi hj heq := nodup_getElem?_inj' hInj
    (map_range_getElem? (flatAddrOf vcm) vcm.flatten.length i hi)
    (heq ▸ map_range_getElem? (flatAddrOf vcm) vcm.flatten.length j hj)
  labelAddr_wf {k l} hk _ := by simp [flatAddrOf, hk]

theorem mkFlatHost_hosted (vcm : VllCodeMap arm64Arch)
    (hInj : ((List.range vcm.flatten.length).map (flatAddrOf vcm)).Nodup)
    (hStep : checkFlattenStep vcm.blocks = true) :
    vcm.Hosted (mkFlatHost vcm hInj) where
  labelAddr_eq _ := rfl
  blocks_ok b hb := flattenBlocks_mem_hosted vcm (flatAddrOf vcm)
    (fun k l hk => by simp [flatAddrOf, hk]) vcm.blocks 0 ⟨[], List.append_nil _⟩ hStep b hb

/-! ## §3. Example 1 (`cmEx1`): Open `fromWord`, `asmArm64`, XCAP & Hosted `vllStep` -/

@[expose] def vcmEx1 : VllCodeMap arm64Arch := unwrapVcm (fromWord armWordBind cmEx1)

theorem ex1_fromWord_ok : fromWord armWordBind cmEx1 = .ok vcmEx1 :=
  except_ok_of_isOkBool (by rfl)

theorem ex1_padsOk : vcmEx1.padsOk = true := by rfl
theorem ex1_asm_has_nop :
    (asmArm64CodeMap vcmEx1).contains (ins (w := .W64) .NOP) = true := by rfl
theorem ex1_hostedStep_ok : checkFlattenStep vcmEx1.blocks = true := by rfl
theorem ex1_inj_ok :
    listNodup ((List.range vcmEx1.flatten.length).map (flatAddrOf vcmEx1)) = true := by
  rfl

@[expose] def hostEx1 : VllHost arm64Arch :=
  mkFlatHost vcmEx1 (nodup_of_listNodup ex1_inj_ok)

theorem ex1_hosted : vcmEx1.Hosted hostEx1 :=
  mkFlatHost_hosted vcmEx1 _ ex1_hostedStep_ok

theorem ex1_vll_wp_fast (r₀ : Regs) (m : Mem 64) (h1 : r₀.r1 = 0#64) (h2 : r₀.r2 = 32#64)
    {s : MachSt arm64Arch} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel armWordBind ⟨r₀, m⟩ (codeMapMaxBudget armWordBind cmEx1)
      (fun _ => True) s)
    (hanc : codeMapMaxBudget armWordBind cmEx1 > 0 →
      (vllFramePreds arm64Arch).raReg s ra0 ∧
      (s.mem =⋆ Eq m ⋆
        hwStackMem arm64Arch (s.gpr arm64Arch.abi.sp) ra0
          (codeMapMaxBudget armWordBind cmEx1) ⋆ fun _ => True)) :
    vcmEx1.wp (plainHaltPost arm64Arch (fun c _ => c = 7#64 ∨ c = 42#64)
      (s.gpr arm64Arch.abi.sp) ra0 (codeMapMaxBudget armWordBind cmEx1) (fun _ => True)) 0#64 s :=
  fromWord_wp_sound arm64Arch_wf armWordBind_wf ex1_fromWord_ok (ex1_cm_wp_fast r₀ m h1 h2)
    hrel hanc

theorem ex1_vllStep_fast (r₀ : Regs) (m : Mem 64) (h1 : r₀.r1 = 0#64) (h2 : r₀.r2 = 32#64)
    {s : MachSt arm64Arch} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel armWordBind ⟨r₀, m⟩ (codeMapMaxBudget armWordBind cmEx1)
      (fun _ => True) s)
    (hanc : codeMapMaxBudget armWordBind cmEx1 > 0 →
      (vllFramePreds arm64Arch).raReg s ra0 ∧
      (s.mem =⋆ Eq m ⋆
        hwStackMem arm64Arch (s.gpr arm64Arch.abi.sp) ra0
          (codeMapMaxBudget armWordBind cmEx1) ⋆ fun _ => True)) :
    Eventually (vllStep hostEx1)
      (fun cfg => (cfg.data.gpr armWordBind.w0 = 7#64 ∨
        cfg.data.gpr armWordBind.w0 = 42#64)) ⟨s, 0#64⟩ := by
  refine (fromWord_hosted_vllStep arm64Arch_wf armWordBind_wf ex1_fromWord_ok ex1_hosted
    (ex1_cm_wp_fast r₀ m h1 h2) hrel hanc ?_)
  intro blk hmem r k _ s₁ hterm _ _ hH
  have hw0All : vcmEx1.blocks.all (fun b =>
      match b.term with | .halt rd => decide (rd = armWordBind.w0) | _ => true) = true := by
    t_kernel_rfl
  have hbw0 := List.all_eq_true.mp hw0All blk hmem
  rw [hterm] at hbw0
  have hr : r = armWordBind.w0 := of_decide_eq_true hbw0
  subst hr
  dsimp only [plainHaltPost] at hH
  split at hH
  · rcases hH with ⟨_, hH0, _⟩; exact hH0
  · rcases hH with ⟨_, hH0, _⟩; exact hH0

/-! ## §4. Example 2b (`cmEx2b`): Dual-Return `rp + 8` Hardware `bl`/`ret` Contification -/

@[expose] def ex2bCrProbe : ContifyRegion :=
  { name := "ex2b_probe"
    entryPc := 0#64
    abi := .contified true
    privFrame := {}
    tree := [.leaf 0#64]
    edges := [⟨0#64, [true], .contRet true⟩, ⟨0#64, [false], .contRet false⟩]
    retainFallbacks := false }

@[expose] def ex2bCrCaller : ContifyRegion :=
  { name := "ex2b_caller"
    entryPc := 8#64
    abi := .retEnvelope
    privFrame := {}
    tree := [.leaf 8#64, .leaf 16#64, .leaf 24#64]
    edges := [⟨8#64, [], .contCall "ex2b_probe" 0#64 true 16#64 (some 24#64)⟩]
    retainFallbacks := false }

@[expose] def ex2bCw : ContifyWitness := ⟨[ex2bCrProbe, ex2bCrCaller]⟩

theorem ex2bCw_pcs_probe : ex2bCrProbe.allPcs = [0#64] := by
  simp [ContifyRegion.allPcs, ex2bCrProbe, GroupTree.allPcs]

theorem ex2bCw_pcs_caller : ex2bCrCaller.allPcs = [8#64, 16#64, 24#64] := by
  simp [ContifyRegion.allPcs, ex2bCrCaller, GroupTree.allPcs]

theorem ex2bCw_check : ex2bCw.check cmEx2b = true := by
  dsimp only [ex2bCw, ContifyWitness.check, ContifyWitness.checkAux, ContifyRegion.check,
    ContifyRegion.toCalleeMeta?]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ex2bCw_pcs_probe, ex2bCw_pcs_caller]
  t_kernel_rfl

theorem ex2bCw_res_eq : residualContifyCodeMap cmEx2b ex2bCw = [] := by
  have h1 : List.flatMap ContifyRegion.allPcs
      (List.filter (fun r => !r.retainFallbacks) ex2bCw.regions) =
      [0#64, 8#64, 16#64, 24#64] := by
    simp [ex2bCw, ex2bCrProbe, ex2bCrCaller, ContifyRegion.allPcs, GroupTree.allPcs]
  dsimp only [residualContifyCodeMap]
  rw [h1]
  simp [cmEx2b, mkEntry]

@[expose] def ex2bItems : List (ContifyRegion × List (BitVec 64) × Nat × Bool) :=
  [(ex2bCrProbe, [0#64], 0, false), (ex2bCrCaller, [8#64, 16#64, 24#64], 0, true)]

@[expose] def ex2bTags : List TagLbl :=
  [ .raw "ex2b_probe",
    .pc "ex2b_probe" 0,
    .aux "ex2b_probe" 0,
    .aux "ex2b_probe" 1,
    .raw "ex2b_caller",
    .pc "ex2b_caller" 8,
    .aux "ex2b_caller" 2,
    .pc "ex2b_caller" 16,
    .pc "ex2b_caller" 24 ]

@[expose] def vcmEx2b : VllCodeMap arm64Arch :=
  rawContVcm armWordBind cmEx2b ex2bCw ex2bItems

theorem ex2b_fromWordContify_ok : fromWordContify armWordBind cmEx2b ex2bCw = .ok vcmEx2b := by
  refine (fromWordContify_eq_fast armWordBind cmEx2b ex2bCw ex2bItems rfl
    (by t_kernel_rfl) ex2bCw_check ex2bCw_res_eq ?_).trans
    (rawContVcm_ok (by t_kernel_rfl) ex2bTags (by t_kernel_rfl) (by t_kernel_rfl)
      (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)
      (by t_kernel_rfl) 24 9 (by t_kernel_rfl) (by t_kernel_rfl) (by decide)
      (by t_kernel_rfl))
  intro x hx
  simp only [ex2bItems, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · refine ⟨ex2bCw_pcs_probe, ?_, ?_⟩ <;>
    · dsimp only [regionFrameSlots, regionNeedFrame, regionMaxDepth]
      simp only [ex2bCw_pcs_probe]; t_kernel_rfl
  · refine ⟨ex2bCw_pcs_caller, ?_, ?_⟩ <;>
    · dsimp only [regionFrameSlots, regionNeedFrame, regionMaxDepth]
      simp only [ex2bCw_pcs_caller]; t_kernel_rfl

open Kraken.AArch64.Parser in
theorem ex2b_asm_has_bl_ret :
    ⸨prog| bl ex2b_probe ⸩.all (asmArm64CodeMap vcmEx2b).contains = true ∧
    ⸨prog| ret ⸩.all (asmArm64CodeMap vcmEx2b).contains = true := by
  have hCallB : (vcmEx2b.blocks.any fun b =>
      match b.term with | .call "ex2b_probe" _ => true | _ => false) = true := by
    t_kernel_rfl
  have hRetB : (vcmEx2b.blocks.any fun b =>
      match b.term with | .ret => true | _ => false) = true := by
    t_kernel_rfl
  obtain ⟨bc, hbc, htc⟩ := List.any_eq_true.mp hCallB
  obtain ⟨br, hbr, htr⟩ := List.any_eq_true.mp hRetB
  have hCallMem : Instr.call "ex2b_probe" ∈ vcmEx2b.flatten := by
    cases ht : bc.term with
    | call s _ =>
      rw [ht] at htc
      by_cases hs : s = "ex2b_probe"
      · subst hs; exact call_mem_flattenBlocks hbc ht
      · simp [hs] at htc
    | _ => simp [ht] at htc
  have hRetMem : (Instr.ret : Instr arm64Arch) ∈ vcmEx2b.flatten := by
    cases ht : br.term <;> simp [ht] at htr
    exact ret_mem_flattenBlocks hbr ht
  have hBlRefl : ⸨prog| bl ex2b_probe ⸩.all (fun d => d == d) = true := by decide
  have hRetRefl : ⸨prog| ret ⸩.all (fun d => d == d) = true := by decide
  constructor
  · apply List.all_eq_true.mpr
    intro d hd
    have hd1 : d ∈ asmArm64 (.call "ex2b_probe") := by
      have heq : ⸨prog| bl ex2b_probe ⸩ = asmArm64 (.call "ex2b_probe") := rfl
      exact heq ▸ hd
    exact contains_of_mem_beq (List.mem_flatMap.mpr ⟨_, hCallMem, hd1⟩)
      (List.all_eq_true.mp hBlRefl d hd)
  · apply List.all_eq_true.mpr
    intro d hd
    have hd1 : d ∈ asmArm64 .ret := by
      have heq : ⸨prog| ret ⸩ = asmArm64 .ret := rfl
      exact heq ▸ hd
    exact contains_of_mem_beq (List.mem_flatMap.mpr ⟨_, hRetMem, hd1⟩)
      (List.all_eq_true.mp hRetRefl d hd)

theorem ex2b_symAgree :
    ∀ cr ∈ ex2bCw.regions, ∀ e ∈ cmEx2b, e.name = cr.name → e.addr = cr.entryPc := by
  intro cr hcr e he hnm
  simp only [ex2bCw, List.mem_cons, List.not_mem_nil, or_false] at hcr
  simp only [cmEx2b, mkEntry, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases hcr with rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl <;>
    simp_all [ex2bCrProbe, ex2bCrCaller]

theorem ex2b_vll_wp (r₀ : Regs) (m : Mem 64) {s : MachSt arm64Arch} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel armWordBind ⟨r₀, m⟩ 32 (fun _ => True) s)
    (hanc : (vllFramePreds arm64Arch).raReg s ra0 ∧
      (s.mem =⋆ Eq m ⋆ hwStackMem arm64Arch (s.gpr arm64Arch.abi.sp) ra0 32 ⋆ fun _ => True)) :
    vcmEx2b.wp (wordHaltPost arm64Arch (fun c _ => c = (r₀.r1 - r₀.r2) ∨ c = 999#64)
      (region (s.gpr arm64Arch.abi.sp - 32#64) (32 + arm64Arch.abi.raBytes) ⋆ fun _ => True))
      8#64 s := by
  refine fromWordContify_wp_sound arm64Arch_wf armWordBind_wf ex2b_fromWordContify_ok
    ex2b_symAgree (budget := 32) ?_ (fun _ he => by rw [ex2bCw_res_eq] at he; simp at he)
    ex2bCw_res_eq (fun cr' hcr' _ => by
      simp only [ex2bCw, List.mem_cons, List.not_mem_nil, or_false] at hcr'
      rcases hcr' with rfl | rfl <;> exact Or.inr rfl)
    (fun cr' hcr' _ ew hew => by
      simp only [ex2bCw, List.mem_cons, List.not_mem_nil, or_false] at hcr'
      rcases hcr' with rfl | rfl
      · simp [ex2bCrProbe] at hew; rcases hew with rfl | rfl <;> trivial
      · simp [ex2bCrCaller] at hew; subst hew; trivial)
    (List.mem_cons_of_mem _ List.mem_cons_self) rfl (ex2b_cm_wp r₀ m) hrel (fun _ => hanc)
    (fun h => absurd h (by decide))
  intro cr hcr
  dsimp only [regionStackBudget, ex2bCw, witnessBudgets, regionFrameSlots, regionNeedFrame,
    regionMaxDepth]
  simp only [ex2bCw_pcs_probe, ex2bCw_pcs_caller]
  simp only [ex2bCw, List.mem_cons, List.not_mem_nil, or_false] at hcr
  rcases hcr with rfl | rfl <;> exact Nat.le_of_ble_eq_true (by t_kernel_rfl)

/-! ## §5. Example 6 (`cmEx6`, `ex6Wit`): `whileM` + `.contified false` + Mutual Parity -/

theorem ex6HelperCr_pcs : ex6HelperCr.allPcs = [0#64] := by
  simp [ContifyRegion.allPcs, ex6HelperCr, GroupTree.allPcs]

theorem ex6MainCr_pcs : ex6MainCr.allPcs = [8#64, 16#64, 24#64, 32#64] := by
  simp [ContifyRegion.allPcs, ex6MainCr, GroupTree.allPcs]

@[expose] def ex6Items : List (ContifyRegion × List (BitVec 64) × Nat × Bool) :=
  [(ex6HelperCr, [0#64], 0, false), (ex6MainCr, [8#64, 16#64, 24#64, 32#64], 0, true)]

@[expose] def ex6Tags : List TagLbl :=
  [ .raw "ex6_raw_step",
    .pc "ex6_raw_step" 0,
    .raw "ex6_while_even",
    .pc "ex6_while_even" 8,
    .aux "ex6_while_even" 0,
    .aux "ex6_while_even" 1,
    .pc "ex6_while_even" 16,
    .pc "ex6_while_even" 24,
    .aux "ex6_while_even" 2,
    .aux "ex6_while_even" 3,
    .pc "ex6_while_even" 32,
    .aux "ex6_while_even" 4,
    .aux "ex6_while_even" 5 ]

@[expose] def vcmEx6 : VllCodeMap arm64Arch :=
  rawContVcm armWordBind cmEx6 ex6Wit ex6Items

theorem ex6_fromWordContify_ok : fromWordContify armWordBind cmEx6 ex6Wit = .ok vcmEx6 := by
  refine (fromWordContify_eq_fast armWordBind cmEx6 ex6Wit ex6Items rfl
    (by t_kernel_rfl) ex6_check ex6_res_eq ?_).trans
    (rawContVcm_ok (by t_kernel_rfl) ex6Tags (by t_kernel_rfl) (by t_kernel_rfl)
      (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)
      (by t_kernel_rfl) 32 13 (by t_kernel_rfl) (by t_kernel_rfl) (by decide)
      (by t_kernel_rfl))
  intro x hx
  simp only [ex6Items, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · refine ⟨ex6HelperCr_pcs, ?_, ?_⟩ <;>
    · dsimp only [regionFrameSlots, regionNeedFrame, regionMaxDepth]
      simp only [ex6HelperCr_pcs]; t_kernel_rfl
  · refine ⟨ex6MainCr_pcs, ?_, ?_⟩ <;>
    · dsimp only [regionFrameSlots, regionNeedFrame, regionMaxDepth]
      simp only [ex6MainCr_pcs]; t_kernel_rfl

theorem ex6_symAgree :
    ∀ cr ∈ ex6Wit.regions, ∀ e ∈ cmEx6, e.name = cr.name → e.addr = cr.entryPc := by
  intro cr hcr e he hnm
  simp only [ex6Wit, List.mem_cons, List.not_mem_nil, or_false] at hcr
  simp only [cmEx6, mkEntry, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases hcr with rfl | rfl <;> rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [ex6HelperCr, ex6MainCr]

theorem ex6_vll_wp_n2_k1 (r₀ : Regs) (m : Mem 64)
    (hr1 : r₀.r1 = 2#64) (hr2 : r₀.r2 = 1#64) (hrv : r₀.rv = 40#64)
    {s : MachSt arm64Arch} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel armWordBind ⟨r₀, m⟩ 32 (fun _ => True) s)
    (hanc : (vllFramePreds arm64Arch).raReg s ra0 ∧
      (s.mem =⋆ Eq m ⋆ hwStackMem arm64Arch (s.gpr arm64Arch.abi.sp) ra0 32 ⋆ fun _ => True)) :
    vcmEx6.wp (wordHaltPost arm64Arch (fun c _ => c = 41#64)
      (region (s.gpr arm64Arch.abi.sp - 32#64) (32 + arm64Arch.abi.raBytes) ⋆ fun _ => True))
      8#64 s := by
  refine fromWordContify_wp_sound arm64Arch_wf armWordBind_wf ex6_fromWordContify_ok
    ex6_symAgree (budget := 32) ?_ (fun _ he => by simp [ex6_res_eq] at he)
    ex6_res_eq (fun cr' hcr' _ => by
      simp only [ex6Wit, List.mem_cons, List.not_mem_nil, or_false] at hcr'
      rcases hcr' with rfl | rfl <;> exact Or.inr rfl)
    ?_ (List.mem_cons_of_mem _ List.mem_cons_self) rfl
    (ex6_cm_wp_n2_k1 r₀ m hr1 hr2 hrv) hrel (fun _ => hanc) (fun h => absurd h (by decide))
  · intro cr hcr
    dsimp only [regionStackBudget, ex6Wit, witnessBudgets, regionFrameSlots, regionNeedFrame,
      regionMaxDepth]
    simp only [ex6HelperCr_pcs, ex6MainCr_pcs]
    simp only [ex6Wit, List.mem_cons, List.not_mem_nil, or_false] at hcr
    rcases hcr with rfl | rfl <;> exact Nat.le_of_ble_eq_true (by t_kernel_rfl)
  · intro cr' hcr' _ ew hew
    simp only [ex6Wit, List.mem_cons, List.not_mem_nil, or_false] at hcr'
    rcases hcr' with rfl | rfl
    · simp [ex6HelperCr] at hew; subst hew; trivial
    · simp [ex6MainCr] at hew
      rcases hew with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem ex6_vll_adequacy_n2_k1 (r₀ : Regs) (m : Mem 64)
    (hr1 : r₀.r1 = 2#64) (hr2 : r₀.r2 = 1#64) (hrv : r₀.rv = 40#64)
    {s : MachSt arm64Arch} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel armWordBind ⟨r₀, m⟩ 32 (fun _ => True) s)
    (hanc : (vllFramePreds arm64Arch).raReg s ra0 ∧
      (s.mem =⋆ Eq m ⋆ hwStackMem arm64Arch (s.gpr arm64Arch.abi.sp) ra0 32 ⋆ fun _ => True)) :
    ∃ c s', vcmEx6.Halts 8#64 s c s' ∧
      wordHaltPost arm64Arch (fun c _ => c = 41#64)
        (region (s.gpr arm64Arch.abi.sp - 32#64) (32 + arm64Arch.abi.raBytes) ⋆ fun _ => True)
        c s' :=
  VllCodeMap.adequacy (ex6_vll_wp_n2_k1 r₀ m hr1 hr2 hrv hrel hanc)

/-! ## §6. `PrivFrameCfg` (`numSlots := 1`) & `Xcap.Bridge` Composition (`armSelfCert`) -/

@[expose] def bPrivSlot : BlockP := fun _ r =>
  .letOp2 (.sub i64) (.var r.sp) (.imm 8#64) fun slot0 =>
  .store (t := i64) (.imm 42#64) (.var slot0)
    (.load i64 (.var slot0) fun v => .halt (.var v))

@[expose] def cmPriv : CodeMap := [mkEntry "priv_entry" 0#64 bPrivSlot]

@[expose] def crPriv : ContifyRegion :=
  { name := "priv_entry"
    entryPc := 0#64
    abi := .retEnvelope
    privFrame := { numSlots := 1, dynAliasGuard := false }
    tree := [.leaf 0#64]
    edges := []
    retainFallbacks := false }

@[expose] def witPriv : ContifyWitness := ⟨[crPriv]⟩

theorem crPriv_pcs : crPriv.allPcs = [0#64] := by
  simp [ContifyRegion.allPcs, crPriv, GroupTree.allPcs]

theorem witPriv_check : witPriv.check cmPriv = true := by
  dsimp only [witPriv, ContifyWitness.check, ContifyWitness.checkAux, ContifyRegion.check]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, crPriv_pcs]
  t_kernel_rfl

theorem witPriv_res_eq : residualContifyCodeMap cmPriv witPriv = [] := by
  have h1 : List.flatMap ContifyRegion.allPcs
      (List.filter (fun r => !r.retainFallbacks) witPriv.regions) = [0#64] := by
    simp [witPriv, crPriv, ContifyRegion.allPcs, GroupTree.allPcs]
  dsimp only [residualContifyCodeMap]
  rw [h1]
  simp [cmPriv, mkEntry]

@[expose] def privItems : List (ContifyRegion × List (BitVec 64) × Nat × Bool) :=
  [(crPriv, [0#64], 2, true)]

@[expose] def privTags : List TagLbl :=
  [ .raw "priv_entry",
    .pc "priv_entry" 0 ]

@[expose] def vcmPriv : VllCodeMap arm64Arch :=
  rawContVcm armWordBind cmPriv witPriv privItems

theorem priv_fromWordContify_ok : fromWordContify armWordBind cmPriv witPriv = .ok vcmPriv := by
  refine (fromWordContify_eq_fast armWordBind cmPriv witPriv privItems rfl
    (by t_kernel_rfl) witPriv_check witPriv_res_eq ?_).trans
    (rawContVcm_ok (by t_kernel_rfl) privTags (by t_kernel_rfl) (by t_kernel_rfl)
      (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl) (by t_kernel_rfl)
      (by t_kernel_rfl) 0 2 (by t_kernel_rfl) (by t_kernel_rfl) (by decide)
      (by t_kernel_rfl))
  intro x hx
  simp only [privItems, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  refine ⟨crPriv_pcs, ?_, ?_⟩ <;>
  · dsimp only [regionFrameSlots, regionNeedFrame, regionMaxDepth]
    simp only [crPriv_pcs]; t_kernel_rfl

theorem priv_emits_slotSt_ld :
    (vcmPriv.flatten.any fun i => match i with | .slotSt 0 _ => true | _ => false) = true ∧
    (vcmPriv.flatten.any fun i => match i with | .slotLd _ 0 => true | _ => false) = true := by
  have hStB : (vcmPriv.blocks.any fun b =>
      b.body.any fun i => match i with | .slotSt 0 _ => true | _ => false) = true := by
    t_kernel_rfl
  have hLdB : (vcmPriv.blocks.any fun b =>
      b.body.any fun i => match i with | .slotLd _ 0 => true | _ => false) = true := by
    t_kernel_rfl
  obtain ⟨bs, hbs, hbis⟩ := List.any_eq_true.mp hStB
  obtain ⟨is, his, hms⟩ := List.any_eq_true.mp hbis
  obtain ⟨bl, hbl, hbil⟩ := List.any_eq_true.mp hLdB
  obtain ⟨il, hil, hml⟩ := List.any_eq_true.mp hbil
  exact ⟨List.any_eq_true.mpr ⟨is, mem_flattenBlocks_body hbs his, hms⟩,
    List.any_eq_true.mpr ⟨il, mem_flattenBlocks_body hbl hil, hml⟩⟩

/-- Concrete `fromWord_open_cptr_with_fnSpec` linking a minimal open L0 caller jumping to
compiled Arm64 `"double_add_ten"` (`armSelf_doubleAddTen_cptr` from `XcapBridgeArm64Test`). -/
@[expose] noncomputable def doubleAddTenAddr : BitVec 64 :=
  armAddrCodec.toBits (armTarget.mach.labelAddr armSelfCert.host "double_add_ten")

@[expose] def bOpenCall (tgt : BitVec 64) : BlockP := fun _ r =>
  .ijmp (.imm tgt) r.keep

@[expose] def cmOpenCall (tgt : BitVec 64) : CodeMap :=
  [mkEntry "bw_open_caller" 0x100#64 (bOpenCall tgt)]

@[expose] def vcmOpenCall (tgt : BitVec 64) : VllCodeMap arm64Arch :=
  let blk : Block arm64Arch :=
    { label := "bw_open_caller"
      pad? := some .btiJC
      body := [.movi (.reg .X10) (tgt.setWidth 64)]
      term := .ijmp (.reg .X10) }
  { blocks := [blk]
    symAddr := buildVllSymAddr [("bw_open_caller", 0x100#64)] [blk]
    addrTaken := ["bw_open_caller"] }

theorem openCall_fromWord_ok (tgt : BitVec 64) :
    fromWord armWordBind (cmOpenCall tgt) = .ok (vcmOpenCall tgt) := by
  t_kernel_rfl

theorem openCall_budget_zero (tgt : BitVec 64) :
    codeMapMaxBudget armWordBind (cmOpenCall tgt) = 0 := by
  t_kernel_rfl

theorem openCall_via_fnSpec
    {Ψ_L1 : Xcap.CodeSpec (MachSt arm64Arch)} {H_L1 : Xcap.Halt (MachSt arm64Arch)}
    (hclL1 : Xcap.Closed (vllXcapMach arm64Arch (vcmOpenCall doubleAddTenAddr).symAddr)
      (vcmOpenCall doubleAddTenAddr).toXcapCode Ψ_L1 H_L1)
    {Ψ_T : Xcap.CodeSpec armTarget.mach.MData} {H_T : armTarget.mach.State → Prop}
    (hclT : Xcap.TargetClosed armTarget armAddrCodec armSelfCert.host Ψ_T H_T)
    (st : BedrockWord.State) {s : MachSt arm64Arch}
    (hRel : WordPlainEntryRel armWordBind st
      (codeMapMaxBudget armWordBind (cmOpenCall doubleAddTenAddr)) (fun _ => True) s)
    (hImpBridge : ∀ s' st',
      WordPlainEntryRel armWordBind st'
        (codeMapMaxBudget armWordBind (cmOpenCall doubleAddTenAddr)) (fun _ => True) s' →
      ∃ d : armTarget.mach.MData,
        Xcap.targetCallPre armTarget armAddrCodec armSelfCert.host
          (Env.ofTable selfTbl "double_add_ten" [i64] [i64])
          (armSelfCert.bound "double_add_ten") 0 Ψ_T d ∧
        (Ψ_T doubleAddTenAddr d → Ψ_L1 doubleAddTenAddr s')) :
    Ψ_L1 0x100#64 s := by
  let Imp : Nat → BedrockWord.CodeSpec := fun _ pc _ => pc = doubleAddTenAddr
  let Exp : Nat → BedrockWord.CodeSpec := fun r pc st' => r > 0 ∧ pc = 0x100#64 ∧ st' = st
  have hMod :
      OpenModOk (cmOpenCall doubleAddTenAddr) (fun _ _ => False) (fun _ => True) Imp Exp := by
    intro ρ Ψ r _ _ hSub pc st0 ⟨hrPos, hpc, hst0⟩
    subst hpc; cases hst0
    refine ⟨reifyBlock (bOpenCall doubleAddTenAddr),
      by simp [cmOpenCall, mkEntry, CodeMap.lookupAddr], ?_⟩
    have hPsi : Ψ doubleAddTenAddr st := hSub 0 hrPos doubleAddTenAddr st (Or.inl rfl)
    cases st with | mk r_ m_ => cases r_ with | mk sp_ rp_ rv_ r1_ r2_ r3_ =>
    simpa [bOpenCall, reifyBlock, toFlat, RegsV.levels0, RegsV.keep, RegsExpr.idxArgs,
      idxArg, BlockFlat.wp, denoteArg, denoteRegsExpr, lookupV, listGet?, castTy, tyDecEq,
      pushRegsV, pushTup, RegsV.toTup, Regs.toRegsV, RegsExpr.eval, Arg.val] using hPsi
  have hfnDouble : armTarget.FnSpec armSelfCert.host "double_add_ten"
      (Env.ofTable selfTbl "double_add_ten" [i64] [i64])
      (armSelfCert.bound "double_add_ten") 0 :=
    vll_cptr_to_target_fnSpec armAddrCodec (fun _ _ hc => (armSelf_doubleAddTen_cptr hc).2)
  refine fromWord_open_cptr_with_fnSpec arm64Arch_wf armWordBind_wf
    (openCall_fromWord_ok doubleAddTenAddr)
    (Imp := Imp) (Exp := Exp) (sp0 := s.gpr arm64Arch.abi.sp) (ra0 := 0#64)
    (R := fun _ => True) hMod trivial hclL1
    (fun _ _ h => by
      simp only [plainHaltPost, openCall_budget_zero, ↓reduceIte, wordHaltPost] at h
      rcases h with ⟨_, hf, _⟩; exact False.elim hf)
    armAddrCodec hfnDouble hclT ?_ 1 0x100#64 st s ⟨Nat.zero_lt_one, rfl, rfl⟩ hRel
    (fun hp => absurd hp (by rw [openCall_budget_zero]; omega))
  intro _ pc st' s' hpc hR' _
  obtain ⟨d, hd, hback⟩ := hImpBridge s' st' hR'
  exact ⟨hpc, d, hd, hpc ▸ hback⟩

/-! ## §7. `check_std_axioms!` & MetaM Isolation/Axiom Audits -/

check_std_axioms!
  LeanQbe.T.Vll.fromWord_open_cptr_sound
  LeanQbe.T.Vll.fromWord_cptr_sound
  LeanQbe.T.Vll.fromWord_wp_sound
  LeanQbe.T.Vll.fromWord_adequacy
  LeanQbe.T.Vll.contified_open_cptr_spec
  LeanQbe.T.Vll.contified_cptr_spec
  LeanQbe.T.Vll.fromWordContify_open_cptr_sound
  LeanQbe.T.Vll.fromWordContify_cptr_sound
  LeanQbe.T.Vll.fromWordContify_wp_sound
  LeanQbe.T.Vll.fromWordContify_adequacy
  LeanQbe.T.Vll.vllHosted_closed
  LeanQbe.T.Vll.vllHosted_closed_noHalt
  LeanQbe.T.Vll.fromWord_hosted_vllStep
  LeanQbe.T.Vll.fromWordContify_hosted_vllStep
  LeanQbe.T.Vll.contified_hosted_vllStep
  LeanQbe.T.Vll.target_fnSpec_to_vll_entry
  LeanQbe.T.Vll.vll_cptr_to_target_fnSpec
  LeanQbe.T.Vll.fromWord_open_cptr_with_fnSpec
  LeanQbe.T.Vll.fromWordContify_open_cptr_with_fnSpec
  LeanQbeTest.T.VllFromWordTest.armWordBind_wf
  LeanQbeTest.T.VllFromWordTest.ex1_fromWord_ok
  LeanQbeTest.T.VllFromWordTest.ex1_hosted
  LeanQbeTest.T.VllFromWordTest.ex1_vll_wp_fast
  LeanQbeTest.T.VllFromWordTest.ex1_vllStep_fast
  LeanQbeTest.T.VllFromWordTest.ex2b_fromWordContify_ok
  LeanQbeTest.T.VllFromWordTest.ex2b_asm_has_bl_ret
  LeanQbeTest.T.VllFromWordTest.ex2b_vll_wp
  LeanQbeTest.T.VllFromWordTest.ex6_fromWordContify_ok
  LeanQbeTest.T.VllFromWordTest.ex6_vll_wp_n2_k1
  LeanQbeTest.T.VllFromWordTest.ex6_vll_adequacy_n2_k1
  LeanQbeTest.T.VllFromWordTest.priv_fromWordContify_ok
  LeanQbeTest.T.VllFromWordTest.priv_emits_slotSt_ld
  LeanQbeTest.T.VllFromWordTest.openCall_fromWord_ok
  LeanQbeTest.T.VllFromWordTest.openCall_via_fnSpec

meta section
open Lean

private def allowedStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
private def isForbiddenArchMod (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Kraken.X64" || s.startsWith "Kraken.AArch64" ||
  s.startsWith "LeanQbe.T.Amd64" || s.startsWith "LeanQbe.T.Arm64"

#eval show MetaM Unit from do
  for modName in [`LeanQbe.T.Vll.FromWord, `LeanQbe.T.Vll.FromWordLemmas] do
    let env ← importModules #[{ module := modName }] {}
    let bad := env.header.moduleNames.filter isForbiddenArchMod
    if !bad.isEmpty then throwError "{modName} leaks arch module(s): {bad.toList}"
  let env ← getEnv
  let targets : List Name :=
    [ ``LeanQbe.T.Vll.fromWord, ``LeanQbe.T.Vll.fromWordContify
    , ``LeanQbe.T.Vll.fromWord_open_cptr_sound, ``LeanQbe.T.Vll.fromWord_wp_sound
    , ``LeanQbe.T.Vll.contified_open_cptr_spec, ``LeanQbe.T.Vll.fromWordContify_open_cptr_sound
    , ``LeanQbe.T.Vll.fromWordContify_wp_sound, ``LeanQbe.T.Vll.vllHosted_closed
    , ``LeanQbe.T.Vll.fromWord_hosted_vllStep, ``LeanQbe.T.Vll.fromWordContify_hosted_vllStep
    , ``LeanQbe.T.Vll.fromWord_open_cptr_with_fnSpec
    , ``LeanQbe.T.Vll.fromWordContify_open_cptr_with_fnSpec
    , ``LeanQbeTest.T.VllFromWordTest.ex1_vllStep_fast
    , ``LeanQbeTest.T.VllFromWordTest.ex2b_asm_has_bl_ret
    , ``LeanQbeTest.T.VllFromWordTest.ex2b_vll_wp
    , ``LeanQbeTest.T.VllFromWordTest.ex6_vll_adequacy_n2_k1
    , ``LeanQbeTest.T.VllFromWordTest.priv_emits_slotSt_ld
    , ``LeanQbeTest.T.VllFromWordTest.openCall_via_fnSpec ]
  for nm in targets do
    let axs ← Lean.collectAxioms nm
    let badAx := axs.filter fun a => !allowedStdAxioms.contains a
    if !badAx.isEmpty then throwError "Disallowed axioms for {nm}: {badAx.toList}"
    match env.find? nm with
    | some ci => if ci.isUnsafe then throwError "Declaration {nm} is unsafe"
    | none => throwError "Declaration {nm} not found"

end

end LeanQbeTest.T.VllFromWordTest
