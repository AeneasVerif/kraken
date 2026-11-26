module

public import LeanQbe.T.Arm64.VllFactorArm64Save
public import LeanQbe.T.Arm64.VllFactorArm640
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas

/-!
# AArch64 `BedrockMach` L1 Flag-Reuse & `jnzGprInv?` Proofs (`Arm64.VllFactorArm64FlagLemmas`)

Helper theorems backing `VllPolicySpec arm64Arch vllArmNativeHooks` and label-freedom for
`VllFactorArm641`, keeping `VllFactorArm641` well under `2,500` LOC with `0` `@[expose]` on
theorems and `0` public `*Lemmas*` imports in `VllFactorArm641`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T
open LeanQbe.T.Vll

/-! ## 1. Label-Freedom Helpers Moved From `VllFactorArm641` -/

theorem vllArmSaveRegs_noLab : ∀ i rs, NoVllLab (vllArmSaveRegs i rs)
  | _, [] => noVllLab_nil
  | _, [_] => noVllLab_one (fun _ e => by cases e)
  | i, .SP :: r2 :: rs =>
    noVllLab_cons (fun _ e => by cases e) (vllArmSaveRegs_noLab (i + 1) (r2 :: rs))
  | i, .reg _ :: .SP :: rs =>
    noVllLab_cons (fun _ e => by cases e) (vllArmSaveRegs_noLab (i + 1) (.SP :: rs))
  | i, .reg _ :: .reg _ :: rs => by
    dsimp only [vllArmSaveRegs]
    refine noVllLab_append ?_ (vllArmSaveRegs_noLab (i + 2) rs)
    split
    · exact noVllLab_one (fun _ e => by cases e)
    · exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)

theorem vllArmRestoreRegs_noLab : ∀ i rs, NoVllLab (vllArmRestoreRegs i rs)
  | _, [] => noVllLab_nil
  | _, [_] => noVllLab_one (fun _ e => by cases e)
  | i, .SP :: r2 :: rs =>
    noVllLab_cons (fun _ e => by cases e) (vllArmRestoreRegs_noLab (i + 1) (r2 :: rs))
  | i, .reg _ :: .SP :: rs =>
    noVllLab_cons (fun _ e => by cases e) (vllArmRestoreRegs_noLab (i + 1) (.SP :: rs))
  | i, .reg _ :: .reg _ :: rs => by
    dsimp only [vllArmRestoreRegs]
    refine noVllLab_append ?_ (vllArmRestoreRegs_noLab (i + 2) rs)
    split
    · exact noVllLab_one (fun _ e => by cases e)
    · exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)

theorem wrapArmNative_noLab {res : Option (List _root_.Directive × FlagMask)}
    {c : List (Instr arm64Arch)} {cl : FlagMask} (h : wrapArmNative res = some (c, cl)) :
    NoVllLab c := by
  obtain ⟨p, hp, hEq⟩ := Option.map_eq_some_iff.mp h
  rcases p with ⟨ds, cl'⟩
  cases hEq
  exact insPure_map_native_noLab

/-! ## 2. Bridge & Flag-Reuse Policy Proofs -/

private theorem wrapArmNative_eq_some' {res : Option (List _root_.Directive × FlagMask)}
    {c : List (Instr arm64Arch)} {cl : FlagMask}
    (h : wrapArmNative res = some (c, cl)) :
    ∃ ds, res = some (ds, cl) ∧ c = ds.map (Instr.native (A := arm64Arch)) := by
  cases res with
  | none => cases h
  | some p =>
    rcases p with ⟨ds, cl'⟩
    simp only [wrapArmNative, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨ds, rfl, rfl⟩

private theorem vllPArg_to_arm' {s : MachSt arm64Arch} {t : Ty}
    {pa : PArg Arm64.Reg Empty ArmCond t} {v : Val t}
    (h : (vllMach arm64Arch).PArgHolds s t pa v) :
    armMach.PArgHolds (vllToMachData s) t pa v := by
  cases pa with
  | gpr r => simpa [Machine.PArgHolds, armMach, vllMach, get_vllToMachData] using h
  | vec vr => exact vr.elim
  | flag c => exact h
  | imm c => exact h

private theorem armPDst_to_vll' {sm : MachineData} {t : Ty}
    {pd : PDst Arm64.Reg Empty ArmCond t} {v : Val t}
    (h : armMach.PDstHolds sm t pd v) :
    (vllMach arm64Arch).PDstHolds (machDataToVll sm) t pd v := by
  cases pd with
  | gpr r => exact h
  | vec vr => exact vr.elim
  | flag c => exact h

theorem vllArm_cmpFlags_spec {co : CmpOp} {cnd : ArmCond} {w : Vll.Width}
    {a b : BitVec w.bits} {f : StatusFlags}
    (hco : (some ∘ armCmpCond) co = some cnd) :
    arm64Arch.evalCond (arm64Arch.cmpFlags w a b f) cnd = co.evalBits a b := by
  simp only [Function.comp_def, Option.some.injEq] at hco; subst hco
  dsimp only [arm64Arch, arm64CmpFlags]
  simp only [armCmpCond, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
    StatusFlags.subs, StatusFlags.from_result, CmpOp.evalBits, BitVec.ult, BitVec.ule,
    BitVec.slt, BitVec.sle]
  cases w <;> cases co <;> grind [BitVec.unsigned, BitVec.signed]

theorem vllArm_jnzGprInv_spec
    {fn : Arm64.Reg → Bool → Sym → List (Instr arm64Arch) × FlagMask}
    {h : VllHost arm64Arch} {k j : Nat} {r : Arm64.Reg} {inv : Bool} {l : Sym}
    {b : Bool} {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hfn : (some fun r inv l =>
        let p := armJnzGprInv r inv l; (p.1.map (Instr.native (A := arm64Arch)), p.2)) = some fn)
    (hc : (fn r inv l).1.IsInfixAt h.prog k) (hl : h.labelAddr l = h.addrOf j)
    (hr : r ∉ arm64Arch.abi.scratch) (hb : GprHolds (s.gpr r) .bool b)
    (hk : ∀ s', (vllMach arm64Arch).Frame arm64Arch.condReads s s' arm64Arch.abi.scratch []
        (fn r inv l).2 → s'.mem = s.mem →
      ((if inv then !b else b) = true → (vllMach arm64Arch).Run h j s' post) ∧
      ((if inv then !b else b) = false →
        (vllMach arm64Arch).Run h (k + (fn r inv l).1.length) s' post)) :
    (vllMach arm64Arch).Run h k s post := by
  cases hfn
  obtain ⟨hp, hlen⟩ := armJnzGprInv_pure_len r inv l
  refine armBranchRun_to_vllNative hp hlen hc hl ?_ (by simpa only [List.length_map] using hk)
  intro host jt postH hinfH hlabH hcontH
  have hg : GprHolds (armMach.getGpr (vllToMachData s) r) .bool b := by
    simpa [armMach, get_vllToMachData] using hb
  exact arm_gprSpec.jnzGprInv_spec rfl hinfH hlabH hr hg
    (fun sm' hfr hm => by simpa only [Nat.zero_add] using hcontH sm' hfr hm)

theorem vllArm_setcc_boolFlag_spec {h : VllHost arm64Arch} {k : Nat}
    {d : XReg} {cnd : ArmCond} {b : Bool} {P : Tup Val [.bool] → Prop}
    {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hb : cnd.interp s.flags = b) (hP : P (b, ())) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k [.setcc (.reg d) cnd]
      ((@PDst.gpr Arm64.Reg Empty ArmCond .bool (.reg d)).gprs ++
        arm64Arch.abi.scratch) [] maskNone s
      (fun s' => (∃ b' : Bool, P (b', ()) ∧
          (vllMach arm64Arch).PDstHolds s' .bool (.gpr (.reg d)) b' ∧
          (vllMach arm64Arch).evalCond s' cnd = b') ∧
        s'.mem = s.mem) post := by
  refine fallsTo_weaken_rd (A := arm64Arch) (rd := (.reg d : Arm64.Reg)) ?_
  intro hc cont
  refine vllMach_run_of_bodyWp hc
    (fun _ hi _ => by simp only [List.mem_singleton] at hi; subst hi; intro e; cases e)
    (fun _ hi _ => by simp only [List.mem_singleton] at hi; subst hi; intro e; cases e)
    (K := fun s' => s' = s.setGprW .w8 (.reg d)
      (BitVec.ofNat 8 (arm64Arch.evalCond s.flags cnd).toNat))
    (instrWp_setcc (A := arm64Arch) (symAddr := h.labelAddr) (rd := .reg d) (c := cnd) rfl)
    fun s' hs' => by
      subst hs'
      have hev : (vllMach arm64Arch).evalCond
          (s.setGprW .w8 (.reg d) (BitVec.ofNat 8 (arm64Arch.evalCond s.flags cnd).toNat)) cnd =
          b := by
        simpa [vllMach, arm64Arch] using hb
      have hpd : (vllMach arm64Arch).PDstHolds
          (s.setGprW .w8 (.reg d) (BitVec.ofNat 8 (arm64Arch.evalCond s.flags cnd).toNat))
          .bool (.gpr (.reg d)) b := by
        show GprHolds ((s.setGprW .w8 (.reg d)
          (BitVec.ofNat 8 (arm64Arch.evalCond s.flags cnd).toNat)).gpr (.reg d)) .bool b
        rw [MachSt.gpr_setGprW_same]
        dsimp only [GprHolds, arm64Arch]
        rw [arm64Arch_wf.writeSub_setWidth .w8, hb]
      refine cont _ ⟨⟨b, hP, hpd, hev⟩, rfl⟩
        ⟨fun r hr => ?_, fun v _ => v.elim, fun _ _ => rfl⟩
      simp only [List.mem_singleton] at hr
      exact MachSt.gpr_setGprW_ne s .w8 _ hr

theorem vllArm_cmpCore_flags_spec {h : VllHost arm64Arch} {k : Nat}
    {o : CmpOp} {wd : Vll.Width} {ra : XReg} {rhs : Src arm64Arch}
    {pd : PDst Arm64.Reg Empty ArmCond .bool} {c : List (Instr arm64Arch)} {clob : FlagMask}
    {va vb : BitVec wd.bits} {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    {G : GprIsa Arm64.Reg Empty ArmCond (Instr arm64Arch)}
    (hcoG : G.condOfCmp? = some ∘ armCmpCond)
    (hc : vllArmCmpCore o wd ra rhs pd = some (c, clob))
    (ha : (s.gpr (.reg ra)).setWidth wd.bits = va) (hb : rhs.evalW wd s.gpr = vb) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c
      (pd.gprs ++ arm64Arch.abi.scratch) [] clob s
      (fun s' => (vllMach arm64Arch).PDstHolds s' .bool pd (o.evalBits va vb) ∧
        FlagCmpOk (vllMach arm64Arch) G s' va vb false ∧
        s'.mem = s.mem) post := by
  have hCmpOk : ∀ (s' : MachSt arm64Arch),
      s'.flags = StatusFlags.subs (va - vb) va vb →
      FlagCmpOk (vllMach arm64Arch) G s' va vb false := by
    intro s' hsf co' cc' _ hco'
    rw [hcoG] at hco'
    show (vllMach arm64Arch).evalCond s' cc' = co'.evalBits va vb
    dsimp only [vllMach]
    rw [hsf]
    exact vllArm_cmpFlags_spec (f := s.flags) hco'
  cases pd with
  | vec v => exact v.elim
  | flag cf =>
    dsimp only [vllArmCmpCore] at hc
    cases heq : (cf == armCmpCond o) <;> simp only [heq, Bool.false_eq_true, ↓reduceIte] at hc
    · cases hc
    · cases hc
      have hcf : cf = armCmpCond o := beq_iff_eq.mp heq; subst hcf
      refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
        (vllMach_cmp_spec arm64Arch_wf (w := wd) (lhs := .reg ra) (rhs := rhs))
        (fun _ hr => False.elim (List.not_mem_nil hr))
        (fun _ hr => False.elim (List.not_mem_nil hr)) (flagMask_sub_refl _)) ?_
      intro s' ⟨hf, hm⟩ _
      have hsf : s'.flags = StatusFlags.subs (va - vb) va vb := by
        rw [hf]; dsimp only [arm64Arch, arm64CmpFlags]; rw [ha, hb]
      have hok := hCmpOk s' hsf
      refine ⟨?_, hok, hm⟩
      exact hok o (armCmpCond o) (by simp) (by rw [hcoG]; rfl)
  | gpr r => cases r with | SP => cases hc | reg d =>
    cases hc
    have h1 : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
        ([.cmp wd (.reg ra) rhs] ++ [.setcc (.reg d) (armCmpCond o)])
        ([] ++ [.reg d]) ([] ++ []) (maskNZCV ||| maskNone) s
        (fun s' => GprHolds (s'.gpr (.reg d)) .bool (o.evalBits va vb) ∧
          FlagCmpOk (vllMach arm64Arch) G s' va vb false ∧ s'.mem = s.mem) post := by
      refine Machine.FallsTo.comp
        (vllMach_cmp_spec arm64Arch_wf (w := wd) (lhs := .reg ra) (rhs := rhs))
        fun s₁ ⟨hf₁, hm₁⟩ _ => by
          have hsf₁ : s₁.flags = StatusFlags.subs (va - vb) va vb := by
            rw [hf₁]; dsimp only [arm64Arch, arm64CmpFlags]; rw [ha, hb]
          have hok₁ := hCmpOk s₁ hsf₁
          have hcc : (vllMach arm64Arch).evalCond s₁ (armCmpCond o) = o.evalBits va vb :=
            hok₁ o (armCmpCond o) (by simp) (by rw [hcoG]; rfl)
          refine Machine.FallsTo.conseq
            (vllMach_setcc_spec arm64Arch_wf (rd := .reg d) (c := armCmpCond o) (s := s₁)) ?_
          intro s' ⟨hg', hm'⟩ hfr'
          refine ⟨by rw [hcc] at hg'; exact hg', ?_, hm'.trans hm₁⟩
          intro co' cc' hne hco'
          have hkeq : (vllMach arm64Arch).evalCond s' cc' = (vllMach arm64Arch).evalCond s₁ cc' :=
            hfr'.2.2 cc'
              (by simp only [FlagMask.disjoint, maskNone, BitVec.and_zero, beq_self_eq_true])
          rw [hkeq]; exact hok₁ co' cc' hne hco'
    refine Machine.FallsTo.conseq (Machine.FallsTo.weaken h1
      (fun r hr => by
        simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr; exact List.mem_cons_self)
      (fun _ hr => False.elim (List.not_mem_nil hr))
      (by simp only [maskNZCV, maskNone, BitVec.or_zero]; exact flagMask_sub_refl _)) ?_
    intro s' ⟨hg, hok, hm⟩ _; exact ⟨hg, hok, hm⟩

theorem vllArm_cmpNative_flags_spec {h : VllHost arm64Arch} {k : Nat}
    {o : CmpOp} {n : Nat} {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)}
    {pd : PDst Arm64.Reg Empty ArmCond .bool} {lhsFirst : Bool} {vh : VariantHint}
    {c : List (Instr arm64Arch)} {clob : FlagMask} {va vb : BitVec n}
    {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    {G : GprIsa Arm64.Reg Empty ArmCond (Instr arm64Arch)}
    (hcoG : G.condOfCmp? = some ∘ armCmpCond)
    (hfl : armCmpFlagsOut o n pa pb pd = some lhsFirst)
    (hfb : wrapArmNative (armOp (.cmp o (.bits n) .bool rfl) (pa, pb, ()) (pd, ()) vh) =
      some (c, clob))
    (ha : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ armScratch) (hd : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (hpa : (vllMach arm64Arch).PArgHolds s (.bits n) pa va)
    (hpb : (vllMach arm64Arch).PArgHolds s (.bits n) pb vb) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' => (vllMach arm64Arch).PDstHolds s' .bool pd (o.evalBits va vb) ∧
        FlagCmpOk (vllMach arm64Arch) G s'
          (if lhsFirst then va else vb) (if lhsFirst then vb else va) false ∧
        s'.mem = s.mem) post := by
  obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some' hfb
  obtain ⟨hp, hlen⟩ := armOp_pure_len hds
  exact armFallsTo_to_vllNative hp hlen fun host postH =>
    Machine.FallsTo.conseq
      (arm_gprSpec.op_cmpFlags_spec hfl hds ha hd (vllPArg_to_arm' hpa) (vllPArg_to_arm' hpb))
      fun sm' ⟨hpd, hfc, hm⟩ _ => by
        refine ⟨armPDst_to_vll' hpd, ?_, hm⟩
        intro co' cc' hne hco'
        rw [hcoG] at hco'
        exact hfc co' cc' hne hco'

theorem armCmpOp_isSome_of_flagsOut {o : CmpOp} {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)}
    {pd : PDst Arm64.Reg Empty ArmCond .bool} {lf : Bool} {vh : VariantHint}
    (hfl : armCmpFlagsOut o n pa pb pd = some lf) :
    (armOp (.cmp o (.bits n) .bool rfl) (pa, pb, ()) (pd, ()) vh).isSome = true := by
  have hfin : ∀ (cmp : List _root_.Instr) (co : CmpOp),
      (pd = .flag (armCmpCond co) ∨ ∃ d, pd = .gpr (.reg d)) →
      (match pd with
        | .flag cf => if cf == armCmpCond co then some (cmp, maskNZCV) else none
        | .gpr (.reg d) => some (cmp ++ [armCset64I d (armCmpCond co)], maskNZCV)
        | .gpr .SP | .vec _ => (none : Option (List _root_.Instr × FlagMask))).isSome = true := by
    intro cmp co hpd
    rcases hpd with rfl | ⟨d, rfl⟩ <;> simp only [beq_self_eq_true, ↓reduceIte, Option.isSome_some]
  dsimp only [armCmpFlagsOut] at hfl
  split at hfl; · cases hfl
  rename_i hn
  split at hfl; · cases hfl
  simp only [Option.bind_eq_some_iff] at hfl
  rcases hfl with ⟨lf', hlf', hok⟩
  have hpd : pd = .flag (armCmpCond (if lf' then o else o.swap)) ∨ ∃ d, pd = .gpr (.reg d) := by
    cases pd with
    | vec v => exact v.elim
    | gpr r => cases r with | SP => simp at hok | reg d => exact Or.inr ⟨d, rfl⟩
    | flag cf =>
      dsimp only at hok
      by_cases he : (cf == armCmpCond (if lf' then o else o.swap)) = true
      · simp only [he, ↓reduceIte, Option.some.injEq] at hok; subst hok
        exact Or.inl (by simp [beq_iff_eq.mp he])
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hok; cases hok
  have hargImm : ∀ (rx : XReg) (m : Nat) (v : BitVec m),
      ∃ xs, armArgInIns (n := m) rx (.imm v) = some xs := by
    intro rx m v; dsimp only [armArgInIns]; exact ⟨_, rfl⟩
  have hargGpr : ∀ (rx ry : XReg),
      ∃ xs, armArgInIns (n := n) rx (.gpr (.reg ry)) = some xs := by
    intro rx ry; dsimp only [armArgInIns]; exact ⟨_, rfl⟩
  dsimp only [armOp, emitCleanPair, armOpIns]
  rw [Option.isSome_map]
  dsimp only [armCmpOpIns]
  simp only [hn, Bool.false_eq_true, ↓reduceIte]
  cases pa with
  | vec v => exact v.elim
  | imm ca => cases pb with
    | vec v => exact v.elim
    | imm _ => cases hlf'
    | gpr r2 => cases r2 with
      | SP => cases hlf'
      | reg rb =>
        dsimp only at hlf'
        by_cases hca0 : (ca == 0#n) = true
        · simp only [hca0, ↓reduceIte] at hlf'
          cases hzc : armZeroCmpIns? o.swap n rb pd
          · simp only [hzc, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
              Option.some.injEq] at hlf'
            subst hlf'; simp only [Bool.false_eq_true, ↓reduceIte] at hpd
            simp only [hca0, ↓reduceIte, hzc]
            cases hn32 : (n == 32 || n == 64)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hci0 : (armCmpImmIns? .W32 .X16 0#32).isSome = true := by decide
              rcases Option.isSome_iff_exists.mp hci0 with ⟨l, hl⟩; rw [hl]
              exact hfin _ o.swap hpd
            · simp only [↓reduceIte]
              cases hci : armCmpImmIns? (armWidthOf n) rb ca
              · have hm : armCmpImmIns? (armWidthOf n) rb ca = none := hci
                have hca0' : ca = 0#n := beq_iff_eq.mp hca0
                rw [hca0'] at hm
                have himm0 : armImm12? (0#n) =
                    some (.imm { imm := .int64 0, shift := .S0 }) := by
                  simp [armImm12?]
                simp [armCmpImmIns?, himm0] at hm
              · exact hfin _ o.swap hpd
          · simp only [hzc, Option.isSome_some, ↓reduceIte] at hlf'; cases hlf'
        · simp only [hca0, Bool.false_eq_true, ↓reduceIte] at hlf'
          simp only [hca0, Bool.false_eq_true, ↓reduceIte]
          cases hn32 : (n == 32 || n == 64) <;> simp only [hn32, ↓reduceIte] at hlf' ⊢
          · cases hlf'; simp only [Bool.false_eq_true, ↓reduceIte] at hpd
            cases armCmpImmIns? .W32 .X16 _ <;> exact hfin _ o.swap hpd
          · cases hci : armCmpImmIns? (armWidthOf n) rb ca <;>
              simp only [hci, Option.isSome_none, Option.isSome_some, Bool.not_false,
                Bool.not_true, Option.some.injEq] at hlf'
            · subst hlf'; simp only [↓reduceIte] at hpd
              rcases hargImm .X16 n ca with ⟨xs, hxs⟩
              simp only [bind, Option.bind, hxs]
              exact hfin _ o hpd
            · subst hlf'; simp only [Bool.false_eq_true, ↓reduceIte] at hpd
              exact hfin _ o.swap hpd
  | gpr r1 => cases r1 with
    | SP => cases hlf'
    | reg ra => cases pb with
      | vec v => exact v.elim
      | imm cb =>
        dsimp only at hlf'
        by_cases hcb0 : (cb == 0#n && (armZeroCmpIns? o n ra pd).isSome) = true
        · simp only [hcb0, ↓reduceIte] at hlf'; cases hlf'
        · simp only [hcb0, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hlf'
          subst hlf'; simp only [↓reduceIte] at hpd
          by_cases hcb : (cb == 0#n) = true
          · have hzc : armZeroCmpIns? o n ra pd = none := by
              simp only [hcb, Bool.true_and, Option.isSome_eq_false_iff, Bool.not_eq_true] at hcb0
              exact Option.isNone_iff_eq_none.mp hcb0
            simp only [hcb, ↓reduceIte, hzc]
            cases hn32 : (n == 32 || n == 64)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have hci0 : (armCmpImmIns? .W32 .X16 0#32).isSome = true := by decide
              rcases Option.isSome_iff_exists.mp hci0 with ⟨l, hl⟩; rw [hl]; exact hfin _ o hpd
            · simp only [↓reduceIte]
              cases hci : armCmpImmIns? (armWidthOf n) ra cb
              · have hm : armCmpImmIns? (armWidthOf n) ra cb = none := hci
                rw [beq_iff_eq.mp hcb] at hm
                have himm0 : armImm12? (0#n) =
                    some (.imm { imm := .int64 0, shift := .S0 }) := by
                  simp [armImm12?]
                simp [armCmpImmIns?, himm0] at hm
              · exact hfin _ o hpd
          · simp only [hcb, Bool.false_eq_true, ↓reduceIte]
            cases hn32 : (n == 32 || n == 64)
            · simp only [Bool.false_eq_true, ↓reduceIte]
              cases armCmpImmIns? .W32 .X16 _ <;> exact hfin _ o hpd
            · simp only [↓reduceIte]
              cases armCmpImmIns? (armWidthOf n) ra cb
              · rcases hargImm .X17 n cb with ⟨xs, hxs⟩
                simp only [bind, Option.bind, hxs]; exact hfin _ o hpd
              · exact hfin _ o hpd
      | gpr r2 => cases r2 with
        | SP => cases hlf'
        | reg rb =>
          simp only [Option.some.injEq] at hlf'
          subst hlf'; simp only [↓reduceIte] at hpd
          rcases hargGpr .X16 ra with ⟨xa, hxa⟩
          rcases hargGpr .X17 rb with ⟨xb, hxb⟩
          simp only [bind, Option.bind, hxa, hxb]
          cases (n == 32 || n == 64) <;> exact hfin _ o hpd

theorem vllArm_testOp_boolFlag_spec
    {h : VllHost arm64Arch} {k w : Nat} {neg : Bool}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits w)}
    {pd : PDst Arm64.Reg Empty ArmCond .bool}
    {c : List (Instr arm64Arch)} {clob : FlagMask} {va vb : BitVec w} {cnd : ArmCond}
    {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hcl : clob ≠ FlagMask.none)
    (hcc : (some ∘ armCmpCond) (if neg then .ne else .eq) = some cnd)
    (hto : wrapArmNative (armTestOp w neg pa pb pd) = some (c, clob))
    (ha : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ armScratch) (hd : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (hpa : (vllMach arm64Arch).PArgHolds s (.bits w) pa va)
    (hpb : (vllMach arm64Arch).PArgHolds s (.bits w) pb vb) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w
        (vllMach arm64Arch).PDstHolds s' .bool pd res ∧ (vllMach arm64Arch).evalCond s' cnd = res ∧
        s'.mem = s.mem) post := by
  obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some' hto
  obtain ⟨hp, hlen⟩ := armTestOp_pure_len hds
  have hcc' : armGpr.condOfCmp? (if neg then .ne else .eq) = some cnd := hcc
  exact armFallsTo_to_vllNative hp hlen fun host postH =>
    Machine.FallsTo.conseq
      (arm_gprSpec.testOp_boolFlag_spec rfl hcl hcc' hds ha hd
        (vllPArg_to_arm' hpa) (vllPArg_to_arm' hpb))
      fun sm' ⟨hpd, hev, hm⟩ _ => ⟨armPDst_to_vll' hpd, hev, hm⟩

end LeanQbe.T.Arm64
