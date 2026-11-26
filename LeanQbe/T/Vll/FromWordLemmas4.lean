module

public import LeanQbe.T.Vll.FromWord
public import LeanQbe.T.BedrockWord.Exec
import LeanQbe.T.Vll.FromWordLemmas0
import LeanQbe.T.Vll.FromWordLemmas1
import LeanQbe.T.Vll.FromWordLemmas2
import LeanQbe.T.Vll.FromWordLemmas3
import LeanQbe.T.Unified.CfgContifyLemmas
import LeanQbe.T.BedrockWord.Ops
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas

/-!
# Stage-0/1 Internal Block, Region & Contification Machinery (`Vll.FromWordLemmas4`)

Private proof support behind the firewall for `LeanQbe.T.Vll.FromWordLemmas`:
* §1. Plain `WordPlainAnchorRel` helpers and `lowerPlainEntry_bwp`.
* §2. Stage-1 region/budget/no-mem/no-halt helpers, `ContifyNode`, `ContifyFix`, and
      `contify_contCall_discharge`.
* §3. `retEnv_entry_bwp`, `contify_block_step`, and `contify_specsClosed`.

Zero `@[expose]`, zero `Arm64`/`Amd64`/`Kraken.X64`/`Kraken.AArch64` imports, zero `*Lemmas*`
public imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.BedrockWord
open LeanQbe.T.Unified

/-! ## §1. Stack-Frame Split/Merge Helpers and `lowerPlainEntry_bwp` -/

private def freshRaFor (A : Arch) (s : MachSt A) (fallback : BitVec 64) : BitVec 64 :=
  match A.abi.raKind with
  | .stack => fallback
  | .linkReg lr => s.gpr lr

private theorem raReg_freshRaFor (A : Arch) (s : MachSt A) (fallback : BitVec 64) :
    (vllFramePreds A).raReg s (freshRaFor A s fallback) := by
  cases h : A.abi.raKind <;> simp [vllFramePreds, freshRaFor, h]

private theorem sub_sub_eq_sub_add (a : BitVec 64) {x y : Nat} (_hxy : x + y ≤ 2 ^ 64) :
    (a - BitVec.ofNat 64 x) - BitVec.ofNat 64 y = a - BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

private theorem hwSp_sub_rem_eq (sp0 : BitVec 64) {selfFrame budget : Nat}
    (hle : selfFrame ≤ budget) (hbd : budget ≤ 2 ^ 64) :
    (sp0 - BitVec.ofNat 64 selfFrame) - BitVec.ofNat 64 (budget - selfFrame) =
      sp0 - BitVec.ofNat 64 budget := by
  simpa [show selfFrame + (budget - selfFrame) = budget by omega] using
    sub_sub_eq_sub_add sp0 (x := selfFrame) (y := budget - selfFrame) (by omega)

private theorem retAddr_merge_region (A : Arch) (sp ra : BitVec 64) :
    ∀ m, (vllFramePreds A).RetAddr sp ra m → region sp A.abi.raBytes m := by
  intro m hm
  cases hkind : A.abi.raKind <;>
    simp only [vllFramePreds, hkind, Abi.raBytes, RaKind.raBytes] at hm ⊢
  · exact cell64_region hm
  · exact hm

theorem hwStackMem_to_region (A : Arch) {sp0 ra : BitVec 64} {n : Nat}
    (hbd : n + A.abi.raBytes ≤ 2 ^ 64) :
    ∀ m, hwStackMem A sp0 ra n m →
      region (sp0 - BitVec.ofNat 64 n) (n + A.abi.raBytes) m := by
  intro m hm
  dsimp only [hwStackMem] at hm
  have h1 := sep_mono (retAddr_merge_region A sp0 ra) hm
  have hsp : sp0 - BitVec.ofNat 64 n + BitVec.ofNat 64 n = sp0 := BitVec.sub_add_cancel _ _
  rw [region_split hbd, hsp]
  exact sep_cast h1 (by ac_rfl)

theorem wordRegsRel_setSp {A : Arch} {b : WordRegBind A} (hwf : b.Wf) (r : Regs)
    (s : MachSt A) (v : BitVec 64) :
    WordRegsRel b r (s.setGpr A.abi.sp v) ↔ WordRegsRel b r s :=
  wordRegsRel_setGpr_work hwf r s (Or.inr (Or.inl rfl)) v

theorem wordRegsRel_of_keepNonSpRa {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {r : Regs} {s₁ s₂ : MachSt A} (hr : WordRegsRel b r s₁)
    (hkeep : ∀ q, q ≠ A.abi.sp → q ∉ A.abi.raRegs → s₂.gpr q = s₁.gpr q) :
    WordRegsRel b r s₂ := by
  have hdisj := (wordRegs_not_sp_ra hwf).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hkeep b.sp (hdisj b.sp (by simp [WordRegBind.wordRegs])).1
      (hdisj b.sp (by simp [WordRegBind.wordRegs])).2).trans hr.1
  · exact (hkeep b.rp (hdisj b.rp (by simp [WordRegBind.wordRegs])).1
      (hdisj b.rp (by simp [WordRegBind.wordRegs])).2).trans hr.2.1
  · exact (hkeep b.rv (hdisj b.rv (by simp [WordRegBind.wordRegs])).1
      (hdisj b.rv (by simp [WordRegBind.wordRegs])).2).trans hr.2.2.1
  · exact (hkeep b.r1 (hdisj b.r1 (by simp [WordRegBind.wordRegs])).1
      (hdisj b.r1 (by simp [WordRegBind.wordRegs])).2).trans hr.2.2.2.1
  · exact (hkeep b.r2 (hdisj b.r2 (by simp [WordRegBind.wordRegs])).1
      (hdisj b.r2 (by simp [WordRegBind.wordRegs])).2).trans hr.2.2.2.2.1
  · exact (hkeep b.r3 (hdisj b.r3 (by simp [WordRegBind.wordRegs])).1
      (hdisj b.r3 (by simp [WordRegBind.wordRegs])).2).trans hr.2.2.2.2.2

def WordPlainAnchorRel {A : Arch} (b : WordRegBind A) (st : BedrockWord.State)
    (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop) (s : MachSt A) : Prop :=
  WordRegsRel b st.regs s ∧
  (budget = 0 → s.mem =⋆ Eq st.mem ⋆ R) ∧
  (budget > 0 → A.abi.spEntry sp0 ∧ budget + A.abi.raBytes ≤ 2 ^ 64 ∧
    s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
    (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 budget ⋆ R))

theorem wordPlainAnchorRel_iff {A : Arch} (b : WordRegBind A) (st : BedrockWord.State)
    (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop) (s : MachSt A) :
    WordPlainAnchorRel b st sp0 ra0 budget R s ↔
      WordRegsRel b st.regs s ∧
      (budget = 0 → s.mem =⋆ Eq st.mem ⋆ R) ∧
      (budget > 0 → A.abi.spEntry sp0 ∧ budget + A.abi.raBytes ≤ 2 ^ 64 ∧
        s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
        (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 budget ⋆ R)) :=
  Iff.rfl

theorem sep_array64_emp {a : BitVec 64} (P : Mem 64 → Prop) {m : Mem 64}
    (hm : P m) : (array64 a [] ⋆ P) m := by
  rw [array64_nil, emp_sep]; exact hm

theorem codeMap_entry_mem_of_lookup {cm : CodeMap} {pc : BitVec 64} {blk : BlockFlat}
    (hlu : cm.lookupAddr pc = some blk) :
    ∃ e ∈ cm, e.addr = pc ∧ e.block = blk := by
  induction cm with
  | nil => cases hlu
  | cons e es ih =>
    dsimp only [CodeMap.lookupAddr] at hlu
    by_cases he : e.addr = pc
    · rw [beq_iff_eq.mpr he, ite_eq_left rfl] at hlu
      cases hlu; exact ⟨e, List.mem_cons_self, he, rfl⟩
    · simp only [beq_false_of_ne he, Bool.false_eq_true, ↓reduceIte] at hlu
      obtain ⟨e', he', rfl, rfl⟩ := ih hlu
      exact ⟨e', List.mem_cons_of_mem _ he', rfl, rfl⟩

theorem lowerPlainEntry_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hvwf : vcm.Wf)
    {sp0 ra0 : BitVec 64} {maxB : Nat} {R : Mem 64 → Prop}
    {Ψ_L0 : BedrockWord.CodeSpec} {H_L0 : HaltPost}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a)
    (hHalt : ∀ c s, plainHaltPost A H_L0 sp0 ra0 maxB R c s → H_L1 c s)
    (hExit : ∀ tgt st s', Ψ_L0 tgt st → WordPlainAnchorRel b st sp0 ra0 maxB R s' →
      Ψ_L1 tgt s')
    {e : CodeEntry} (hBud : plainEntryBudget b e.block ≤ maxB)
    {s0 s1 : Nat} {bs : List (Block A)} (hlo : (lowerPlainEntry b cm e).run s0 = .ok (bs, s1))
    (hsub : ∀ x ∈ bs, x ∈ vcm.blocks)
    {rw : Regs} {mL0 : Mem 64} {s_entry : MachSt A}
    (hRel : WordPlainAnchorRel b ⟨rw, mL0⟩ sp0 ra0 maxB R s_entry)
    (hbp : e.block.wp cm.symEnv Ψ_L0 H_L0 (pushRegsV rw.toRegsV) mL0) :
    Ψ_L1 (vcm.symAddr e.name) s_entry := by
  dsimp only [lowerPlainEntry] at hlo
  let spills := tempSpillCount b (maxBlockDepth e.block 6)
  change StateT.run (lowerPlainBody b cm e.name (if spills > 0 then some spills else none)
    e.name (some b.padKind)
    (match (if spills > 0 then some spills else none) with | some ns => [.prologue ns] | none => [])
    6 e.block) s0 = .ok (bs, s1) at hlo
  by_cases hspPos : spills > 0
  · have hfsz_pos : 0 < A.abi.frameSize spills :=
      Nat.lt_of_lt_of_le (by omega) (hawf.slots_le_frameSize spills)
    have hBudEq : plainEntryBudget b e.block = A.abi.frameSize spills := by
      dsimp only [plainEntryBudget]; rw [ite_eq_left hspPos]
    have hMaxPos : maxB > 0 := Nat.lt_of_lt_of_le (hBudEq ▸ hfsz_pos) hBud
    obtain ⟨hspE, hbd, hspEq, hra0, hm⟩ := hRel.2.2 hMaxPos
    have hfsz_le : A.abi.frameSize spills ≤ maxB := hBudEq ▸ hBud
    have hfsz_bd : A.abi.frameSize spills ≤ 2 ^ 64 := by omega
    have hm_split : s_entry.mem =⋆ (vllFramePreds A).RetAddr sp0 ra0 ⋆
        region (sp0 - BitVec.ofNat 64 (A.abi.frameSize spills)) (A.abi.frameSize spills) ⋆
        (region (sp0 - BitVec.ofNat 64 maxB) (maxB - A.abi.frameSize spills) ⋆
          Eq mL0 ⋆ R) := by
      rw [hwStackMem_split hfsz_le hbd] at hm
      exact sep_cast hm (by ac_rfl)
    have hm_pro : s_entry.mem =⋆ (vllFramePreds A).RetAddr (s_entry.gpr A.abi.sp) ra0 ⋆
        region (s_entry.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize spills))
          (A.abi.frameSize spills) ⋆
        (region (sp0 - BitVec.ofNat 64 maxB) (maxB - A.abi.frameSize spills) ⋆
          Eq mL0 ⋆ R) := by
      simpa only [hspEq] using hm_split
    let hwSp := sp0 - BitVec.ofNat 64 (A.abi.frameSize spills)
    let G := (vllFramePreds A).Saved sp0 ra0 spills ⋆
      region (sp0 - BitVec.ofNat 64 maxB) (maxB - A.abi.frameSize spills) ⋆ R
    have hframeSome : (if spills > 0 then some spills else none) = some spills :=
      ite_eq_left hspPos
    simp only [hframeSome] at hlo
    refine lowerPlainBody_bwp hawf hwf hvwf hcl hcmAddr
      (dMax := maxBlockDepth e.block 6) (hwSp := hwSp) (ra₀ := ra0) (G := G)
      (by change tempSpillCount b (maxBlockDepth e.block 6) ≤ (some spills).getD 0
          exact Nat.le_refl spills)
      ?_ ?_ e.block e.name (some b.padKind) [.prologue spills] 6
      (pushRegsV rw.toRegsV) rw mL0 s_entry (Nat.le_refl 6) (Nat.le_refl _) hlo hsub hbp ?_
    · intro s_fin tgtVal nxt' m' slots' hlen hw0 hr' _ hsp' hm' hpsi
      have hsp_bd : A.abi.frameSize spills + A.abi.raBytes ≤ 2 ^ 64 := by omega
      have hcan : hwSp + BitVec.ofNat 64 (A.abi.frameSize spills) = sp0 :=
        BitVec.sub_add_cancel _ _
      have hm_ep : s_fin.mem =⋆ array64 (s_fin.gpr A.abi.sp) slots' ⋆
          (vllFramePreds A).Saved
            (s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize spills)) ra0 spills ⋆
          (region (sp0 - BitVec.ofNat 64 maxB) (maxB - A.abi.frameSize spills) ⋆
            Eq m' ⋆ R) := by
        simp only [hsp', hcan, G] at hm' ⊢
        exact sep_cast hm' (by ac_rfl)
      refine instrWp_epilogue hawf hlen hsp_bd hm_ep ?_
      intro s' hspFin hraFin hkeep hmFinEq hmPost
      have hr'' := wordRegsRel_of_keepNonSpRa hwf hr' hkeep
      have hw0_s' : s'.gpr b.w0 = tgtVal := by
        have hw0_sp : b.w0 ≠ A.abi.sp := (work_not_sp hwf).2.1
        have hw0_ra : b.w0 ∉ A.abi.raRegs := (work_not_ra hwf).2.1
        exact (hkeep b.w0 hw0_sp hw0_ra).trans hw0
      have hspFin' : s'.gpr A.abi.sp = sp0 := by
        rw [hspFin, hsp']; exact BitVec.sub_add_cancel _ _
      have hmFin' : s'.mem =⋆ Eq m' ⋆ hwStackMem A sp0 ra0 maxB ⋆ R := by
        rw [hspFin'] at hmPost
        rw [hwStackMem_split hfsz_le hbd]
        exact sep_cast hmPost (by ac_rfl)
      have hAnch' : WordPlainAnchorRel b ⟨nxt'.eval, m'⟩ sp0 ra0 maxB R s' :=
        ⟨hr'', fun hz => absurd hz (Nat.ne_of_gt hMaxPos),
          fun _ => ⟨hspE, hbd, hspFin', hraFin, hmFin'⟩⟩
      dsimp only [bodyWp]
      simpa only [hw0_s'] using hExit tgtVal ⟨nxt'.eval, m'⟩ s' hpsi hAnch'
    · intro s_fin cVal m' slots' hlen hw0 hsp' hm' hHL0
      have hsp_bd : A.abi.frameSize spills + A.abi.raBytes ≤ 2 ^ 64 := by omega
      have hcan : hwSp + BitVec.ofNat 64 (A.abi.frameSize spills) = sp0 :=
        BitVec.sub_add_cancel _ _
      have hm_ep : s_fin.mem =⋆ array64 (s_fin.gpr A.abi.sp) slots' ⋆
          (vllFramePreds A).Saved
            (s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize spills)) ra0 spills ⋆
          (region (sp0 - BitVec.ofNat 64 maxB) (maxB - A.abi.frameSize spills) ⋆
            Eq m' ⋆ R) := by
        simp only [hsp', hcan, G] at hm' ⊢
        exact sep_cast hm' (by ac_rfl)
      refine instrWp_epilogue hawf hlen hsp_bd hm_ep ?_
      intro s' hspFin _ hkeep hmFinEq hmPost
      have hw0_s' : s'.gpr b.w0 = cVal := by
        have hw0_sp : b.w0 ≠ A.abi.sp := (work_not_sp hwf).2.1
        have hw0_ra : b.w0 ∉ A.abi.raRegs := (work_not_ra hwf).2.1
        exact (hkeep b.w0 hw0_sp hw0_ra).trans hw0
      have hspFin' : s'.gpr A.abi.sp = sp0 := by
        rw [hspFin, hsp']; exact BitVec.sub_add_cancel _ _
      have hmFin' : s'.mem =⋆ Eq m' ⋆ hwStackMem A sp0 ra0 maxB ⋆ R := by
        rw [hspFin'] at hmPost
        rw [hwStackMem_split hfsz_le hbd]
        exact sep_cast hmPost (by ac_rfl)
      refine hHalt (s'.gpr b.w0) s' ?_
      dsimp only [plainHaltPost]
      rw [ite_eq_right (Nat.ne_of_gt hMaxPos)]
      exact ⟨m', by simpa only [hw0_s'] using hHL0, sep_cast hmFin' (by ac_rfl)⟩
    · refine instrWp_prologue hawf hra0 hfsz_bd hm_pro ?_
      intro slots hlen; dsimp only; intro m' hm'
      rw [hspEq] at hm'
      refine ⟨slots, hlen, ?_, ?_, fun h => absurd h (by simp), ?_, ?_⟩
      · refine envRel_pushRegsV 0 ?_
        simpa only [wordRegsRel_setFlags, wordRegsRel_setMem,
          wordRegsRel_setSp hwf] using hRel.1
      · simpa only [wordRegsRel_setFlags, wordRegsRel_setMem,
          wordRegsRel_setSp hwf] using hRel.1
      · rw [MachSt.gpr_setFlags, MachSt.gpr_setMem, MachSt.gpr_setGpr_same, hspEq]
      · exact sep_cast hm' (by dsimp only [G, hwSp]; ac_rfl)
  · have hsp0 : spills = 0 := Nat.eq_zero_of_not_pos hspPos
    have hframeNone : (if spills > 0 then some spills else none) = none := by simp [hsp0]
    simp only [hframeNone] at hlo
    let raLocal := if maxB > 0 then ra0 else freshRaFor A s_entry ra0
    let G := if maxB > 0 then hwStackMem A sp0 ra0 maxB ⋆ R else R
    let hwSp := if maxB > 0 then sp0 else s_entry.gpr A.abi.sp
    refine lowerPlainBody_bwp hawf hwf hvwf hcl hcmAddr
      (dMax := maxBlockDepth e.block 6) (hwSp := hwSp) (ra₀ := raLocal) (G := G)
      (by change tempSpillCount b (maxBlockDepth e.block 6) ≤ (none : Option Nat).getD 0
          exact Nat.le_of_eq hsp0)
      ?_ ?_ e.block e.name (some b.padKind) [] 6
      (pushRegsV rw.toRegsV) rw mL0 s_entry (Nat.le_refl 6) (Nat.le_refl _) hlo hsub hbp ?_
    · intro s_fin tgtVal nxt' m' slots' hlen hw0 hr' hra' hsp' hm' hpsi
      dsimp only [bodyWp]
      have hm'_emp : (Eq m' ⋆ G) s_fin.mem := by
        have hslNil : slots' = [] := List.eq_nil_of_length_eq_zero hlen
        subst hslNil; rw [array64_nil, emp_sep] at hm'; exact hm'
      have hAnch' : WordPlainAnchorRel b ⟨nxt'.eval, m'⟩ sp0 ra0 maxB R s_fin := by
        refine ⟨hr', fun hz => ?_, fun hpos => ?_⟩
        · have hnot : ¬ (maxB > 0) := by omega
          simpa only [G, hnot, ↓reduceIte] using hm'_emp
        · obtain ⟨hspE, hbd, _, _, _⟩ := hRel.2.2 hpos
          have hra1 : (vllFramePreds A).raReg s_fin ra0 := by
            simpa only [raLocal, hpos, ↓reduceIte] using hra' rfl
          have hsp1 : s_fin.gpr A.abi.sp = sp0 := by
            simpa only [hwSp, hpos, ↓reduceIte] using hsp'
          have hm1 : (Eq m' ⋆ hwStackMem A sp0 ra0 maxB ⋆ R) s_fin.mem :=
            sep_cast (by simpa only [G, hpos, ↓reduceIte] using hm'_emp) (by ac_rfl)
          exact ⟨hspE, hbd, hsp1, hra1, hm1⟩
      simpa only [hw0] using hExit tgtVal ⟨nxt'.eval, m'⟩ s_fin hpsi hAnch'
    · intro s_fin cVal m' slots' hlen hw0 hsp' hm' hHL0
      dsimp only [bodyWp]
      have hm'_emp : (Eq m' ⋆ G) s_fin.mem := by
        have hslNil : slots' = [] := List.eq_nil_of_length_eq_zero hlen
        subst hslNil; rw [array64_nil, emp_sep] at hm'; exact hm'
      refine hHalt (s_fin.gpr b.w0) s_fin ?_
      dsimp only [plainHaltPost]
      by_cases hpos : maxB > 0
      · rw [ite_eq_right (Nat.ne_of_gt hpos)]
        exact ⟨m', by simpa only [hw0] using hHL0,
          by simpa only [G, hpos, ↓reduceIte] using hm'_emp⟩
      · have hz : maxB = 0 := Nat.eq_zero_of_not_pos hpos
        rw [hz, ite_eq_left rfl]
        exact ⟨m', by simpa only [hw0] using hHL0,
          by simpa only [G, hpos, ↓reduceIte] using hm'_emp⟩
    · refine ⟨[], rfl, envRel_pushRegsV 0 hRel.1, hRel.1, fun _ => ?_, ?_, ?_⟩
      · by_cases hpos : maxB > 0
        · simp only [raLocal, hpos, ↓reduceIte]; exact (hRel.2.2 hpos).2.2.2.1
        · simp only [raLocal, hpos, ↓reduceIte]; exact raReg_freshRaFor A s_entry ra0
      · by_cases hpos : maxB > 0
        · simp only [hwSp, hpos, ↓reduceIte]; exact (hRel.2.2 hpos).2.2.1
        · simp only [hwSp, hpos, ↓reduceIte]
      · refine sep_array64_emp _ ?_
        by_cases hpos : maxB > 0
        · simp only [G, hpos, ↓reduceIte]; exact sep_cast (hRel.2.2 hpos).2.2.2.2 (by ac_rfl)
        · have hz : maxB = 0 := Nat.eq_zero_of_not_pos hpos
          simp only [G, hpos, ↓reduceIte]; exact hRel.2.1 hz

/-! ## §2. Stage-1 Region, Memory-Free, Epilogue & `ContifyNode` Infrastructure -/

theorem checkContRegion_entryPc_mem {cm : CodeMap} {cr : ContifyRegion}
    {callees : List ContCalleeMeta} (hchk : cr.check cm callees = true) :
    cr.entryPc ∈ cr.allPcs := by
  dsimp only [ContifyRegion.check] at hchk
  simp only [Bool.and_eq_true] at hchk
  have hEntIn : cr.entryPc ∈ cr.tree.map GroupTree.entryPc := by
    simpa using hchk.1.1.1.1.2
  obtain ⟨g, hgMem, hgEq⟩ := List.mem_map.mp hEntIn
  have hGrp := checkContGroupNodes_forall cm cr callees _ cr.tree hchk.1.1.2 g hgMem
  have hMemG := checkContGroupNode_entryPc_mem cm cr callees _ g hGrp
  rw [hgEq] at hMemG
  exact List.mem_flatMap.mpr ⟨g, hgMem, hMemG⟩

theorem checkContRegion_priv_facts {cm : CodeMap} {cr : ContifyRegion}
    {callees : List ContCalleeMeta} (hchk : cr.check cm callees = true) :
    cr.privFrame.numSlots ≤ 64 ∧ (cr.privFrame.numSlots > 0 → cr.abi = .retEnvelope) := by
  dsimp only [ContifyRegion.check] at hchk
  simp only [Bool.and_eq_true] at hchk
  have h64 : cr.privFrame.numSlots ≤ 64 := of_decide_eq_true hchk.1.1.1.1.1.1.1.1.2
  refine ⟨h64, fun hpos => ?_⟩
  have h1 := hchk.1.1.1.1.1.1.1.2
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h1
  rcases h1 with hzero | heq
  · omega
  · exact heq

private theorem lowerM_bind_ok'' {α β : Type} {m : LowerM α} {f : α → LowerM β} {s0 s1 : Nat}
    {r : β} (h : (m >>= f).run s0 = .ok (r, s1)) :
    ∃ a sMid, m.run s0 = .ok (a, sMid) ∧ (f a).run sMid = .ok (r, s1) := by
  change Except.bind (m.run s0) (fun p => (f p.1).run p.2) = .ok (r, s1) at h
  cases hm : m.run s0 with
  | error _ => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

private theorem lowerM_mapM_mem'' {α β : Type} (f : α → LowerM (List β)) :
    ∀ (xs : List α) (s0 s1 : Nat) (xss : List (List β)),
      (xs.mapM f).run s0 = .ok (xss, s1) →
      ∀ x ∈ xs, ∃ sA sB ys, (f x).run sA = .ok (ys, sB) ∧ ∀ y ∈ ys, y ∈ xss.flatten
  | [], _, _, _, _, _, hx => by cases hx
  | x :: xs, s0, s1, xss, h, z, hz => by
    rw [List.mapM_cons] at h
    obtain ⟨y0, sMid, hx, h1⟩ := lowerM_bind_ok'' h
    obtain ⟨xss', sEnd, hxs, h2⟩ := lowerM_bind_ok'' h1
    change Except.ok (y0 :: xss', sEnd) = Except.ok _ at h2; cases h2
    rcases List.mem_cons.mp hz with rfl | hzTail
    · exact ⟨s0, sMid, y0, hx, fun y hy => List.mem_flatten.mpr ⟨y0, List.mem_cons_self, hy⟩⟩
    · obtain ⟨sA, sB, ys, hfy, hmem⟩ := lowerM_mapM_mem'' f xs sMid s1 xss' hxs z hzTail
      exact ⟨sA, sB, ys, hfy, fun y hy => by
        rw [List.flatten_cons]; exact List.mem_append_right _ (hmem y hy)⟩

theorem fromWordContify_entry_block_mem {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {wit : ContifyWitness} {vcm : VllCodeMap A} (h : fromWordContify b cm wit = .ok vcm)
    {cr : ContifyRegion} (hcr : cr ∈ wit.regions) :
    ({ label := cr.name, pad? := some b.padKind,
       body := (if regionNeedFrame b cm cr then [.prologue (regionFrameSlots b cm cr)] else []) ++
         emitPrivFrameInit b cr.privFrame.numSlots,
       term := .fall (innerLabel cr cr.entryPc) } : Block A) ∈ vcm.blocks := by
  dsimp only [fromWordContify] at h
  cases hck : cm.checkWf with
  | false => rw [hck] at h; cases h
  | true =>
    rw [hck] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hwck : wit.check cm = true
    · rw [hwck] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hr1 : (wit.regions.mapM (lowerContRegion b cm)).run 0 with
      | error _ =>
        change Except.bind ((wit.regions.mapM (lowerContRegion b cm)).run 0) _ = .ok vcm at h
        rw [hr1] at h; cases h
      | ok p1 =>
        rcases p1 with ⟨regBlocksList, st1⟩
        change Except.bind ((wit.regions.mapM (lowerContRegion b cm)).run 0) _ = .ok vcm at h
        rw [hr1] at h; dsimp only [Except.bind] at h
        let wRes := residualContifyCodeMap cm wit
        cases hr2 : (wRes.mapM (lowerPlainEntry b cm)).run st1 with
        | error _ =>
          change Except.bind ((wRes.mapM (lowerPlainEntry b cm)).run st1) _ = .ok vcm at h
          rw [hr2] at h; cases h
        | ok p2 =>
          rcases p2 with ⟨resBlocksList, st2⟩
          change Except.bind ((wRes.mapM (lowerPlainEntry b cm)).run st1) _ = .ok vcm at h
          rw [hr2] at h; dsimp only [Except.bind] at h
          obtain ⟨rfl, _, _⟩ := finalizeVllCodeMap_wf h
          obtain ⟨_, _, _, hregRun, hsub⟩ :=
            lowerM_mapM_mem'' (lowerContRegion b cm) wit.regions 0 st1 regBlocksList hr1 cr hcr
          dsimp only [lowerContRegion] at hregRun
          obtain ⟨_, _, _, hrest⟩ := lowerM_bind_ok'' hregRun
          change StateT.pure _ _ = Except.ok _ at hrest; cases hrest
          exact List.mem_append_left _ (hsub _ List.mem_cons_self)
    · have hwfF : wit.check cm = false := Bool.eq_false_iff.mpr hwck
      rw [hwfF] at h; dsimp only [Bool.not_false, ↓reduceIte, Bind.bind, Except.bind] at h
      cases h

private theorem foldl_maxCallee_contCall {A : Arch} {acc : List (Sym × Nat)}
    {ew : EdgeWitness} {edges : List EdgeWitness} (hew : ew ∈ edges)
    {callee : Sym} {calleePc : BitVec 64} {dualRet : Bool} {retPc : BitVec 64}
    {altPc? : Option (BitVec 64)}
    (hk : ew.kind = .contCall callee calleePc dualRet retPc altPc?) :
    A.abi.raBytes ≤ edges.foldl (fun accB (e : EdgeWitness) =>
      match e.kind with
      | .contCall callee' _ _ _ _ =>
        let cb := (acc.find? fun (p : Sym × Nat) => p.1 == callee').map Prod.snd |>.getD 0
        Nat.max accB (A.abi.raBytes + cb)
      | _ => accB) 0 := by
  let step : Nat → EdgeWitness → Nat := fun accB e =>
    match e.kind with
    | .contCall callee' _ _ _ _ =>
      let cb := (acc.find? fun (p : Sym × Nat) => p.1 == callee').map Prod.snd |>.getD 0
      Nat.max accB (A.abi.raBytes + cb)
    | _ => accB
  have hge : ∀ m (e : EdgeWitness), m ≤ step m e := fun m e => by
    cases hek : e.kind <;> simp [step, hek, Nat.le_max_left]
  suffices h : ∀ (es : List EdgeWitness) (m : Nat), ew ∈ es → A.abi.raBytes ≤ es.foldl step m from
    h edges 0 hew
  intro es
  induction es with
  | nil => intro _ hm; cases hm
  | cons x xs ih =>
    intro m hm
    dsimp only [List.foldl]
    rcases List.mem_cons.mp hm with rfl | htail
    · have h1 : A.abi.raBytes ≤ step m ew := by
        dsimp only [step]; rw [hk]; exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)
      have h2 : ∀ (ys : List EdgeWitness) (n : Nat), n ≤ ys.foldl step n := by
        intro ys; induction ys with
        | nil => exact fun _ => Nat.le_refl _
        | cons y ys ih' => exact fun n => Nat.le_trans (hge n y) (ih' _)
      exact Nat.le_trans h1 (h2 xs _)
    · exact ih _ htail

private theorem regionNeedFrame_pos_budget {A : Arch} (hawf : A.Wf) (b : WordRegBind A)
    (cm : CodeMap) {wit : ContifyWitness} (hwck : wit.check cm = true)
    {cr : ContifyRegion} (hcr : cr ∈ wit.regions)
    (hnf : regionNeedFrame b cm cr = true) :
    0 < regionStackBudget b cm wit cr := by
  have hnfOrig : regionNeedFrame b cm cr = true := hnf
  obtain ⟨pre, post, hSplit⟩ := List.mem_iff_append.mp hcr
  obtain ⟨hBudEq, hSelfLe, _⟩ := witnessBudgets_split b cm hwck hSplit
  have hSelfPos : regionNeedFrame b cm cr = true →
      (cr.privFrame.numSlots > 0 ∨ tempSpillCount b (regionMaxDepth cm cr) > 0) →
      0 < regionStackBudget b cm wit cr := by
    intro hnf' hOr
    have hns : 0 < regionFrameSlots b cm cr := by
      dsimp only [regionFrameSlots, regionSpillBase]
      rcases hOr with hp | hs <;> (split <;> omega)
    have hfsz : 0 < A.abi.frameSize (regionFrameSlots b cm cr) :=
      Nat.lt_of_lt_of_le (by omega) (hawf.slots_le_frameSize _)
    have hsf : (if regionNeedFrame b cm cr then A.abi.frameSize (regionFrameSlots b cm cr) else 0) =
        A.abi.frameSize (regionFrameSlots b cm cr) := by simp [hnf']
    rw [hsf] at hSelfLe
    exact Nat.lt_of_lt_of_le hfsz hSelfLe
  dsimp only [regionNeedFrame] at hnf
  rcases Bool.or_eq_true_iff.mp hnf with h1 | hCalls
  · rcases Bool.or_eq_true_iff.mp h1 with hPriv | hSpills
    · exact hSelfPos hnfOrig (Or.inl (by simpa using hPriv))
    · exact hSelfPos hnfOrig (Or.inr (by simpa using hSpills))
  · cases hkind : A.abi.raKind with
    | linkReg lr =>
      have hlr := hawf.linkReg_frameSize lr hkind (regionFrameSlots b cm cr)
      have hsf : (if regionNeedFrame b cm cr then A.abi.frameSize (regionFrameSlots b cm cr)
          else 0) = A.abi.frameSize (regionFrameSlots b cm cr) := by simp [hnfOrig]
      rw [hsf] at hSelfLe
      omega
    | stack =>
      dsimp only [regionHasCalls] at hCalls
      rw [List.any_eq_true] at hCalls
      obtain ⟨ew, hew, hkindEw⟩ := hCalls
      cases hk : ew.kind <;> rw [hk] at hkindEw <;> simp at hkindEw
      have hra : A.abi.raBytes = 8 := by simp [Abi.raBytes, hkind, RaKind.raBytes]
      have hmax := foldl_maxCallee_contCall (A := A)
        (acc := witnessBudgets b cm pre []) hew hk
      rw [hBudEq]
      exact Nat.lt_of_lt_of_le (by rw [hra]; decide) (Nat.le_trans hmax (Nat.le_add_left _ _))

theorem regionMemFree_blockNoMem {cm : CodeMap} {callees : List ContCalleeMeta}
    {cr : ContifyRegion} (hmf : regionMemFree cm callees cr = true)
    {pc : BitVec 64} (hpc : pc ∈ cr.allPcs) {blk : BlockFlat}
    (hlu : cm.lookupAddr pc = some blk) :
    blockNoMem blk = true := by
  dsimp only [regionMemFree] at hmf
  have h1 := List.all_eq_true.mp hmf pc hpc
  rw [hlu] at h1
  exact (Bool.and_eq_true_iff.mp h1).1

def noHaltBlock : BlockFlat → Bool
  | .let_ _ k => noHaltBlock k
  | .load _ _ k => noHaltBlock k
  | .store _ _ k => noHaltBlock k
  | .codeAddr _ k => noHaltBlock k
  | .jnz _ t e => noHaltBlock t && noHaltBlock e
  | .ijmp _ _ => true
  | .halt _ => false
  | .hlt => true

theorem noHaltBlock_wp_false {ρ : SymEnv} {Ψ : BedrockWord.CodeSpec} {H₁ H₂ : HaltPost} :
    ∀ (blk : BlockFlat) (bvs : List ((t : Ty) × Val t)) (m : Mem 64),
      noHaltBlock blk = true → blk.wp ρ Ψ H₁ bvs m → blk.wp ρ Ψ H₂ bvs m
  | .let_ op k, bvs, m, hnh, hwp => by
    dsimp only [BlockFlat.wp] at hwp ⊢
    cases hda : denoteArgs bvs op.args <;> rw [hda] at hwp; · exact hwp
    exact Op.wp_mono (fun xs hk => noHaltBlock_wp_false k _ m hnh hk) hwp
  | .load t a k, bvs, m, hnh, hwp => by
    dsimp only [BlockFlat.wp] at hwp ⊢
    cases hda : denoteArg bvs a <;> rw [hda] at hwp; · exact hwp
    obtain ⟨v, hv, hk⟩ := hwp
    exact ⟨v, hv, noHaltBlock_wp_false k _ m hnh hk⟩
  | .store v a k, bvs, m, hnh, hwp => by
    dsimp only [BlockFlat.wp] at hwp ⊢
    cases hdv : denoteArg bvs v <;> rw [hdv] at hwp; · exact hwp
    cases hda : denoteArg bvs a <;> rw [hda] at hwp; · exact hwp
    exact ⟨hwp.1, noHaltBlock_wp_false k _ _ hnh hwp.2⟩
  | .codeAddr sym k, bvs, m, hnh, ⟨a, ha, hk⟩ => ⟨a, ha, noHaltBlock_wp_false k _ m hnh hk⟩
  | .jnz c t e, bvs, m, hnh, hwp => by
    dsimp only [noHaltBlock] at hnh
    rcases Bool.and_eq_true_iff.mp hnh with ⟨hnt, hne⟩
    dsimp only [BlockFlat.wp] at hwp ⊢
    cases hdc : denoteArg bvs c <;> rw [hdc] at hwp; · exact hwp
    exact ⟨fun ht => noHaltBlock_wp_false t bvs m hnt (hwp.1 ht),
      fun hf => noHaltBlock_wp_false e bvs m hne (hwp.2 hf)⟩
  | .ijmp _ _, _, _, _, hwp => hwp
  | .halt _, _, _, hnh, _ => by dsimp only [noHaltBlock] at hnh; cases hnh
  | .hlt, _, _, _, hwp => False.elim hwp

private theorem listNodup_nodup' {α : Type} [BEq α] [LawfulBEq α] :
    ∀ xs : List α, listNodup xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    dsimp only [listNodup] at h
    rw [Bool.and_eq_true] at h
    have hn : xs.contains x = false := by cases hc : xs.contains x <;> simp_all
    have hm_not : x ∉ xs := fun hm => by rw [List.contains_iff_mem.mpr hm] at hn; cases hn
    exact List.nodup_cons.mpr ⟨hm_not, listNodup_nodup' xs h.2⟩

private theorem regionSplit_memFree_unique {cm : CodeMap} {wit : ContifyWitness}
    (hwck : wit.check cm = true) {pre : List ContifyRegion}
    (hpre : ∃ cr post, wit.regions = pre ++ cr :: post)
    {c₁ c₂ : ContCalleeMeta} (h1 : c₁ ∈ foldCallees cm [] pre)
    (h2 : c₂ ∈ foldCallees cm [] pre) (heq : c₁.name = c₂.name) :
    c₁ = c₂ := by
  have hw := hwck; dsimp only [ContifyWitness.check] at hw
  simp only [Bool.and_eq_true] at hw
  have hNd : (wit.regions.map (·.name)).Nodup := listNodup_nodup' _ hw.1.1
  obtain ⟨cr0, post0, hSplit0⟩ := hpre
  rw [hSplit0, List.map_append] at hNd
  have hNdPre : (pre.map (·.name)).Nodup := (List.nodup_append.mp hNd).1
  rcases mem_foldCallees cm pre c₁ [] h1 with hIn1 | ⟨p1a, p2a, cra, hEqa, htoa⟩
  · cases hIn1
  rcases mem_foldCallees cm pre c₂ [] h2 with hIn2 | ⟨p1b, p2b, crb, hEqb, htob⟩
  · cases hIn2
  have hna : cra.name = c₁.name := by
    cases ha : cra.abi <;> simp [ContifyRegion.toCalleeMeta?, ha] at htoa
    subst htoa; rfl
  have hnb : crb.name = c₂.name := by
    cases hb : crb.abi <;> simp [ContifyRegion.toCalleeMeta?, hb] at htob
    subst htob; rfl
  have hlenEq : p1a.length = p1b.length := Decidable.byContradiction fun hne => by
    have hSame : cra.name = crb.name := by rw [hna, hnb, heq]
    have hElemA : (pre.map (·.name))[p1a.length]? = some cra.name := by
      rw [hEqa, List.map_append, List.getElem?_append_right (by simp), List.length_map,
        Nat.sub_self]; rfl
    have hElemB : (pre.map (·.name))[p1b.length]? = some crb.name := by
      rw [hEqb, List.map_append, List.getElem?_append_right (by simp), List.length_map,
        Nat.sub_self]; rfl
    rw [hSame] at hElemA
    have hNdPre' : (pre.map (·.name)).Nodup := hNdPre
    have hNodupIdx : ∀ (xs : List Sym) (i j : Nat) (a : Sym),
        xs.Nodup → xs[i]? = some a → xs[j]? = some a → i = j := by
      intro xs
      induction xs with
      | nil => intro i _ _ _ hi; cases hi
      | cons z zs ih' =>
        intro i j a hndZ hi hj
        rw [List.nodup_cons] at hndZ
        cases i <;> cases j
        · rfl
        · rename_i j'
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          simp only [List.getElem?_cons_succ] at hj
          exact absurd (hi ▸ List.mem_of_getElem? hj) hndZ.1
        · rename_i i'
          simp only [List.getElem?_cons_succ] at hi
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          exact absurd (hj ▸ List.mem_of_getElem? hi) hndZ.1
        · rename_i i' j'
          simp only [List.getElem?_cons_succ] at hi hj
          exact congrArg Nat.succ (ih' i' j' a hndZ.2 hi hj)
    exact absurd (hNodupIdx (pre.map (·.name)) p1a.length p1b.length crb.name hNdPre'
      hElemA hElemB) hne
  have hEqBoth : p1a ++ cra :: p2a = p1b ++ crb :: p2b := hEqa.symm.trans hEqb
  have hp1 : p1a = p1b := by
    have := congrArg (List.take p1a.length) hEqBoth
    simpa [List.take_append_of_le_length, hlenEq] using this
  subst hp1
  have hrc : cra = crb := by
    have := List.append_cancel_left hEqBoth
    exact (List.cons.inj this).1
  subst hrc
  rw [htoa] at htob; cases htob; rfl

private theorem foldCallees_callee_match {cm : CodeMap} {wit : ContifyWitness}
    (hwck : wit.check cm = true) {pre : List ContifyRegion} {cr : ContifyRegion}
    {post : List ContifyRegion} (hSplit : wit.regions = pre ++ cr :: post)
    {callee : Sym} {calleePc : BitVec 64} {dualRet : Bool}
    (hCal : (foldCallees cm [] pre).any (fun c =>
      (c.name == callee) && (c.entryPc == calleePc) && (c.dualRet == dualRet)) = true)
    (hMf : cr.privFrame.numSlots > 0 → (foldCallees cm [] pre).any (fun c =>
      (c.name == callee) && (c.entryPc == calleePc) && c.memFree) = true) :
    ∃ p1 p2 cr_c, pre = p1 ++ cr_c :: p2 ∧ cr_c.name = callee ∧ cr_c.entryPc = calleePc ∧
      cr_c.abi = .contified dualRet ∧
      (cr.privFrame.numSlots > 0 →
        regionMemFree cm (foldCallees cm [] p1) cr_c = true) := by
  obtain ⟨c, hcMem, hcEq⟩ := List.any_eq_true.mp hCal
  simp only [Bool.and_eq_true, beq_iff_eq] at hcEq
  rcases hcEq with ⟨⟨rfl, rfl⟩, rfl⟩
  rcases mem_foldCallees cm pre c [] hcMem with hIn | ⟨p1, p2, cr_c, hPreEq, hto⟩
  · cases hIn
  cases habi : cr_c.abi <;> simp [ContifyRegion.toCalleeMeta?, habi] at hto
  rename_i dr
  subst hto
  refine ⟨p1, p2, cr_c, hPreEq, rfl, rfl, by simpa using habi, fun hpos => ?_⟩
  obtain ⟨c', hcMem', hcEq'⟩ := List.any_eq_true.mp (hMf hpos)
  simp only [Bool.and_eq_true, beq_iff_eq] at hcEq'
  rcases hcEq' with ⟨⟨hnEq, _⟩, hmfC⟩
  have heqC := regionSplit_memFree_unique hwck ⟨cr, post, hSplit⟩ hcMem' hcMem hnEq
  exact (congrArg ContCalleeMeta.memFree heqC).symm.trans hmfC

private theorem pre_region_mem {wit : ContifyWitness} {pre p1 p2 : List ContifyRegion}
    {cr_c cr : ContifyRegion} {post : List ContifyRegion}
    (hSplit : wit.regions = pre ++ cr :: post) (hPre : pre = p1 ++ cr_c :: p2) :
    cr_c ∈ wit.regions := by
  rw [hSplit, hPre]
  exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

private theorem call_frame_split_region (A : Arch)
    {sp0 hwSp : BitVec 64} {budget selfFrame cb : Nat}
    (hself : selfFrame ≤ budget) (hcb : selfFrame + (A.abi.raBytes + cb) ≤ budget)
    (hbd : budget + A.abi.raBytes ≤ 2 ^ 64)
    (hhw : hwSp = sp0 - BitVec.ofNat 64 selfFrame) :
    region (sp0 - BitVec.ofNat 64 budget) (budget - selfFrame) =
      (region (sp0 - BitVec.ofNat 64 budget) (budget - selfFrame - (A.abi.raBytes + cb)) ⋆
        (region ((hwSp - BitVec.ofNat 64 A.abi.raBytes) - BitVec.ofNat 64 cb) cb ⋆
          region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes)) := by
  let rem := budget - selfFrame
  let calleeNeed := A.abi.raBytes + cb
  have h1 : calleeNeed ≤ rem := by dsimp only [rem, calleeNeed]; omega
  have h2 : rem ≤ 2 ^ 64 := by dsimp only [rem]; omega
  have hhw_rem : hwSp - BitVec.ofNat 64 rem = sp0 - BitVec.ofNat 64 budget := by
    rw [hhw]; exact hwSp_sub_rem_eq sp0 hself (by omega)
  have hsub1 := region_sub_split (a := hwSp) h1 h2
  rw [hhw_rem] at hsub1
  have hsub2 := region_sub_split (a := hwSp) (lo := A.abi.raBytes) (hi := calleeNeed)
    (by dsimp only [calleeNeed]; omega) (by dsimp only [calleeNeed]; omega)
  have hsp_c : hwSp - BitVec.ofNat 64 calleeNeed =
      (hwSp - BitVec.ofNat 64 A.abi.raBytes) - BitVec.ofNat 64 cb := by
    rw [show calleeNeed = A.abi.raBytes + cb from rfl]
    exact (sub_sub_eq_sub_add hwSp (x := A.abi.raBytes) (y := cb) (by omega)).symm
  rw [hsp_c] at hsub2
  rw [← hsp_c] at hsub2
  rw [hsub1, hsub2,
    show calleeNeed - A.abi.raBytes = cb by dsimp only [calleeNeed]; omega, hsp_c]

def contMemPred (isMF : Bool) (mL0 : Mem 64) : Mem 64 → Prop :=
  if isMF then emp else Eq mL0

theorem contMemPred_eq (isMF : Bool) (mL0 : Mem 64) :
    contMemPred isMF mL0 = Eq (if isMF then (∅ : Mem 64) else mL0) := by
  cases isMF <;> simp [contMemPred, eq_empty_eq_emp]

theorem contified_epilogue_ret_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (_hwf : b.Wf) {symAddr : Sym → BitVec 64} {needFC : Bool} {nsC cb : Nat}
    {hwSpC sp_c ra_c : BitVec 64} {slots : List (BitVec 64)} {G_ret G_outer : Mem 64 → Prop}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)} {s_fin : MachSt A}
    (hself : needFC = true → A.abi.frameSize nsC ≤ cb)
    (hbdC : cb + A.abi.raBytes ≤ 2 ^ 64)
    (hhw : needFC = true → hwSpC = sp_c - BitVec.ofNat 64 (A.abi.frameSize nsC))
    (hhw0 : needFC = false → hwSpC = sp_c)
    (hlen : slots.length = if needFC then nsC else 0)
    (hra0 : needFC = false → (vllFramePreds A).raReg s_fin ra_c)
    (hsp : s_fin.gpr A.abi.sp = hwSpC)
    (hm : s_fin.mem =⋆ array64 hwSpC slots ⋆
      (if needFC then
        ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
          region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ G_ret ⋆ G_outer)
      else
        ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
          G_ret ⋆ G_outer)))
    (hk : ∀ s_ret : MachSt A,
      (∀ q, q ≠ A.abi.sp → q ∉ A.abi.raRegs → s_ret.gpr q = s_fin.gpr q) →
      s_ret.gpr A.abi.sp = sp_c + BitVec.ofNat 64 A.abi.raBytes →
      (s_ret.mem =⋆ region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ G_ret ⋆ G_outer) →
      Ψ_L1 ra_c s_ret) :
    bodyWp A symAddr (if needFC then [.epilogue nsC] else [])
      (fun s' => termWp A symAddr .ret Ψ_L1 H_L1 s') Ψ_L1 H_L1 s_fin := by
  have finishRet : ∀ (s' : MachSt A),
      (∀ q, q ≠ A.abi.sp → q ∉ A.abi.raRegs → s'.gpr q = s_fin.gpr q) →
      s'.gpr A.abi.sp = sp_c →
      (vllFramePreds A).raReg s' ra_c →
      (s'.mem =⋆ (vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
        G_ret ⋆ G_outer) →
      termWp A symAddr .ret Ψ_L1 H_L1 s' := by
    intro s' hkeep' hsp' hra' hm'
    have hm_reg : s'.mem =⋆ region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆
        G_ret ⋆ G_outer := by
      have hm0 : ((vllFramePreds A).RetAddr sp_c ra_c ⋆
          (region (sp_c - BitVec.ofNat 64 cb) cb ⋆ G_ret ⋆ G_outer)) s'.mem :=
        sep_cast hm' (by ac_rfl)
      have h1 := sep_mono (retAddr_merge_region A sp_c ra_c) hm0
      have hspC : sp_c - BitVec.ofNat 64 cb + BitVec.ofNat 64 cb = sp_c := BitVec.sub_add_cancel _ _
      rw [region_split hbdC, hspC]
      exact sep_cast h1 (by ac_rfl)
    cases hkind : A.abi.raKind with
    | linkReg lr =>
      refine termWp_ret_linkReg hkind ?_
      have hlr : s'.gpr lr = ra_c := by simpa [vllFramePreds, hkind] using hra'
      rw [hlr]
      exact hk s' hkeep' (by simp [Abi.raBytes, hkind, RaKind.raBytes, hsp']) hm_reg
    | stack =>
      have hm_cell : (cell64 sp_c ra_c ⋆ (region (sp_c - BitVec.ofNat 64 cb) cb ⋆
          G_ret ⋆ G_outer)) s'.mem := by
        exact sep_cast (by simpa [vllFramePreds, hkind] using hm') (by ac_rfl)
      have hld : loadVal s'.mem i64 (s'.gpr A.abi.sp) = some ra_c := by
        rw [hsp']; exact loadVal_cell64 hm_cell
      refine termWp_ret_stack hkind hld ?_
      refine hk (s'.setGpr A.abi.sp (s'.gpr A.abi.sp + 8#64))
        (fun q hq _ => (MachSt.gpr_setGpr_ne _ _ hq).trans (hkeep' q hq (by assumption)))
        (by simp [hsp', Abi.raBytes, hkind, RaKind.raBytes])
        (by simpa [MachSt.mem_setGpr] using hm_reg)
  by_cases hnf : needFC = true
  · simp only [hnf, ↓reduceIte] at hlen hm ⊢
    have hfsz_le := hself hnf
    have hhw_eq := hhw hnf
    have hcan : s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize nsC) = sp_c := by
      rw [hsp, hhw_eq]; exact BitVec.sub_add_cancel _ _
    have hbd_ep : A.abi.frameSize nsC + A.abi.raBytes ≤ 2 ^ 64 := by omega
    have hm_ep : s_fin.mem =⋆ array64 (s_fin.gpr A.abi.sp) slots ⋆
        (vllFramePreds A).Saved
          (s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize nsC)) ra_c nsC ⋆
        (region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ G_ret ⋆ G_outer) := by
      have hm0 : (array64 (s_fin.gpr A.abi.sp) slots ⋆
          ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
            region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ G_ret ⋆ G_outer))
          s_fin.mem := hsp ▸ hm
      have hSavedEq : (vllFramePreds A).Saved sp_c ra_c nsC =
          (vllFramePreds A).Saved (s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize nsC))
            ra_c nsC := by rw [hcan]
      rw [hSavedEq] at hm0
      exact sep_cast hm0 (by ac_rfl)
    refine instrWp_epilogue hawf hlen hbd_ep hm_ep ?_
    intro s' hsp' hra' hkeep' _ hmPost
    have hsp'' : s'.gpr A.abi.sp = sp_c := hsp'.trans hcan
    have hm'' : s'.mem =⋆ (vllFramePreds A).RetAddr sp_c ra_c ⋆
        region (sp_c - BitVec.ofNat 64 cb) cb ⋆ G_ret ⋆ G_outer := by
      rw [hsp''] at hmPost
      have hsp_sub := region_sub_split (a := sp_c) hfsz_le (by omega)
      rw [hsp_sub]
      exact sep_cast hmPost (by ac_rfl)
    exact finishRet s' hkeep' hsp'' hra' hm''
  · have hnfF : needFC = false := Bool.eq_false_iff.mpr hnf
    simp only [hnfF, Bool.false_eq_true, ↓reduceIte] at hlen hm ⊢
    dsimp only [bodyWp]
    have hslNil : slots = [] := List.eq_nil_of_length_eq_zero hlen
    subst hslNil
    have hm' : ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
        G_ret ⋆ G_outer) s_fin.mem := by
      rw [hhw0 hnfF, array64_nil] at hm
      have hm0 : (emp ⋆ ((vllFramePreds A).RetAddr sp_c ra_c ⋆
          region (sp_c - BitVec.ofNat 64 cb) cb ⋆ G_ret ⋆ G_outer)) s_fin.mem :=
        sep_cast hm (by ac_rfl)
      rw [emp_sep] at hm0; exact hm0
    exact finishRet s_fin (fun _ _ _ => rfl) (hsp.trans (hhw0 hnfF)) (hra0 hnfF) hm'

private theorem array64_saved_rem_to_region (A : Arch) (hwf : A.Wf)
    {sp0 hwSp : BitVec 64} {slots : List (BitVec 64)} {ra : BitVec 64}
    {ns budget : Nat} (hlen : slots.length = ns)
    (hle : A.abi.frameSize ns ≤ budget) (hbd : budget + A.abi.raBytes ≤ 2 ^ 64)
    (hhw : hwSp = sp0 - BitVec.ofNat 64 (A.abi.frameSize ns)) :
    ∀ m, (array64 hwSp slots ⋆
        ((vllFramePreds A).Saved sp0 ra ns ⋆
          region (sp0 - BitVec.ofNat 64 budget) (budget - A.abi.frameSize ns))) m →
      region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) m := by
  intro m hm
  have hsl := hwf.slots_le_frameSize ns
  have hfsBd : A.abi.frameSize ns + A.abi.raBytes ≤ 2 ^ 64 := by omega
  have h8ns : 8 * slots.length ≤ 2 ^ 64 := by rw [hlen]; omega
  have harr : ∀ m', array64 hwSp slots m' → region hwSp (8 * ns) m' := by
    intro m' ha; simpa [hlen] using array64_region h8ns ha
  have hSav : ∀ m', (vllFramePreds A).Saved sp0 ra ns m' →
      region (hwSp + BitVec.ofNat 64 (8 * ns))
        (A.abi.frameSize ns - 8 * ns + A.abi.raBytes) m' := by
    intro m' hm'
    rw [hhw]
    cases hkind : A.abi.raKind <;>
      simp only [vllFramePreds, hkind, Abi.raBytes, RaKind.raBytes] at hm' ⊢
    · have hrb : A.abi.raBytes = 8 := by simp [Abi.raBytes, hkind, RaKind.raBytes]
      have hm'' := sep_mono_r (fun _ => cell64_region) hm'
      have hsp : (sp0 - BitVec.ofNat 64 (A.abi.frameSize ns) + BitVec.ofNat 64 (8 * ns)) +
          BitVec.ofNat 64 (A.abi.frameSize ns - 8 * ns) = sp0 := by
        apply BitVec.eq_of_toNat_eq
        have hs := sp0.isLt
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
      rw [region_split (by omega), hsp]
      exact hm''
    · have hlr := hwf.linkReg_frameSize _ hkind ns
      have hra0 : A.abi.raBytes = 0 := by simp [Abi.raBytes, hkind, RaKind.raBytes]
      have hm'' := sep_mono (fun _ => cell64_region) hm'
      have hheq : A.abi.frameSize ns - 8 * ns + 0 =
          8 + (A.abi.frameSize ns - 8 * ns - 8) := by omega
      rw [hheq, region_split (by rw [hra0] at hfsBd; omega)]
      exact hm''
  have h1 : (region hwSp (8 * ns) ⋆
      (region (hwSp + BitVec.ofNat 64 (8 * ns)) (A.abi.frameSize ns - 8 * ns + A.abi.raBytes) ⋆
        region (sp0 - BitVec.ofNat 64 budget) (budget - A.abi.frameSize ns))) m :=
    sep_mono harr (sep_mono_r (fun _ => sep_mono hSav) hm)
  have h2 : (region hwSp (A.abi.frameSize ns + A.abi.raBytes) ⋆
      region (sp0 - BitVec.ofNat 64 budget) (budget - A.abi.frameSize ns)) m := by
    have hsp1 : A.abi.frameSize ns + A.abi.raBytes =
        8 * ns + (A.abi.frameSize ns - 8 * ns + A.abi.raBytes) := by omega
    rw [hsp1, region_split (by omega)]
    exact sep_cast h1 (by ac_rfl)
  have hsum : budget + A.abi.raBytes =
      (budget - A.abi.frameSize ns) + (A.abi.frameSize ns + A.abi.raBytes) := by omega
  have hsp2 : sp0 - BitVec.ofNat 64 budget + BitVec.ofNat 64 (budget - A.abi.frameSize ns) =
      hwSp := by
    rw [hhw]
    apply BitVec.eq_of_toNat_eq
    have hs := sp0.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [hsum, region_split (by omega), hsp2]
  exact sep_cast h2 (by ac_rfl)

theorem noHaltBlock_of_blockNoMem :
    ∀ blk : BlockFlat, blockNoMem blk = true → noHaltBlock blk = true
  | .let_ _ k => fun h => noHaltBlock_of_blockNoMem k h
  | .load _ _ _ => fun h => by simp [blockNoMem] at h
  | .store _ _ _ => fun h => by simp [blockNoMem] at h
  | .codeAddr _ k => fun h => noHaltBlock_of_blockNoMem k h
  | .jnz _ t e => fun h => by
    dsimp only [blockNoMem] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨ht, he⟩
    simp [noHaltBlock, noHaltBlock_of_blockNoMem t ht, noHaltBlock_of_blockNoMem e he]
  | .ijmp _ _ => fun _ => rfl
  | .halt _ => fun h => by simp [blockNoMem] at h
  | .hlt => fun _ => rfl

private theorem blockFlat_wp_noMem_sp {cm : CodeMap} {pf : PrivFrameCfg}
    {Ψ : BedrockWord.CodeSpec} {H₁ H₂ : HaltPost} {sp0 rp0 : BitVec 64} (m₁ m₂ : Mem 64) :
    ∀ (blk : BlockFlat) (path : BranchPath) (st : ContSymState)
      (bvs : List ((t : Ty) × Val t)) (leaves : List ContSymLeaf),
      blockNoMem blk = true →
      ContSymStateOk bvs sp0 rp0 st →
      symEvalContBlock cm pf blk path st = some leaves →
      (∀ lf ∈ leaves, (lf.st.evalArg lf.nextRegs.sp == .spOffset 0#64) = true) →
      blk.wp cm.symEnv Ψ H₁ bvs m₁ →
      blk.wp cm.symEnv (fun q st' => Ψ q ⟨st'.regs, m₁⟩ ∧ st'.regs.sp = sp0 ∧ st'.mem = m₂)
        H₂ bvs m₂
  | .let_ op k, path, st, bvs, leaves, hnm, hst, hsym, hspLf, hwp => by
    dsimp only [BlockFlat.wp] at hwp ⊢
    cases hargs : denoteArgs bvs op.args <;> rw [hargs] at hwp; · exact hwp
    dsimp only [symEvalContBlock] at hsym
    exact evalContOp_wp_mono op hst hargs
      (fun _ hk hst' =>
        blockFlat_wp_noMem_sp m₁ m₂ k path _ _ leaves hnm hst' hsym hspLf hk) hwp
  | .load _ _ _, _, _, _, _, hnm, _, _, _, _ => by simp [blockNoMem] at hnm
  | .store _ _ _, _, _, _, _, hnm, _, _, _, _ => by simp [blockNoMem] at hnm
  | .codeAddr sym k, path, st, bvs, leaves, hnm, hst, hsym, hspLf, hwp => by
    obtain ⟨a, ha, hk⟩ := hwp
    dsimp only [symEvalContBlock] at hsym
    change (match cm.symEnv sym with | some a => _ | none => none) = some leaves at hsym
    rw [ha] at hsym
    let sv := if (a &&& 7#64) == 0#64 then ContSymVal.alignedConst a else .const a
    have hsvOk : ContSymValMatch (⟨i64, a⟩ :: bvs) sp0 rp0 sv i64 a := by
      dsimp only [sv]; split
      · rename_i h0; exact fun _ => ⟨rfl, beq_iff_eq.mp h0⟩
      · exact fun _ => rfl
    exact ⟨a, ha, blockFlat_wp_noMem_sp m₁ m₂ k path _ _ leaves hnm
      (contSymStateOk_cons (t := i64) a sv hst hsvOk) hsym hspLf hk⟩
  | .jnz c t e, path, st, bvs, leaves, hnm, hst, hsym, hspLf, hwp => by
    dsimp only [blockNoMem] at hnm
    rcases Bool.and_eq_true_iff.mp hnm with ⟨hnt, hne⟩
    dsimp only [BlockFlat.wp] at hwp ⊢
    cases hdc : denoteArg bvs c <;> rw [hdc] at hwp; · exact hwp
    rename_i c'; rcases hwp with ⟨ht, hf⟩
    dsimp only [symEvalContBlock, Bind.bind, Option.bind] at hsym
    cases hstT : symEvalContBlock cm pf t (path ++ [true]) (st.pushCondFact c true) with
    | none => rw [hstT] at hsym; cases hsym
    | some lt =>
      rw [hstT] at hsym
      cases hstE : symEvalContBlock cm pf e (path ++ [false]) (st.pushCondFact c false) with
      | none => rw [hstE] at hsym; cases hsym
      | some le =>
        rw [hstE] at hsym; cases hsym
        exact ⟨fun htr => blockFlat_wp_noMem_sp m₁ m₂ t (path ++ [true]) _ bvs lt hnt
            (pushContCondFact_sound hst hdc true htr) hstT
            (fun lf hl => hspLf lf (List.mem_append_left _ hl)) (ht htr),
          fun hfl => blockFlat_wp_noMem_sp m₁ m₂ e (path ++ [false]) _ bvs le hne
            (pushContCondFact_sound hst hdc false hfl) hstE
            (fun lf hl => hspLf lf (List.mem_append_right _ hl)) (hf hfl)⟩
  | .ijmp tgt nxt, path, st, bvs, leaves, _, hst, hsym, hspLf, hwp => by
    dsimp only [symEvalContBlock] at hsym; cases hsym
    dsimp only [BlockFlat.wp] at hwp ⊢
    cases hdt : denoteArg bvs tgt <;> rw [hdt] at hwp; · exact hwp
    cases hdn : denoteRegsExpr bvs nxt <;> rw [hdn] at hwp; · exact hwp
    rename_i tgt' nxt'
    have hspArg : ∃ spv : Arg Val i64, denoteArg bvs nxt.sp = some spv ∧
        nxt'.eval.sp = spv.val := by
      dsimp only [denoteRegsExpr] at hdn
      cases h0 : denoteArg bvs nxt.sp <;> rw [h0] at hdn; · cases hdn
      cases h1 : denoteArg bvs nxt.rp <;> rw [h1] at hdn; · cases hdn
      cases h2 : denoteArg bvs nxt.rv <;> rw [h2] at hdn; · cases hdn
      cases h3 : denoteArg bvs nxt.r1 <;> rw [h3] at hdn; · cases hdn
      cases h4 : denoteArg bvs nxt.r2 <;> rw [h4] at hdn; · cases hdn
      cases h5 : denoteArg bvs nxt.r3 <;> rw [h5] at hdn; · cases hdn
      cases hdn; exact ⟨_, rfl, rfl⟩
    obtain ⟨spv, hspv, hspEval⟩ := hspArg
    have hmSp := evalContArg_symValMatch hst hspv
    rw [beq_iff_eq.mp (hspLf ⟨path, st, tgt, nxt⟩ List.mem_cons_self)] at hmSp
    have hsp0 : spv.val = sp0 + 0#64 := hmSp rfl
    exact ⟨hwp, by simpa [hspEval] using hsp0, rfl⟩
  | .halt _, _, _, _, _, hnm, _, _, _, _ => by simp [blockNoMem] at hnm
  | .hlt, _, _, _, _, _, _, _, _, hwp => False.elim hwp

theorem regionMemFree_block_wp {cm : CodeMap} {callees : List ContCalleeMeta}
    {cr : ContifyRegion} (hmf : regionMemFree cm callees cr = true)
    {pc : BitVec 64} (hpc : pc ∈ cr.allPcs) {blk : BlockFlat}
    (hlu : cm.lookupAddr pc = some blk) {rw : Regs} {m₁ m₂ : Mem 64}
    {Ψ : BedrockWord.CodeSpec} {H₁ H₂ : HaltPost}
    (hwp : blk.wp cm.symEnv Ψ H₁ (pushRegsV rw.toRegsV) m₁) :
    blk.wp cm.symEnv (fun q st' => Ψ q ⟨st'.regs, m₁⟩ ∧ st'.regs.sp = rw.sp ∧ st'.mem = m₂) H₂
      (pushRegsV rw.toRegsV) m₂ := by
  dsimp only [regionMemFree] at hmf
  have h1 := List.all_eq_true.mp hmf pc hpc
  rw [hlu] at h1
  rcases Bool.and_eq_true_iff.mp h1 with ⟨hnm, hsymB⟩
  cases hsym : symEvalContBlock cm cr.privFrame blk [] ContSymState.init with
  | none => rw [hsym] at hsymB; cases hsymB
  | some leaves =>
    rw [hsym] at hsymB
    have hspLf : ∀ lf ∈ leaves, (lf.st.evalArg lf.nextRegs.sp == .spOffset 0#64) = true :=
      fun lf hlf => (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hsymB lf hlf)).1
    exact blockFlat_wp_noMem_sp m₁ m₂ blk [] ContSymState.init (pushRegsV rw.toRegsV) leaves hnm
      (contSymStateOk_init rw) hsym hspLf hwp

theorem checkContBlockLeaves_facts {cm : CodeMap} {cr : ContifyRegion}
    {callees : List ContCalleeMeta} {pcs : List (BitVec 64)} {pc : BitVec 64}
    {blk : BlockFlat} (hlu : cm.lookupAddr pc = some blk)
    (hchk : checkContBlockLeaves cm cr callees pcs pc = true) :
    blk.Wf ∧
    (symEvalContBlock cm cr.privFrame blk [] ContSymState.init).isSome = true ∧
    ∀ lf ∈ (symEvalContBlock cm cr.privFrame blk [] ContSymState.init).getD [],
      ∃ ew, cr.toRegionWitness.findEdge pc lf.path = some ew ∧
        checkContEdgeLeaf cm cr.abi cr.privFrame callees pcs lf ew.kind = true := by
  dsimp only [checkContBlockLeaves] at hchk
  rw [hlu] at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨hwc, _⟩, hrest⟩
  refine ⟨hwc, ?_⟩
  cases hsym : symEvalContBlock cm cr.privFrame blk [] ContSymState.init with
  | none => rw [hsym] at hrest; cases hrest
  | some leaves =>
    rw [hsym] at hrest
    refine ⟨rfl, fun lf hlf => ?_⟩
    have ha := List.all_eq_true.mp hrest lf hlf
    cases hfe : cr.toRegionWitness.findEdge pc lf.path with
    | none => rw [hfe] at ha; cases ha
    | some ew => rw [hfe] at ha; exact ⟨ew, rfl, ha⟩

private theorem codeMap_entry_eq_of_lookup {cm : CodeMap} (hnd : cm.AddrsNodup)
    {e : CodeEntry} (he : e ∈ cm) {blk : BlockFlat} (hlu : cm.lookupAddr e.addr = some blk) :
    e.block = blk := by
  induction cm with
  | nil => cases he
  | cons x xs ih =>
    dsimp only [CodeMap.AddrsNodup, List.map_cons] at hnd
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp he with rfl | htail
    · simp only [CodeMap.lookupAddr, beq_self_eq_true, ↓reduceIte] at hlu
      cases hlu; rfl
    · have hne : x.addr ≠ e.addr := fun h => hnd'.1 (List.mem_map.mpr ⟨e, htail, h.symm⟩)
      simp only [CodeMap.lookupAddr, beq_false_of_ne hne, Bool.false_eq_true, ↓reduceIte] at hlu
      exact ih hnd'.2 htail hlu

theorem regionFrame_bounds {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {cr : ContifyRegion} {callees : List ContCalleeMeta} (hchk : cr.check cm callees = true)
    {pc : BitVec 64} (hpc : pc ∈ cr.allPcs) {blk : BlockFlat} (hlu : cm.lookupAddr pc = some blk) :
    let dMax := regionMaxDepth cm cr
    let needF := regionNeedFrame b cm cr
    let ns := regionFrameSlots b cm cr
    let ns_ := if needF then ns else 0
    let spillBase := regionSpillBase cr
    6 ≤ dMax ∧ maxBlockDepth blk 6 ≤ dMax ∧
    cr.privFrame.numSlots ≤ 64 ∧
    (cr.privFrame.numSlots > 0 → cr.abi = .retEnvelope) ∧
    (regionHasCalls cr = true → needF = true) ∧
    (cr.privFrame.numSlots > 0 → cr.privFrame.numSlots + 1 ≤ spillBase) ∧
    spillBase + tempSpillCount b dMax ≤ ns_ ∧
    (needF = false → cr.privFrame.numSlots = 0 ∧ ns = 0) := by
  obtain ⟨hd6, hdMax⟩ := regionMaxDepth_ge hpc hlu
  obtain ⟨h64, hEnv⟩ := checkContRegion_priv_facts hchk
  have hnfFalse : regionNeedFrame b cm cr = false →
      cr.privFrame.numSlots = 0 ∧ regionFrameSlots b cm cr = 0 := by
    intro hnfF
    dsimp only [regionNeedFrame] at hnfF
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero] at hnfF
    exact ⟨hnfF.1.1, by simp [regionFrameSlots, regionSpillBase, hnfF.1.1, hnfF.1.2]⟩
  refine ⟨hd6, hdMax, h64, hEnv, fun hc => by simp [regionNeedFrame, hc],
    fun hp => by simp [regionSpillBase, hp], ?_, hnfFalse⟩
  by_cases hnf : regionNeedFrame b cm cr = true
  · simp only [hnf, ↓reduceIte]
    dsimp only [regionFrameSlots, regionSpillBase]
    split <;> omega
  · have hnfF : regionNeedFrame b cm cr = false := Bool.eq_false_iff.mpr hnf
    obtain ⟨hp0, _⟩ := hnfFalse hnfF
    have hs0 : tempSpillCount b (regionMaxDepth cm cr) = 0 := by
      dsimp only [regionNeedFrame] at hnfF
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero] at hnfF
      exact hnfF.1.2
    simp [hnfF, regionSpillBase, hp0, hs0]

theorem checkContRegion_pcs_mem {cm : CodeMap} {cr : ContifyRegion}
    {callees : List ContCalleeMeta} (_hchk : cr.check cm callees = true) :
    ∀ {pcs : List (BitVec 64)} {p : BitVec 64},
      (∀ q ∈ pcs, q ∈ cr.allPcs) → (findLabelIdx pcs p).isSome = true → p ∈ cr.allPcs := by
  intro pcs p hp hfind
  rcases Option.isSome_iff_exists.mp hfind with ⟨_, hEq⟩
  exact hp p (mem_of_findLabelIdx hEq)

private def ContifySpecPred (_A : Arch) : Type := BitVec 64 × BedrockWord.State → Prop

private def ResEntryConj (A : Arch) (b : WordRegBind A) (cm : CodeMap) (wit : ContifyWitness)
    (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop)
    (Ψ_L1 : Xcap.CodeSpec (MachSt A)) (pc : BitVec 64) (st : BedrockWord.State) : Prop :=
  ∀ e ∈ residualContifyCodeMap cm wit, e.addr = pc →
    ∀ s, WordPlainAnchorRel b st sp0 ra0 budget R s → Ψ_L1 pc s

private def RetEnvExtConj (A : Arch) (b : WordRegBind A) (_cm : CodeMap) (wit : ContifyWitness)
    (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop)
    (Ψ_L1 : Xcap.CodeSpec (MachSt A)) (pc : BitVec 64) (st : BedrockWord.State) : Prop :=
  ∀ cr ∈ wit.regions, cr.abi = .retEnvelope → cr.entryPc = pc →
    (cr.privFrame.numSlots > 0 → st.regs.sp = sp0 ∧ cr.privFrame.numSlots ≤ 64 ∧
      ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k)) →
    ∀ s, WordPlainAnchorRel b st sp0 ra0 budget R s → Ψ_L1 pc s

private def RetEnvIntConj (A : Arch) (b : WordRegBind A) (cm : CodeMap) (wit : ContifyWitness)
    (vcm : VllCodeMap A) (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop)
    (Ψ_L1 : Xcap.CodeSpec (MachSt A)) (pc : BitVec 64) (st : BedrockWord.State) : Prop :=
  ∀ cr ∈ wit.regions, cr.abi = .retEnvelope → pc ∈ cr.allPcs →
    let nPriv := cr.privFrame.numSlots
    let needF := regionNeedFrame b cm cr
    let ns := regionFrameSlots b cm cr
    let selfF := if needF then A.abi.frameSize ns else 0
    ∀ (sp_in ra_in : BitVec 64) (mPub : Mem 64) (slots : List (BitVec 64)) (s : MachSt A),
      (needF = true ∨ budget > 0 → sp_in = sp0 ∧ ra_in = ra0) →
      let hwSp := if needF then sp0 - BitVec.ofNat 64 selfF else sp_in
      let G :=
        if needF then (vllFramePreds A).Saved sp0 ra0 ns ⋆
          region (sp0 - BitVec.ofNat 64 budget) (budget - selfF) ⋆ R
        else if budget = 0 then R else hwStackMem A sp0 ra0 budget ⋆ R
      slots.length = (if needF then ns else 0) →
      WordRegsRel b st.regs s →
      (nPriv > 0 → st.regs.sp = sp0) →
      (needF = false → (vllFramePreds A).raReg s ra_in) →
      s.gpr A.abi.sp = hwSp →
      Stage1PrivSlots nPriv sp0 slots st.mem mPub →
      (array64 hwSp slots ⋆ (Eq mPub ⋆ G)) s.mem →
      Ψ_L1 (vcm.symAddr (innerLabel cr pc)) s

private def ContifyNode (A : Arch) (b : WordRegBind A) (cm : CodeMap) (wit : ContifyWitness)
    (vcm : VllCodeMap A) (H_L0 : HaltPost) (Ψ_L1 : Xcap.CodeSpec (MachSt A))
    (H_L1 : Xcap.Halt (MachSt A)) (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop)
    (Φ : ContifySpecPred A) : ContifySpecPred A := fun (pc, st) =>
  ResEntryConj A b cm wit sp0 ra0 budget R Ψ_L1 pc st ∧
  RetEnvExtConj A b cm wit sp0 ra0 budget R Ψ_L1 pc st ∧
  RetEnvIntConj A b cm wit vcm sp0 ra0 budget R Ψ_L1 pc st ∧
  (∀ pre cr post, wit.regions = pre ++ cr :: post → ∀ dualRet,
    cr.abi = .contified dualRet → pc ∈ cr.allPcs →
    let needF := regionNeedFrame b cm cr
    let ns := regionFrameSlots b cm cr
    let isMF := regionMemFree cm (foldCallees cm [] pre) cr
    ∀ (sp0_c rp0 ra_ret hwSp : BitVec 64) (slots : List (BitVec 64)) (G : Mem 64 → Prop)
      (s : MachSt A),
      (isMF = true → st.regs.sp = sp0_c) →
      st.regs.rp = rp0 →
      slots.length = (if needF then ns else 0) →
      WordRegsRel b st.regs s →
      (needF = false → (vllFramePreds A).raReg s ra_ret) →
      s.gpr A.abi.sp = hwSp →
      (array64 hwSp slots ⋆ (contMemPred isMF st.mem ⋆ G)) s.mem →
      (∀ (isAlt : Bool) (s_fin : MachSt A) (nxt' : Regs) (m' : Mem 64)
        (slots' : List (BitVec 64)),
        (isAlt = true → dualRet = true) →
        (isMF = true → m' = st.mem) →
        (isMF = true → nxt'.sp = sp0_c) →
        slots'.length = (if needF then ns else 0) →
        WordRegsRel b nxt' s_fin →
        (dualRet = true → ValHolds64 .bool isAlt (s_fin.gpr b.altRet)) →
        (needF = false → (vllFramePreds A).raReg s_fin ra_ret) →
        s_fin.gpr A.abi.sp = hwSp →
        (array64 hwSp slots' ⋆ (contMemPred isMF m' ⋆ G)) s_fin.mem →
        Φ (rp0 + (if isAlt then 8#64 else 0#64), ⟨nxt', m'⟩) →
        bodyWp A vcm.symAddr (if needF then [.epilogue ns] else [])
          (fun s' => termWp A vcm.symAddr .ret Ψ_L1 H_L1 s') Ψ_L1 H_L1 s_fin) →
      (isMF = false →
        (∃ pc_h ∈ cr.allPcs, ∃ blk_h, cm.lookupAddr pc_h = some blk_h ∧
          noHaltBlock blk_h = false) →
        ∀ (s_fin : MachSt A) (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
          slots'.length = (if needF then ns else 0) →
          s_fin.gpr b.w0 = cVal → s_fin.gpr A.abi.sp = hwSp →
          (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
          H_L0 cVal m' →
          bodyWp A vcm.symAddr (if needF then [.epilogue ns] else [])
            (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin) →
      Ψ_L1 (vcm.symAddr (innerLabel cr pc)) s)

private theorem contifyNode_mono (A : Arch) (b : WordRegBind A) (cm : CodeMap)
    (wit : ContifyWitness) (vcm : VllCodeMap A) (H_L0 : HaltPost)
    (Ψ_L1 : Xcap.CodeSpec (MachSt A)) (H_L1 : Xcap.Halt (MachSt A))
    (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop) :
    Xcap.Lfp.mono (ContifyNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R) := by
  show Xcap.Lfp.mono (ContifyNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R)
  rintro Φ₁ Φ₂ hle ⟨pc, st⟩ ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, fun pre cr post hs dual habi hpc sp0_c rp0 ra hwSp slots G s
      hsp0C hrp hlen hr hra hsp hm hRet hHalt =>
    h4 pre cr post hs dual habi hpc sp0_c rp0 ra hwSp slots G s hsp0C hrp hlen hr hra hsp hm
      (fun isAlt s_f nxt' m' sl' ha hm' hsp' hl hr' hdu hra' hsp'' hm'' hPhi =>
        hRet isAlt s_f nxt' m' sl' ha hm' hsp' hl hr' hdu hra' hsp'' hm'' (hle _ hPhi))
      hHalt⟩

private def ContifyOpenNode (A : Arch) (b : WordRegBind A) (cm : CodeMap)
    (wit : ContifyWitness) (vcm : VllCodeMap A) (H_L0 : HaltPost)
    (Ψ_L1 : Xcap.CodeSpec (MachSt A)) (H_L1 : Xcap.Halt (MachSt A))
    (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop)
    (ExtSpec Inv : BedrockWord.CodeSpec) (Φ : ContifySpecPred A) : ContifySpecPred A :=
  fun p =>
    (ContifyNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R Φ p ∨
      (cm.lookupAddr p.1 = none ∧ ExtSpec p.1 p.2)) ∧
    Inv p.1 p.2

private theorem contifyOpenNode_mono (A : Arch) (b : WordRegBind A) (cm : CodeMap)
    (wit : ContifyWitness) (vcm : VllCodeMap A) (H_L0 : HaltPost)
    (Ψ_L1 : Xcap.CodeSpec (MachSt A)) (H_L1 : Xcap.Halt (MachSt A))
    (sp0 ra0 : BitVec 64) (budget : Nat) (R : Mem 64 → Prop)
    (ExtSpec Inv : BedrockWord.CodeSpec) :
    Xcap.Lfp.mono
      (ContifyOpenNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv) := by
  intro Φ₁ Φ₂ hle p ⟨hN, hInv⟩
  refine ⟨?_, hInv⟩
  rcases hN with hNode | hE
  · exact Or.inl (contifyNode_mono A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R hle p hNode)
  · exact Or.inr hE

def ContifyFixExt (A : Arch) (b : WordRegBind A) (cm : CodeMap) (wit : ContifyWitness)
    (vcm : VllCodeMap A) (H_L0 : HaltPost) (Ψ_L1 : Xcap.CodeSpec (MachSt A))
    (H_L1 : Xcap.Halt (MachSt A)) (sp0 ra0 : BitVec 64) (budget : Nat)
    (R : Mem 64 → Prop) (ExtSpec Inv : BedrockWord.CodeSpec) : BedrockWord.CodeSpec :=
  fun pc st => Xcap.Lfp.lfp
    (ContifyOpenNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv) (pc, st)

def ContifyFix (A : Arch) (b : WordRegBind A) (cm : CodeMap) (wit : ContifyWitness)
    (vcm : VllCodeMap A) (H_L0 : HaltPost) (Ψ_L1 : Xcap.CodeSpec (MachSt A))
    (H_L1 : Xcap.Halt (MachSt A)) (sp0 ra0 : BitVec 64) (budget : Nat)
    (R : Mem 64 → Prop) : BedrockWord.CodeSpec :=
  ContifyFixExt A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R
    (fun _ _ => False) (fun _ _ => True)

theorem contified_epilogue_halt_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {symAddr : Sym → BitVec 64} {needFC : Bool} {nsC cb : Nat}
    {hwSpC sp_c ra_c cVal : BitVec 64} {slots : List (BitVec 64)} {G_outer : Mem 64 → Prop}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)} {s_fin : MachSt A}
    (hself : needFC = true → A.abi.frameSize nsC ≤ cb)
    (hbdC : cb + A.abi.raBytes ≤ 2 ^ 64)
    (hhw : needFC = true → hwSpC = sp_c - BitVec.ofNat 64 (A.abi.frameSize nsC))
    (hhw0 : needFC = false → hwSpC = sp_c)
    (hlen : slots.length = if needFC then nsC else 0)
    (hsp : s_fin.gpr A.abi.sp = hwSpC)
    (hw0 : s_fin.gpr b.w0 = cVal)
    (hm : s_fin.mem =⋆ array64 hwSpC slots ⋆
      (if needFC then
        ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
          region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ G_outer)
      else
        ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
          G_outer)))
    (hk : ∀ s' : MachSt A, s'.gpr b.w0 = cVal →
      (s'.mem =⋆ region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ G_outer) →
      H_L1 cVal s') :
    bodyWp A symAddr (if needFC then [.epilogue nsC] else [])
      (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin := by
  by_cases hnf : needFC = true
  · simp only [hnf, ↓reduceIte] at hlen hm ⊢
    have hfsz_le := hself hnf
    have hcan : s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize nsC) = sp_c := by
      rw [hsp, hhw hnf]; exact BitVec.sub_add_cancel _ _
    have hm_ep : s_fin.mem =⋆ array64 (s_fin.gpr A.abi.sp) slots ⋆
        (vllFramePreds A).Saved
          (s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize nsC)) ra_c nsC ⋆
        (region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ G_outer) := by
      have hm0 : (array64 (s_fin.gpr A.abi.sp) slots ⋆
          ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
            region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ G_outer))
          s_fin.mem := hsp ▸ hm
      have hSavedEq : (vllFramePreds A).Saved sp_c ra_c nsC =
          (vllFramePreds A).Saved (s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize nsC))
            ra_c nsC := by rw [hcan]
      rw [hSavedEq] at hm0
      exact sep_cast hm0 (by ac_rfl)
    refine instrWp_epilogue hawf hlen (by omega) hm_ep ?_
    intro s' hsp' _ hkeep' _ hmPost
    have hw0_s' : s'.gpr b.w0 = cVal :=
      (hkeep' b.w0 (work_not_sp hwf).2.1 (work_not_ra hwf).2.1).trans hw0
    have hsp'' : s'.gpr A.abi.sp = sp_c := hsp'.trans hcan
    have hm_reg : s'.mem =⋆ region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆
        G_outer := by
      rw [hsp''] at hmPost
      have hm0 : ((vllFramePreds A).RetAddr sp_c ra_c ⋆
          (region (sp_c - BitVec.ofNat 64 (A.abi.frameSize nsC)) (A.abi.frameSize nsC) ⋆
            region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ G_outer)) s'.mem :=
        sep_cast hmPost (by ac_rfl)
      have hm1 := sep_mono (retAddr_merge_region A sp_c ra_c) hm0
      have hsp_sub := region_sub_split (a := sp_c) hfsz_le (by omega)
      have hsp_cb : sp_c - BitVec.ofNat 64 cb + BitVec.ofNat 64 cb = sp_c :=
        BitVec.sub_add_cancel _ _
      rw [region_split hbdC, hsp_cb, hsp_sub]
      exact sep_cast hm1 (by ac_rfl)
    dsimp only [bodyWp]
    exact hw0_s'.symm ▸ hk s' hw0_s' hm_reg
  · have hnfF : needFC = false := Bool.eq_false_iff.mpr hnf
    simp only [hnfF, Bool.false_eq_true, ↓reduceIte] at hlen hm ⊢
    dsimp only [bodyWp]
    have hslNil : slots = [] := List.eq_nil_of_length_eq_zero hlen
    subst hslNil
    have hm' : ((vllFramePreds A).RetAddr sp_c ra_c ⋆
        (region (sp_c - BitVec.ofNat 64 cb) cb ⋆ G_outer)) s_fin.mem := by
      rw [hhw0 hnfF, array64_nil] at hm
      have hm0 : (emp ⋆ ((vllFramePreds A).RetAddr sp_c ra_c ⋆
          (region (sp_c - BitVec.ofNat 64 cb) cb ⋆ G_outer))) s_fin.mem :=
        sep_cast hm (by ac_rfl)
      rw [emp_sep] at hm0; exact hm0
    have hm_reg : s_fin.mem =⋆ region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆
        G_outer := by
      have hm1 := sep_mono (retAddr_merge_region A sp_c ra_c) hm'
      have hsp_cb : sp_c - BitVec.ofNat 64 cb + BitVec.ofNat 64 cb = sp_c :=
        BitVec.sub_add_cancel _ _
      rw [region_split hbdC, hsp_cb]
      exact sep_cast hm1 (by ac_rfl)
    exact hw0.symm ▸ hk s_fin hw0 hm_reg

private theorem contify_contCall_discharge {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hvwf : vcm.Wf) (hwck : wit.check cm = true)
    {budget : Nat} (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hEntMem : ∀ cr_c ∈ wit.regions,
      ({ label := cr_c.name, pad? := some b.padKind,
         body := (if regionNeedFrame b cm cr_c then [.prologue (regionFrameSlots b cm cr_c)]
                  else []) ++ emitPrivFrameInit b cr_c.privFrame.numSlots,
         term := .fall (innerLabel cr_c cr_c.entryPc) } : Block A) ∈ vcm.blocks)
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    (hbd : budget + A.abi.raBytes ≤ 2 ^ 64)
    (hHaltC : ∀ cr_c ∈ wit.regions, ∀ dualRet, cr_c.abi = .contified dualRet →
      (∃ pc ∈ cr_c.allPcs, ∃ blk, cm.lookupAddr pc = some blk ∧ noHaltBlock blk = false) →
      ∀ c s, wordHaltPost A H_L0
        (region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R) c s → H_L1 c s)
    {pre : List ContifyRegion} {cr : ContifyRegion} {post : List ContifyRegion}
    (hSplit : wit.regions = pre ++ cr :: post)
    {callee : Sym} {calleePc : BitVec 64} {dualRet : Bool} {retPc : BitVec 64}
    {altRetPc? : Option (BitVec 64)} {tgtLbl : Sym}
    {nxt' : Regs} {slots' : List (BitVec 64)} {mConc' mPub' : Mem 64} {s_call : MachSt A}
    (Φ : ContifySpecPred A)
    (hNF : regionNeedFrame b cm cr = true)
    (hEw : ∃ ew ∈ cr.edges, ew.kind = .contCall callee calleePc dualRet retPc altRetPc?)
    (hCal : (foldCallees cm [] pre).any (fun c =>
      (c.name == callee) && (c.entryPc == calleePc) && (c.dualRet == dualRet)) = true)
    (hMf : cr.privFrame.numSlots > 0 → (foldCallees cm [] pre).any (fun c =>
      (c.name == callee) && (c.entryPc == calleePc) && c.memFree) = true)
    (hRp : nxt'.rp = retPc)
    (hSp : cr.privFrame.numSlots > 0 → nxt'.sp = sp0)
    (hlen : slots'.length = if regionNeedFrame b cm cr then regionFrameSlots b cm cr else 0)
    (hpriv : Stage1PrivSlots cr.privFrame.numSlots sp0 slots' mConc' mPub')
    (hr : WordRegsRel b nxt' s_call)
    (hsp : s_call.gpr A.abi.sp =
      sp0 - BitVec.ofNat 64 (A.abi.frameSize (regionFrameSlots b cm cr)))
    (hm : (array64 (sp0 - BitVec.ofNat 64 (A.abi.frameSize (regionFrameSlots b cm cr))) slots' ⋆
      (Eq mPub' ⋆ ((vllFramePreds A).Saved sp0 ra0 (regionFrameSlots b cm cr) ⋆
        region (sp0 - BitVec.ofNat 64 budget)
          (budget - A.abi.frameSize (regionFrameSlots b cm cr)) ⋆ R))) s_call.mem)
    (hNode : ContifyNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R Φ
      (calleePc, ⟨nxt', mConc'⟩))
    (hCont : Xcap.cptr Ψ_L1 (vcm.symAddr tgtLbl) (fun s_ret =>
      ∃ (isAlt : Bool) (r_ret : Regs) (mConc'' mPub'' : Mem 64),
        (dualRet = false → isAlt = false) ∧
        (dualRet = true → ValHolds64 .bool isAlt (s_ret.gpr b.altRet)) ∧
        WordRegsRel b r_ret s_ret ∧
        Stage1PrivSlots cr.privFrame.numSlots sp0 slots' mConc'' mPub'' ∧
        (cr.privFrame.numSlots > 0 → r_ret.sp = sp0) ∧
        (regionNeedFrame b cm cr = false → (vllFramePreds A).raReg s_ret ra0) ∧
        s_ret.gpr A.abi.sp = sp0 - BitVec.ofNat 64 (A.abi.frameSize (regionFrameSlots b cm cr)) ∧
        (array64 (sp0 - BitVec.ofNat 64 (A.abi.frameSize (regionFrameSlots b cm cr))) slots' ⋆
          (Eq mPub'' ⋆ ((vllFramePreds A).Saved sp0 ra0 (regionFrameSlots b cm cr) ⋆
            region (sp0 - BitVec.ofNat 64 budget)
              (budget - A.abi.frameSize (regionFrameSlots b cm cr)) ⋆ R))) s_ret.mem ∧
        Φ (if isAlt then retPc + 8#64 else retPc, ⟨r_ret, mConc''⟩))) :
    termWp A vcm.symAddr (.call callee tgtLbl) Ψ_L1 H_L1 s_call := by
  obtain ⟨p1, p2, cr_c, hPreEq, rfl, rfl, habiC, hMfC⟩ :=
    foldCallees_callee_match hwck hSplit hCal hMf
  have hcrC : cr_c ∈ wit.regions := pre_region_mem hSplit hPreEq
  have hchkC := witness_checkAux_split (pre := p1) (cr := cr_c) (post := p2 ++ cr :: post)
    hwck (by rw [hSplit, hPreEq]; simp)
  have hPriv0C : cr_c.privFrame.numSlots = 0 := Decidable.byContradiction fun hne => by
    have := (checkContRegion_priv_facts hchkC).2 (Nat.pos_of_ne_zero hne)
    rw [habiC] at this; cases this
  have hEntC : cr_c.entryPc ∈ cr_c.allPcs := checkContRegion_entryPc_mem hchkC
  obtain ⟨ew, hewMem, hewKind⟩ := hEw
  obtain ⟨_, hSelfLe, hEdgeBd⟩ := witnessBudgets_split b cm hwck hSplit
  have hBudC_le := hEdgeBd (by rw [hPreEq]; simp) hewMem hewKind
  have hBudCr := hBudReg cr (by rw [hSplit]; simp)
  have hselfF : (if regionNeedFrame b cm cr then A.abi.frameSize (regionFrameSlots b cm cr)
      else 0) = A.abi.frameSize (regionFrameSlots b cm cr) := by simp [hNF]
  rw [hselfF] at hSelfLe hBudC_le
  let ns := regionFrameSlots b cm cr
  let selfF := A.abi.frameSize ns
  let hwSp := sp0 - BitVec.ofNat 64 selfF
  let cb := regionStackBudget b cm wit cr_c
  have hcb_le_tot : selfF + (A.abi.raBytes + cb) ≤ budget := Nat.le_trans hBudC_le hBudCr
  have hSelfLeB : selfF ≤ budget := Nat.le_trans hSelfLe hBudCr
  let isMF := regionMemFree cm (foldCallees cm [] p1) cr_c
  let rem := budget - selfF
  let calleeNeed := A.abi.raBytes + cb
  let sp_c := hwSp - BitVec.ofNat 64 A.abi.raBytes
  let ra_c := vcm.symAddr tgtLbl
  have hSplitMem :=
    call_frame_split_region A (sp0 := sp0) (hwSp := hwSp) hSelfLeB hcb_le_tot hbd rfl
  let remOuter := region (sp0 - BitVec.ofNat 64 budget) (rem - calleeNeed) ⋆
    array64 hwSp slots' ⋆ (vllFramePreds A).Saved sp0 ra0 ns ⋆ R
  let outerG := (if isMF then Eq mPub' else emp) ⋆ remOuter
  have hSelfLeC := (witnessBudgets_split b cm hwck
    (pre := p1) (cr := cr_c) (post := p2 ++ cr :: post)
    (by rw [hSplit, hPreEq]; simp only [List.append_assoc, List.cons_append])).2.1
  have hRunCalleeEntry : ∀ (s1 : MachSt A),
      s1.gpr A.abi.sp = sp_c →
      (vllFramePreds A).raReg s1 ra_c →
      WordRegsRel b nxt' s1 →
      (s1.mem =⋆ (vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
        contMemPred isMF mConc' ⋆ outerG) →
      Ψ_L1 (vcm.symAddr cr_c.name) s1 := by
    intro s1 hsp1 hra1 hr1 hm1
    have hBlk := hEntMem cr_c hcrC
    refine closed_bwp hvwf hcl hBlk ?_
    dsimp only
    rw [hPriv0C]
    simp only [emitPrivFrameInit, beq_self_eq_true, ↓reduceIte, List.append_nil]
    have hContSpec := hNode.2.2.2 p1 cr_c (p2 ++ cr :: post)
      (by rw [hSplit, hPreEq]; simp only [List.append_assoc, List.cons_append]) dualRet
      habiC hEntC
    let needFC := regionNeedFrame b cm cr_c
    let nsC := regionFrameSlots b cm cr_c
    have hbdC : cb + A.abi.raBytes ≤ 2 ^ 64 := by omega
    have hspMerge : ∀ m', (region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆
        contMemPred isMF m' ⋆ outerG) =
        (contMemPred isMF m' ⋆ (if isMF then Eq mPub' else emp) ⋆
          region (sp0 - BitVec.ofNat 64 budget) (rem - calleeNeed) ⋆
          region (sp_c - BitVec.ofNat 64 cb) cb ⋆
          region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆
          array64 hwSp slots' ⋆ (vllFramePreds A).Saved sp0 ra0 ns ⋆ R) := by
      intro m'
      have hsp_cb : region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) =
          (region (sp_c - BitVec.ofNat 64 cb) cb ⋆
            region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes) := by
        have hcan : sp_c - BitVec.ofNat 64 cb + BitVec.ofNat 64 cb =
            hwSp - BitVec.ofNat 64 A.abi.raBytes := BitVec.sub_add_cancel _ _
        rw [region_split hbdC, hcan]
      rw [hsp_cb]
      dsimp only [outerG, remOuter]
      ac_rfl
    have handleRet : ∀ (hwSpC : BitVec 64) (G_c : Mem 64 → Prop),
        (needFC = true → A.abi.frameSize nsC ≤ cb) →
        (needFC = true → hwSpC = sp_c - BitVec.ofNat 64 (A.abi.frameSize nsC)) →
        (needFC = false → hwSpC = sp_c) →
        (∀ m', (if needFC then
            ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
              region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆
              contMemPred isMF m' ⋆ outerG)
          else
            ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              contMemPred isMF m' ⋆ outerG)) =
          (contMemPred isMF m' ⋆ G_c)) →
        ∀ (isAlt : Bool) (s_f : MachSt A) (nxt_r : Regs) (m_r : Mem 64)
          (sl_r : List (BitVec 64)),
          (isAlt = true → dualRet = true) →
          (isMF = true → m_r = mConc') →
          (isMF = true → nxt_r.sp = nxt'.sp) →
          sl_r.length = (if needFC then nsC else 0) →
          WordRegsRel b nxt_r s_f →
          (dualRet = true → ValHolds64 .bool isAlt (s_f.gpr b.altRet)) →
          (needFC = false → (vllFramePreds A).raReg s_f ra_c) →
          s_f.gpr A.abi.sp = hwSpC →
          (array64 hwSpC sl_r ⋆ (contMemPred isMF m_r ⋆ G_c)) s_f.mem →
          Φ (retPc + (if isAlt then 8#64 else 0#64), ⟨nxt_r, m_r⟩) →
          bodyWp A vcm.symAddr (if needFC then [.epilogue nsC] else [])
            (fun s' => termWp A vcm.symAddr .ret Ψ_L1 H_L1 s') Ψ_L1 H_L1 s_f := by
      intro hwSpC G_c hsf' hhw' hhw0' hGeq isAlt s_f nxt_r m_r sl_r haok hm_isMF hsp_isMF hlen_r
        hr_r hAltV hra_r hsp_f hm_f hPhi
      refine contified_epilogue_ret_bwp hawf hwf hsf' hbdC hhw' hhw0' hlen_r hra_r hsp_f
        (G_ret := contMemPred isMF m_r) (G_outer := outerG) ?_ ?_
      · have h1 : (if needFC then
            ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
              region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆
              contMemPred isMF m_r ⋆ outerG)
          else
            ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              contMemPred isMF m_r ⋆ outerG)) =
            (contMemPred isMF m_r ⋆ G_c) := hGeq m_r
        rw [h1]; exact hm_f
      · intro s_ret hkeep_r hsp_ret hm_ret
        have hAltW : b.altRet ≠ A.abi.sp ∧ b.altRet ∉ A.abi.raRegs :=
          ⟨(work_not_sp hwf).1, (work_not_ra hwf).1⟩
        have hr_ret := wordRegsRel_of_keepNonSpRa hwf hr_r hkeep_r
        have hsp_ret' : s_ret.gpr A.abi.sp = hwSp := by
          rw [hsp_ret]
          simpa [sp_c] using BitVec.sub_add_cancel hwSp (BitVec.ofNat 64 A.abi.raBytes)
        have hm_fin_split : ∃ mConc'' mPub'',
            Stage1PrivSlots cr.privFrame.numSlots sp0 slots' mConc'' mPub'' ∧
            mConc'' = m_r ∧
            (array64 hwSp slots' ⋆ (Eq mPub'' ⋆ ((vllFramePreds A).Saved sp0 ra0 ns ⋆
              region (sp0 - BitVec.ofNat 64 budget) rem ⋆ R))) s_ret.mem := by
          by_cases hmfc : isMF = true
          · have hm_eq := hm_isMF hmfc
            refine ⟨mConc', mPub', hpriv, hm_eq.symm, ?_⟩
            have hm_cast : (array64 hwSp slots' ⋆ (Eq mPub' ⋆ ((vllFramePreds A).Saved sp0 ra0 ns ⋆
                region (sp0 - BitVec.ofNat 64 budget) (rem - calleeNeed) ⋆
                region (sp_c - BitVec.ofNat 64 cb) cb ⋆
                region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆ R))) s_ret.mem := by
              rw [hspMerge m_r] at hm_ret
              simp only [contMemPred, hmfc, ↓reduceIte] at hm_ret
              have hm_emp : (emp ⋆ (array64 hwSp slots' ⋆
                  (Eq mPub' ⋆ ((vllFramePreds A).Saved sp0 ra0 ns ⋆
                    region (sp0 - BitVec.ofNat 64 budget) (rem - calleeNeed) ⋆
                    region (sp_c - BitVec.ofNat 64 cb) cb ⋆
                    region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆ R))))
                  s_ret.mem := sep_cast hm_ret (by ac_rfl)
              rw [emp_sep] at hm_emp; exact hm_emp
            dsimp only [rem, calleeNeed, sp_c] at hm_cast
            rw [hSplitMem]
            exact sep_cast hm_cast (by ac_rfl)
          · have hmfcF : isMF = false := Bool.eq_false_iff.mpr hmfc
            have hPrivZero : cr.privFrame.numSlots = 0 := Decidable.byContradiction fun hp => by
              have hMfT : isMF = true := hMfC (Nat.pos_of_ne_zero hp)
              rw [hmfcF] at hMfT; cases hMfT
            have hpriv'' : Stage1PrivSlots cr.privFrame.numSlots sp0 slots' m_r m_r :=
              (stage1PrivSlots_zero_eq hPrivZero).mpr rfl
            refine ⟨m_r, m_r, hpriv'', rfl, ?_⟩
            have hm_cast : (array64 hwSp slots' ⋆ (Eq m_r ⋆ ((vllFramePreds A).Saved sp0 ra0 ns ⋆
                region (sp0 - BitVec.ofNat 64 budget) (rem - calleeNeed) ⋆
                region (sp_c - BitVec.ofNat 64 cb) cb ⋆
                region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆ R))) s_ret.mem := by
              rw [hspMerge m_r] at hm_ret
              simp only [contMemPred, hmfcF, Bool.false_eq_true, ↓reduceIte] at hm_ret
              have hm_emp : (emp ⋆ (array64 hwSp slots' ⋆
                  (Eq m_r ⋆ ((vllFramePreds A).Saved sp0 ra0 ns ⋆
                    region (sp0 - BitVec.ofNat 64 budget) (rem - calleeNeed) ⋆
                    region (sp_c - BitVec.ofNat 64 cb) cb ⋆
                    region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆ R))))
                  s_ret.mem := sep_cast hm_ret (by ac_rfl)
              rw [emp_sep] at hm_emp; exact hm_emp
            dsimp only [rem, calleeNeed, sp_c] at hm_cast
            rw [hSplitMem]
            exact sep_cast hm_cast (by ac_rfl)
        obtain ⟨mConc'', mPub'', hpriv'', hm_rEq, hm_sret⟩ := hm_fin_split
        apply hCont s_ret
        refine ⟨isAlt, nxt_r, mConc'', mPub'', fun hd => Decidable.byContradiction fun hnt => by
            cases isAlt
            · exact hnt rfl
            · exact absurd (haok rfl) (by simp [hd]),
          fun hdu => by
            rw [hkeep_r b.altRet hAltW.1 hAltW.2]; exact hAltV hdu,
          hr_ret, hpriv'', fun hp => (hsp_isMF (hMfC hp)).trans (hSp hp),
          fun h => by simp [hNF] at h, hsp_ret', hm_sret, ?_⟩
        cases isAlt
        · simp only [BitVec.add_zero, Bool.false_eq_true, ↓reduceIte] at hPhi ⊢
          simpa [hm_rEq] using hPhi
        · simp only [↓reduceIte] at hPhi ⊢
          simpa [hm_rEq] using hPhi
    have handleHalt : ∀ (hwSpC : BitVec 64) (G_c : Mem 64 → Prop),
        (needFC = true → A.abi.frameSize nsC ≤ cb) →
        (needFC = true → hwSpC = sp_c - BitVec.ofNat 64 (A.abi.frameSize nsC)) →
        (needFC = false → hwSpC = sp_c) →
        (∀ m', (if needFC then
            ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
              region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ Eq m' ⋆ outerG)
          else
            ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              Eq m' ⋆ outerG)) =
          (Eq m' ⋆ G_c)) →
        isMF = false →
        (∃ pc_h ∈ cr_c.allPcs, ∃ blk_h, cm.lookupAddr pc_h = some blk_h ∧
          noHaltBlock blk_h = false) →
        ∀ (s_fin : MachSt A) (cVal : BitVec 64) (m' : Mem 64) (sl_h : List (BitVec 64)),
          sl_h.length = (if needFC then nsC else 0) →
          s_fin.gpr b.w0 = cVal → s_fin.gpr A.abi.sp = hwSpC →
          (array64 hwSpC sl_h ⋆ (Eq m' ⋆ G_c)) s_fin.mem → H_L0 cVal m' →
          bodyWp A vcm.symAddr (if needFC then [.epilogue nsC] else [])
            (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin := by
      intro hwSpC G_c hsf' hhw' hhw0' hGeq hmfcF hExH s_fin cVal m' sl_h hlen_h hw0_h hsp_h
        hm_h hHL0
      have hm_ep : s_fin.mem =⋆ array64 hwSpC sl_h ⋆
          (if needFC then
            ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
              region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ (Eq m' ⋆ outerG))
          else
            ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              (Eq m' ⋆ outerG))) := by
        have hm0 : (array64 hwSpC sl_h ⋆ (Eq m' ⋆ G_c)) s_fin.mem := hm_h
        have h1 : (Eq m' ⋆ G_c) =
            (if needFC then
              ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
                region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆
                (Eq m' ⋆ outerG))
            else
              ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
                (Eq m' ⋆ outerG))) := by
          rw [← hGeq m']
          cases needFC <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ac_rfl
        rw [← h1]
        exact hm0
      refine contified_epilogue_halt_bwp hawf hwf hsf' hbdC hhw' hhw0' hlen_h hsp_h hw0_h hm_ep ?_
      intro s' _ hm_post
      have hlen_caller : slots'.length = ns := by simpa [hNF] using hlen
      have hm_split_m : (region (hwSp - BitVec.ofNat 64 A.abi.raBytes - BitVec.ofNat 64 cb) cb ⋆
          region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆
          region (sp0 - BitVec.ofNat 64 budget) (budget - selfF - (A.abi.raBytes + cb)) ⋆
          array64 hwSp slots' ⋆ (vllFramePreds A).Saved sp0 ra0 ns ⋆
          (Eq m' ⋆ R)) s'.mem := by
        have hsp_cb : region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) =
            (region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes) := by
          have hcan : sp_c - BitVec.ofNat 64 cb + BitVec.ofNat 64 cb =
              hwSp - BitVec.ofNat 64 A.abi.raBytes := BitVec.sub_add_cancel _ _
          rw [region_split hbdC, hcan]
        rw [hsp_cb] at hm_post
        simp only [outerG, remOuter, hmfcF, Bool.false_eq_true, ↓reduceIte] at hm_post
        dsimp only [rem, calleeNeed, sp_c] at hm_post
        exact sep_cast hm_post (by ac_rfl)
      have hm_caller_rem : ((array64 hwSp slots' ⋆ ((vllFramePreds A).Saved sp0 ra0 ns ⋆
          region (sp0 - BitVec.ofNat 64 budget) (budget - selfF))) ⋆ (Eq m' ⋆ R)) s'.mem := by
        rw [hSplitMem]
        exact sep_cast hm_split_m (by ac_rfl)
      have hm_c1 := sep_mono (array64_saved_rem_to_region A hawf hlen_caller hSelfLeB hbd rfl)
        hm_caller_rem
      have hm_fin : (s'.mem =⋆ Eq m' ⋆
          (region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R)) :=
        sep_cast hm_c1 (by ac_rfl)
      exact hHaltC cr_c hcrC dualRet habiC hExH cVal s' ⟨m', hHL0, hm_fin⟩
    by_cases hnc : needFC = true
    · have hsf' : A.abi.frameSize nsC ≤ cb := by simpa [needFC, hnc] using hSelfLeC
      have hfsBd : A.abi.frameSize nsC ≤ 2 ^ 64 := by omega
      have hspSplit := region_sub_split (a := sp_c) hsf' (by omega)
      have hm_pro : s1.mem =⋆ (vllFramePreds A).RetAddr (s1.gpr A.abi.sp) ra_c ⋆
          region (s1.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize nsC))
            (A.abi.frameSize nsC) ⋆
          (region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆
            contMemPred isMF mConc' ⋆ outerG) := by
        rw [hspSplit] at hm1
        simpa only [hsp1] using sep_cast hm1 (by ac_rfl)
      let hwSpC := sp_c - BitVec.ofNat 64 (A.abi.frameSize nsC)
      let G_c := (vllFramePreds A).Saved sp_c ra_c nsC ⋆
        region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ outerG
      have hGeq1 : ∀ m', (if needFC then
            ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
              region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆
              contMemPred isMF m' ⋆ outerG)
          else
            ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              contMemPred isMF m' ⋆ outerG)) =
          (contMemPred isMF m' ⋆ G_c) := fun m' => by
        simp only [hnc, ↓reduceIte, G_c]; ac_rfl
      have hGeq2 : ∀ m', (if needFC then
            ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
              region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ Eq m' ⋆ outerG)
          else
            ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              Eq m' ⋆ outerG)) =
          (Eq m' ⋆ G_c) := fun m' => by
        simp only [hnc, ↓reduceIte, G_c]; ac_rfl
      have hnc' : regionNeedFrame b cm cr_c = true := hnc
      simp only [hnc', ↓reduceIte]
      refine instrWp_prologue hawf hra1 hfsBd hm_pro ?_
      intro slotsC hlenC; dsimp only; intro mC hmC
      have hrC : WordRegsRel b nxt'
          (((s1.setGpr A.abi.sp (s1.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize nsC))).setMem
            mC).setFlags (A.prologueFlags nsC s1.flags)) := by
        simpa only [wordRegsRel_setFlags, wordRegsRel_setMem, wordRegsRel_setSp hwf] using hr1
      rw [hsp1] at hmC
      have hmC' : (array64 hwSpC slotsC ⋆ (contMemPred isMF mConc' ⋆ G_c))
          (((s1.setGpr A.abi.sp (s1.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize nsC))).setMem
            mC).setFlags (A.prologueFlags nsC s1.flags)).mem := by
        simp only [MachSt.mem_setFlags, MachSt.mem_setMem]
        exact sep_cast hmC (by dsimp only [hwSpC, G_c, nsC]; ac_rfl)
      dsimp only [bodyWp]
      exact termWp_fall (hContSpec nxt'.sp retPc ra_c hwSpC slotsC G_c _ (fun _ => rfl) hRp
        (by simp [hlenC, hnc']) hrC (fun h => by rw [hnc'] at h; cases h)
        (by simp [hwSpC, hsp1, nsC]) hmC'
        (handleRet hwSpC G_c (fun _ => hsf') (fun _ => rfl) (fun h => by simp [hnc] at h) hGeq1)
        (handleHalt hwSpC G_c (fun _ => hsf') (fun _ => rfl) (fun h => by simp [hnc] at h) hGeq2))
    · have hncF : needFC = false := Bool.eq_false_iff.mpr hnc
      have hncF' : regionNeedFrame b cm cr_c = false := hncF
      simp only [hncF', Bool.false_eq_true, ↓reduceIte]
      dsimp only [bodyWp]
      let G_c := (vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
        outerG
      have hGeq1 : ∀ m', (if needFC then
            ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
              region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆
              contMemPred isMF m' ⋆ outerG)
          else
            ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              contMemPred isMF m' ⋆ outerG)) =
          (contMemPred isMF m' ⋆ G_c) := fun m' => by
        simp only [hncF, Bool.false_eq_true, ↓reduceIte, G_c]; ac_rfl
      have hGeq2 : ∀ m', (if needFC then
            ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
              region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ Eq m' ⋆ outerG)
          else
            ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
              Eq m' ⋆ outerG)) =
          (Eq m' ⋆ G_c) := fun m' => by
        simp only [hncF, Bool.false_eq_true, ↓reduceIte, G_c]; ac_rfl
      exact termWp_fall (hContSpec nxt'.sp retPc ra_c sp_c [] G_c s1 (fun _ => rfl) hRp
        (by simp [hncF']) hr1 (fun _ => hra1) hsp1
        (sep_array64_emp _ (by simpa [G_c] using sep_cast hm1 (by ac_rfl)))
        (handleRet sp_c G_c (fun h => by simp [hncF] at h) (fun h => by simp [hncF] at h)
          (fun _ => rfl) hGeq1)
        (handleHalt sp_c G_c (fun h => by simp [hncF] at h) (fun h => by simp [hncF] at h)
          (fun _ => rfl) hGeq2))
  have hm_reassoc : (region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆
      region (sp_c - BitVec.ofNat 64 cb) cb ⋆ contMemPred isMF mConc' ⋆ outerG) s_call.mem := by
    have hm1 : (region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆
        region (sp_c - BitVec.ofNat 64 cb) cb ⋆ Eq mPub' ⋆ remOuter) s_call.mem := by
      dsimp only [remOuter]
      rw [hSplitMem] at hm
      exact sep_cast hm (by dsimp only [hwSp, sp_c, rem, calleeNeed, selfF, ns]; ac_rfl)
    by_cases hmfc : isMF = true
    · have hm2 : (emp ⋆ (region (hwSp - BitVec.ofNat 64 A.abi.raBytes) A.abi.raBytes ⋆
          region (sp_c - BitVec.ofNat 64 cb) cb ⋆ Eq mPub' ⋆ remOuter)) s_call.mem :=
        (congrFun (emp_sep _) _).mpr hm1
      simp only [contMemPred, hmfc, ↓reduceIte, outerG]
      exact sep_cast hm2 (by ac_rfl)
    · have hmfcF : isMF = false := Bool.eq_false_iff.mpr hmfc
      have hPrivZero : cr.privFrame.numSlots = 0 := Decidable.byContradiction fun hp => by
        have hMfT : isMF = true := hMfC (Nat.pos_of_ne_zero hp)
        rw [hmfcF] at hMfT; cases hMfT
      have hmConcPub : mConc' = mPub' := (stage1PrivSlots_zero_eq hPrivZero).mp hpriv
      simp only [contMemPred, hmfcF, Bool.false_eq_true, ↓reduceIte, outerG, hmConcPub]
      exact sep_cast hm1 (by ac_rfl)
  cases hkind : A.abi.raKind with
  | linkReg lr =>
    refine termWp_call_linkReg hkind ?_
    let s1 := s_call.setGpr lr ra_c
    have hsp_ne_lr : A.abi.sp ≠ lr := by
      simpa [Abi.raRegs, hkind, RaKind.raRegs] using hawf.sp_disj.2.2.2.2.2
    have hraBytes0 : A.abi.raBytes = 0 := by simp [Abi.raBytes, hkind, RaKind.raBytes]
    have hspc_eq : sp_c = hwSp := by simp [sp_c, hraBytes0]
    have hsp1 : s1.gpr A.abi.sp = sp_c := by
      rw [hspc_eq]; exact (MachSt.gpr_setGpr_ne _ _ hsp_ne_lr).trans hsp
    have hra1 : (vllFramePreds A).raReg s1 ra_c := by simp [vllFramePreds, hkind, s1]
    have hr1 : WordRegsRel b nxt' s1 := wordRegsRel_of_keepNonSpRa hwf hr fun q _ hq =>
      MachSt.gpr_setGpr_ne _ _ fun e => hq (e ▸ by simp [Abi.raRegs, hkind, RaKind.raRegs])
    have hm1 : (s1.mem =⋆ (vllFramePreds A).RetAddr sp_c ra_c ⋆
        region (sp_c - BitVec.ofNat 64 cb) cb ⋆ contMemPred isMF mConc' ⋆ outerG) := by
      simp only [s1, MachSt.mem_setGpr, vllFramePreds, hkind, region_zero, emp_sep]
      have hm2 : (region (sp_c - BitVec.ofNat 64 cb) cb ⋆ contMemPred isMF mConc' ⋆ outerG)
          s_call.mem := by
        simpa only [hraBytes0, region_zero, emp_sep] using hm_reassoc
      exact hm2
    exact hRunCalleeEntry s1 hsp1 hra1 hr1 hm1
  | stack =>
    have hraBytes8 : A.abi.raBytes = 8 := by simp [Abi.raBytes, hkind, RaKind.raBytes]
    have hspc_eq : sp_c = s_call.gpr A.abi.sp - 8#64 := by
      simp [sp_c, hsp, hraBytes8]; rfl
    have hm_cell : (region (s_call.gpr A.abi.sp - 8#64) 8 ⋆
        (region (sp_c - BitVec.ofNat 64 cb) cb ⋆ contMemPred isMF mConc' ⋆ outerG))
        s_call.mem := by
      rw [hsp]
      exact sep_cast hm_reassoc (by dsimp only [hwSp, selfF, ns]; rw [hraBytes8]; ac_rfl)
    obtain ⟨v0, hv0⟩ := region_sep_cell64 hm_cell
    obtain ⟨hst, hmem_st⟩ := store_cell64 ra_c hv0
    refine termWp_call_stack hkind hst ?_
    let s1 := (s_call.setGpr A.abi.sp (s_call.gpr A.abi.sp - 8#64)).setMem
      (storeMem s_call.mem i64 (s_call.gpr A.abi.sp - 8#64) ra_c)
    have hsp1 : s1.gpr A.abi.sp = sp_c := by simp [s1, hspc_eq]
    have hra1 : (vllFramePreds A).raReg s1 ra_c := by simp [vllFramePreds, hkind]
    have hr1 : WordRegsRel b nxt' s1 :=
      (wordRegsRel_setMem _ _ _ _).mpr ((wordRegsRel_setSp hwf _ _ _).mpr hr)
    have hm1 : (s1.mem =⋆ (vllFramePreds A).RetAddr sp_c ra_c ⋆
        region (sp_c - BitVec.ofNat 64 cb) cb ⋆ contMemPred isMF mConc' ⋆ outerG) := by
      have hcellEq : cell64 (s_call.gpr A.abi.sp - 8#64) ra_c = cell64 sp_c ra_c := by
        rw [hspc_eq]
      rw [hcellEq] at hmem_st
      simp only [s1, MachSt.mem_setMem, vllFramePreds, hkind]
      exact sep_cast hmem_st (by ac_rfl)
    exact hRunCalleeEntry s1 hsp1 hra1 hr1 hm1

/-! ## §3. `retEnv_entry_bwp`, `contify_block_step`, and `contify_specsClosed` -/

private theorem retEnv_entry_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    {budget : Nat} (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    {cr : ContifyRegion} (hcr : cr ∈ wit.regions) (habi : cr.abi = .retEnvelope)
    {st : BedrockWord.State} {s : MachSt A}
    (hPriv : cr.privFrame.numSlots > 0 → st.regs.sp = sp0 ∧ cr.privFrame.numSlots ≤ 64 ∧
      ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k))
    (hAnch : WordPlainAnchorRel b st sp0 ra0 budget R s)
    (hInt : RetEnvIntConj A b cm wit vcm sp0 ra0 budget R Ψ_L1 cr.entryPc st) :
    Ψ_L1 cr.entryPc s := by
  obtain ⟨_, hwck, hvwf, _, hRegEnts, _, _, _⟩ := fromWordContify_wf hfc
  obtain ⟨pre, post, hSplit⟩ := List.mem_iff_append.mp hcr
  have hchk := witness_checkAux_split hwck hSplit
  have hEntPc := checkContRegion_entryPc_mem hchk
  have hBlk := fromWordContify_entry_block_mem hfc hcr
  obtain ⟨blk0, hlu0⟩ := by
    have hs := hchk; dsimp only [ContifyRegion.check] at hs
    simp only [Bool.and_eq_true] at hs
    exact Option.isSome_iff_exists.mp hs.1.1.1.1.1.2
  have hBounds := regionFrame_bounds (b := b) hchk hEntPc hlu0
  rw [← (hRegEnts cr hcr).1]
  refine closed_bwp hvwf hcl hBlk ?_
  dsimp only
  let nPriv := cr.privFrame.numSlots
  let needF := regionNeedFrame b cm cr
  let ns := regionFrameSlots b cm cr
  have hIntEnt := hInt cr hcr habi hEntPc
  by_cases hnf : needF = true
  · have hnf' : regionNeedFrame b cm cr = true := hnf
    simp only [hnf', ↓reduceIte] at hIntEnt ⊢
    have hBudPos : budget > 0 := Nat.lt_of_lt_of_le
      (regionNeedFrame_pos_budget hawf b cm hwck hcr hnf) (hBudReg cr hcr)
    obtain ⟨_, hbd, hspEq, hra0, hm⟩ := hAnch.2.2 hBudPos
    obtain ⟨_, hSelfLe, _⟩ := witnessBudgets_split b cm hwck hSplit
    have hSelfLe' : A.abi.frameSize ns ≤ budget := by
      change (if needF then A.abi.frameSize ns else 0) ≤ regionStackBudget b cm wit cr at hSelfLe
      simp only [hnf, ↓reduceIte] at hSelfLe
      exact Nat.le_trans hSelfLe (hBudReg cr hcr)
    have hfsBd : A.abi.frameSize ns ≤ 2 ^ 64 := by omega
    have hm_pro : s.mem =⋆ (vllFramePreds A).RetAddr (s.gpr A.abi.sp) ra0 ⋆
        region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns)) (A.abi.frameSize ns) ⋆
        (region (sp0 - BitVec.ofNat 64 budget) (budget - A.abi.frameSize ns) ⋆
          Eq st.mem ⋆ R) := by
      rw [hwStackMem_split hSelfLe' hbd] at hm
      simpa only [hspEq] using sep_cast hm (by ac_rfl)
    refine instrWp_prologue hawf hra0 hfsBd hm_pro ?_
    intro slots hlen; dsimp only; intro m' hm'
    rw [hspEq] at hm'
    let s_pro :=
      ((s.setGpr A.abi.sp (sp0 - BitVec.ofNat 64 (A.abi.frameSize ns))).setMem m').setFlags
        (A.prologueFlags ns s.flags)
    have hsp' : s_pro.gpr A.abi.sp = sp0 - BitVec.ofNat 64 (A.abi.frameSize ns) := by simp [s_pro]
    have hr' : WordRegsRel b st.regs s_pro := by
      simpa only [s_pro, wordRegsRel_setFlags, wordRegsRel_setMem,
        wordRegsRel_setSp hwf] using hAnch.1
    have hprivLen : nPriv > 0 → nPriv + 1 ≤ slots.length := fun hp => by
      have : nPriv + 1 ≤ ns := by
        dsimp only [ns, regionFrameSlots, regionSpillBase]
        split <;> omega
      omega
    have hm_init : (array64 (sp0 - BitVec.ofNat 64 (A.abi.frameSize (regionFrameSlots b cm cr)))
        slots ⋆ (Eq st.mem ⋆ ((vllFramePreds A).Saved sp0 ra0 (regionFrameSlots b cm cr) ⋆
          region (sp0 - BitVec.ofNat 64 budget)
            (budget - A.abi.frameSize (regionFrameSlots b cm cr)) ⋆ R))) s_pro.mem := by
      simpa only [s_pro, MachSt.mem_setFlags, MachSt.mem_setMem] using sep_cast hm' (by ac_rfl)
    have hs_pro_eq :
        (((s.setGpr A.abi.sp (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize ns))).setMem
            m').setFlags (A.prologueFlags ns s.flags)) = s_pro := by
      simp [s_pro, hspEq]
    by_cases hn0 : cr.privFrame.numSlots = 0
    · simp only [hn0, emitPrivFrameInit, beq_self_eq_true, ↓reduceIte]
      rw [hs_pro_eq]
      exact termWp_fall (hIntEnt sp0 ra0 st.mem slots _ (fun _ => ⟨rfl, rfl⟩) hlen hr'
        (fun hp => absurd hn0 (Nat.ne_of_gt hp)) (fun h => by cases h)
        hsp' ((stage1PrivSlots_zero_eq hn0).mpr rfl) hm_init)
    · have hnPos : cr.privFrame.numSlots > 0 := Nat.pos_of_ne_zero hn0
      obtain ⟨hsp0, hpriv64, hprivOk⟩ := hPriv hnPos
      rw [hs_pro_eq]
      refine emitPrivFrameInit_stage1_bodyWp hawf hwf hsp0 hr'
        (fun _ => ⟨hpriv64, by simpa [hsp0] using hprivOk⟩) hprivLen
        (by rw [hsp']; exact hm_init) ?_
      intro s' slots' hlen' hprivRel' hr'' hsp'' _ _ hm''
      exact termWp_fall (hIntEnt sp0 ra0 st.mem slots' s' (fun _ => ⟨rfl, rfl⟩)
        (hlen'.trans hlen) hr'' (fun _ => hsp0) (fun h => by cases h) (hsp''.trans hsp')
        hprivRel' (by simpa only [hsp'', hsp', ns] using hm''))
  · have hnfF : regionNeedFrame b cm cr = false := Bool.eq_false_iff.mpr hnf
    obtain ⟨hnPriv0, hns0⟩ := hBounds.2.2.2.2.2.2.2 hnfF
    simp only [hnfF, Bool.false_eq_true, ↓reduceIte, hnPriv0, emitPrivFrameInit,
      beq_self_eq_true, List.append_nil, bodyWp] at hIntEnt ⊢
    let sp_in := if budget > 0 then sp0 else s.gpr A.abi.sp
    let ra_in := if budget > 0 then ra0 else freshRaFor A s ra0
    refine termWp_fall (hIntEnt sp_in ra_in st.mem [] s (fun hOr => by
        rcases hOr with hF | hPos
        · cases hF
        · simp [sp_in, ra_in, hPos]) rfl hAnch.1 (fun hp => absurd rfl (Nat.ne_of_gt hp))
      (fun _ => by
        by_cases hb : budget > 0
        · simp only [ra_in, hb, ↓reduceIte]; exact (hAnch.2.2 hb).2.2.2.1
        · simp only [ra_in, hb, ↓reduceIte]; exact raReg_freshRaFor A s ra0)
      (by
        by_cases hb : budget > 0
        · simp only [sp_in, hb, ↓reduceIte]; exact (hAnch.2.2 hb).2.2.1
        · simp only [sp_in, hb, ↓reduceIte])
      (by rw [← hnPriv0]; exact (stage1PrivSlots_zero_eq hnPriv0).mpr rfl)
      (sep_array64_emp _ ?_))
    by_cases hb : budget > 0
    · have hnz : budget ≠ 0 := Nat.ne_of_gt hb
      rw [ite_eq_right hnz]
      exact sep_cast (hAnch.2.2 hb).2.2.2.2 (by ac_rfl)
    · have hz : budget = 0 := Nat.eq_zero_of_not_pos hb
      rw [ite_eq_left hz]
      exact hAnch.2.1 hz

private theorem contify_block_step {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    (hbd : budget + A.abi.raBytes ≤ 2 ^ 64)
    (hspE_b : budget > 0 → A.abi.spEntry sp0)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hHalt : ∀ c s, wordHaltPost A H_L0 (if budget = 0 then R
      else region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R) c s → H_L1 c s)
    (Φ : ContifySpecPred A)
    (hToNode : ∀ pc st, Φ (pc, st) → ContifyNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R Φ
      (pc, st))
    (hPhiJump : ∀ tgt st' s',
      ((∃ e ∈ residualContifyCodeMap cm wit, True) ∨
       (∃ cr ∈ wit.regions, cr.abi = .retEnvelope ∧
         ((cr.privFrame.dynAliasGuard = true ∧ cr.privFrame.numSlots > 0) ∨
          ∃ ew ∈ cr.edges,
            match ew.kind with
            | .bailout | .guarded _ | .strideTable _ _ true => True
            | _ => False))) →
      Φ (tgt, st') → WordPlainAnchorRel b st' sp0 ra0 budget R s' → Ψ_L1 tgt s')
    {pc : BitVec 64} {blk : BlockFlat} (hlu : cm.lookupAddr pc = some blk)
    {st : BedrockWord.State}
    (hbp : blk.wp cm.symEnv (fun q st' => Φ (q, st')) H_L0 (pushRegsV st.regs.toRegsV) st.mem) :
    ContifyNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R Φ (pc, st) := by
  obtain ⟨hcmwf, hwck, hvwf, _, hRegEnts, hInnerBlks, _, hCmAddr_raw⟩ := fromWordContify_wf hfc
  have hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a :=
    fun sym a ha => hCmAddr_raw sym a hSymAgree ha
  have hEntMem : ∀ cr_c ∈ wit.regions,
      ({ label := cr_c.name, pad? := some b.padKind,
         body := (if regionNeedFrame b cm cr_c then [.prologue (regionFrameSlots b cm cr_c)]
                  else []) ++ emitPrivFrameInit b cr_c.privFrame.numSlots,
         term := .fall (innerLabel cr_c cr_c.entryPc) } : Block A) ∈ vcm.blocks :=
    fun cr_c hcr_c => fromWordContify_entry_block_mem hfc hcr_c
  have hHaltPlain : ∀ c s, plainHaltPost A H_L0 sp0 ra0 budget R c s → H_L1 c s := by
    intro c s hp
    dsimp only [plainHaltPost] at hp
    by_cases hz : budget = 0
    · rw [ite_eq_left hz] at hp
      exact hHalt c s (by simpa [hz] using hp)
    · rw [ite_eq_right hz] at hp
      rcases hp with ⟨m', hHL0, hm'⟩
      refine hHalt c s ?_
      rw [ite_eq_right hz]
      have hm1 : (Eq m' ⋆
          (region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R)) s.mem :=
        sep_mono_r (fun _ h => sep_mono (hwStackMem_to_region A hbd) h) hm'
      exact ⟨m', hHL0, sep_cast hm1 (by ac_rfl)⟩
  have hRetInt : RetEnvIntConj A b cm wit vcm sp0 ra0 budget R Ψ_L1 pc st := by
    intro cr hcr habi hpc
    obtain ⟨pre, post, hSplit⟩ := List.mem_iff_append.mp hcr
    have hchk := witness_checkAux_split hwck hSplit
    obtain ⟨pcsInner, hpcsSub, hLeavesChk⟩ := checkContRegion_allPcs_leaf hchk hpc
    obtain ⟨ceBlk, _, _, bs, hluC, hlo, hsub⟩ := fromWordContify_contBlock_sub hfc hcr hpc
    have hceEq : ceBlk = blk := by rw [hluC] at hlu; cases hlu; rfl
    rw [hceEq] at hlo
    rw [hceEq] at hluC
    have hLeavesFacts := checkContBlockLeaves_facts hluC hLeavesChk
    have hBounds := regionFrame_bounds (b := b) hchk hpc hluC
    obtain ⟨_, hMaxBd, hPriv64, hPrivEnv, hNeedCall, hsb_le, hspills, _⟩ := hBounds
    obtain ⟨_, hSelfLe, _⟩ := witnessBudgets_split b cm hwck hSplit
    intro nPriv needF ns selfF sp_in ra_in mPub slots s hSpin hwSp G hlen hr hsp0 hra hs_sp
      hpriv hm
    let Ψ_L0 : BedrockWord.CodeSpec := fun q st' => Φ (q, st')
    let ra₀ : BitVec 64 := if needF then ra0 else ra_in
    refine lowerContBlock_bwp hawf hwf hvwf pc
      (rp0 := 0#64) (hwSp := hwSp) (ra₀ := ra₀) (G := G)
      hcl hcmAddr hPriv64 hPrivEnv
      hNeedCall hsb_le hspills ?hIn ?hIj ?hHa ?hRt ?hCa blk (innerLabel cr pc) [] st.regs
      st.mem mPub s hMaxBd hsp0 (fun hc => by simp [habi, RegionAbi.isContified] at hc)
      hLeavesFacts.2.1 hLeavesFacts.2.2 hlo hsub hbp ?hAcc
    case hIn =>
      intro p nxtR mC mP sl s_t hp hl hr' hns _ hra' hsp' hpr hm' hPhi
      have hpAll := checkContRegion_pcs_mem hchk hpcsSub hp
      have hNodeP := hToNode p ⟨nxtR, mC⟩ hPhi
      refine hNodeP.2.2.1 cr hcr habi hpAll sp_in ra_in mP sl s_t hSpin hl hr' hns
        (fun h => by
          have h1 := hra' h
          have h' : needF = false := h
          simp only [ra₀, h'] at h1
          exact h1)
        hsp' hpr hm'
    case hIj =>
      intro ⟨_, hew⟩ s_fin tgtVal nxt' m' slots' hlen' hw0 hr' hra' hsp' hm' hPhi
      by_cases hnf : needF = true
      · have hnf_ : regionNeedFrame b cm cr = true := hnf
        have hBudPos : budget > 0 := Nat.lt_of_lt_of_le
          (regionNeedFrame_pos_budget hawf b cm hwck hcr hnf_) (hBudReg cr hcr)
        have hSelfLe' : A.abi.frameSize ns ≤ budget :=
          Nat.le_trans (by simpa [needF, hnf] using hSelfLe) (hBudReg cr hcr)
        have hbd_ep : A.abi.frameSize ns + A.abi.raBytes ≤ 2 ^ 64 := by omega
        have hcan : hwSp + BitVec.ofNat 64 (A.abi.frameSize ns) = sp0 := by
          simp only [hwSp, selfF, hnf]; exact BitVec.sub_add_cancel _ _
        simp only [hnf_, ↓reduceIte] at hlen' hm' ⊢
        have hm_ep : s_fin.mem =⋆ array64 (s_fin.gpr A.abi.sp) slots' ⋆
            (vllFramePreds A).Saved
              (s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)) ra0 ns ⋆
            (region (sp0 - BitVec.ofNat 64 budget) (budget - A.abi.frameSize ns) ⋆
              Eq m' ⋆ R) := by
          simp only [hsp', hcan, G, selfF, hnf, ↓reduceIte] at hm' ⊢
          exact sep_cast hm' (by ac_rfl)
        refine instrWp_epilogue hawf hlen' hbd_ep hm_ep ?_
        intro s' hspFin hraFin hkeep _ hmPost
        have hr'' := wordRegsRel_of_keepNonSpRa hwf hr' hkeep
        have hw0_s' : s'.gpr b.w0 = tgtVal :=
          (hkeep b.w0 (work_not_sp hwf).2.1 (work_not_ra hwf).2.1).trans hw0
        have hspFin' : s'.gpr A.abi.sp = sp0 := by
          rw [hspFin, hsp']; exact hcan
        have hmFin' : s'.mem =⋆ Eq m' ⋆ hwStackMem A sp0 ra0 budget ⋆ R := by
          rw [hspFin'] at hmPost
          rw [hwStackMem_split hSelfLe' hbd]
          exact sep_cast hmPost (by ac_rfl)
        have hAnch' : WordPlainAnchorRel b ⟨nxt', m'⟩ sp0 ra0 budget R s' :=
          ⟨hr'', fun hz => absurd hz (Nat.ne_of_gt hBudPos),
            fun _ => ⟨hspE_b hBudPos, hbd, hspFin', hraFin, hmFin'⟩⟩
        dsimp only [bodyWp]
        simpa only [hw0_s'] using hPhiJump tgtVal ⟨nxt', m'⟩ s'
          (Or.inr ⟨cr, hcr, habi, hew⟩) hPhi hAnch'
      · have hnfF : needF = false := Bool.eq_false_iff.mpr hnf
        have hnfF_ : regionNeedFrame b cm cr = false := hnfF
        simp only [hnfF_, Bool.false_eq_true, ↓reduceIte] at hlen' hra' ⊢
        dsimp only [bodyWp]
        have hslNil : slots' = [] := List.eq_nil_of_length_eq_zero hlen'
        subst hslNil
        rw [array64_nil, emp_sep] at hm'
        have hAnch' : WordPlainAnchorRel b ⟨nxt', m'⟩ sp0 ra0 budget R s_fin := by
          refine ⟨hr', fun hz => ?_, fun hpos => ?_⟩
          · have hgz : G = R := by simp [G, hnfF, hz]
            rw [hgz] at hm'; exact hm'
          · have hnz : budget ≠ 0 := Nat.ne_of_gt hpos
            obtain ⟨hsp_in, hra_in⟩ := hSpin (Or.inr hpos)
            have hra'' : (vllFramePreds A).raReg s_fin ra0 := by
              have h1 := hra' trivial
              simp only [ra₀, hnfF, Bool.false_eq_true, ↓reduceIte, hra_in] at h1
              exact h1
            have hsp'' : s_fin.gpr A.abi.sp = sp0 := by
              simpa only [hwSp, hnfF, Bool.false_eq_true, ↓reduceIte, hsp_in] using hsp'
            have hgz : G = (hwStackMem A sp0 ra0 budget ⋆ R) := by
              simp [G, hnfF, hnz]
            rw [hgz] at hm'
            exact ⟨hspE_b hpos, hbd, hsp'', hra'', sep_cast hm' (by ac_rfl)⟩
        simpa only [hw0] using hPhiJump tgtVal ⟨nxt', m'⟩ s_fin
          (Or.inr ⟨cr, hcr, habi, hew⟩) hPhi hAnch'
    case hHa =>
      intro s_fin cVal m' slots' hlen' hw0 hsp' hm' hHL0
      by_cases hnf : needF = true
      · have hnf_ : regionNeedFrame b cm cr = true := hnf
        have hBudPos : budget > 0 := Nat.lt_of_lt_of_le
          (regionNeedFrame_pos_budget hawf b cm hwck hcr hnf_) (hBudReg cr hcr)
        have hSelfLe' : A.abi.frameSize ns ≤ budget :=
          Nat.le_trans (by simpa [needF, hnf] using hSelfLe) (hBudReg cr hcr)
        have hbd_ep : A.abi.frameSize ns + A.abi.raBytes ≤ 2 ^ 64 := by omega
        have hcan : hwSp + BitVec.ofNat 64 (A.abi.frameSize ns) = sp0 := by
          simp only [hwSp, selfF, hnf]; exact BitVec.sub_add_cancel _ _
        simp only [hnf_, ↓reduceIte] at hlen' hm' ⊢
        have hm_ep : s_fin.mem =⋆ array64 (s_fin.gpr A.abi.sp) slots' ⋆
            (vllFramePreds A).Saved
              (s_fin.gpr A.abi.sp + BitVec.ofNat 64 (A.abi.frameSize ns)) ra0 ns ⋆
            (region (sp0 - BitVec.ofNat 64 budget) (budget - A.abi.frameSize ns) ⋆
              Eq m' ⋆ R) := by
          simp only [hsp', hcan, G, selfF, hnf, ↓reduceIte] at hm' ⊢
          exact sep_cast hm' (by ac_rfl)
        refine instrWp_epilogue hawf hlen' hbd_ep hm_ep ?_
        intro s' hspFin _ hkeep _ hmPost
        have hw0_s' : s'.gpr b.w0 = cVal :=
          (hkeep b.w0 (work_not_sp hwf).2.1 (work_not_ra hwf).2.1).trans hw0
        have hspFin' : s'.gpr A.abi.sp = sp0 := by
          rw [hspFin, hsp']; exact hcan
        have hmFin' : s'.mem =⋆ Eq m' ⋆ hwStackMem A sp0 ra0 budget ⋆ R := by
          rw [hspFin'] at hmPost
          rw [hwStackMem_split hSelfLe' hbd]
          exact sep_cast hmPost (by ac_rfl)
        have hmReg : s'.mem =⋆ Eq m' ⋆
            (region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R) := by
          have hm1 : (hwStackMem A sp0 ra0 budget ⋆ (Eq m' ⋆ R)) s'.mem :=
            sep_cast hmFin' (by ac_rfl)
          have hm2 := sep_mono (hwStackMem_to_region A hbd) hm1
          exact sep_cast hm2 (by ac_rfl)
        have hnz : budget ≠ 0 := Nat.ne_of_gt hBudPos
        dsimp only [bodyWp]
        refine hHalt (s'.gpr b.w0) s' ?_
        rw [ite_eq_right hnz]
        exact ⟨m', by simpa only [hw0_s'] using hHL0, hmReg⟩
      · have hnfF : needF = false := Bool.eq_false_iff.mpr hnf
        have hnfF_ : regionNeedFrame b cm cr = false := hnfF
        simp only [hnfF_, Bool.false_eq_true, ↓reduceIte] at hlen' ⊢
        dsimp only [bodyWp]
        have hslNil : slots' = [] := List.eq_nil_of_length_eq_zero hlen'
        subst hslNil
        rw [array64_nil, emp_sep] at hm'
        refine hHalt (s_fin.gpr b.w0) s_fin ?_
        by_cases hz : budget = 0
        · rw [ite_eq_left hz]
          have hgz : G = R := by simp [G, hnfF, hz]
          rw [hgz] at hm'
          exact ⟨m', by simpa only [hw0] using hHL0, hm'⟩
        · rw [ite_eq_right hz]
          have hgz : G = (hwStackMem A sp0 ra0 budget ⋆ R) := by
            simp [G, hnfF, hz]
          rw [hgz] at hm'
          have hm2 : (hwStackMem A sp0 ra0 budget ⋆ (Eq m' ⋆ R)) s_fin.mem :=
            sep_cast hm' (by ac_rfl)
          have hm3 := sep_mono (hwStackMem_to_region A hbd) hm2
          have hm4 : (Eq m' ⋆
              (region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R)) s_fin.mem :=
            sep_cast hm3 (by ac_rfl)
          exact ⟨m', by simpa only [hw0] using hHL0, hm4⟩
    case hRt =>
      intro _ _ _ _ _ _ _ hRetAbi
      rw [habi] at hRetAbi; cases hRetAbi
    case hCa =>
      intro callee calleePc dualRet retPc altRetPc? tgtLbl nxt' slots' mConc' mPub' s_call _
        hNF hEw hCal hMf _ hRp _ _ _ hSp hlen' hpriv' hr' hsp' hm' hPhi hCont
      have hnf_ : needF = true := hNF
      have hBudPos : budget > 0 := Nat.lt_of_lt_of_le
        (regionNeedFrame_pos_budget hawf b cm hwck hcr hNF) (hBudReg cr hcr)
      have hnz : budget ≠ 0 := Nat.ne_of_gt hBudPos
      have hSelfEq : selfF = A.abi.frameSize ns := by simp [selfF, hnf_]
      have hHwEq : hwSp = sp0 - BitVec.ofNat 64 (A.abi.frameSize ns) := by
        simp [hwSp, hnf_, hSelfEq]
      have hGEq : G = ((vllFramePreds A).Saved sp0 ra0 ns ⋆
          region (sp0 - BitVec.ofNat 64 budget) (budget - A.abi.frameSize ns) ⋆ R) := by
        simp [G, hnf_, hSelfEq]
      have hra0Eq : ra₀ = ra0 := by simp [ra₀, hnf_]
      rw [hHwEq, hGEq] at hm' hCont
      rw [hHwEq] at hsp'
      rw [hra0Eq] at hCont
      have hHaltC : ∀ cr_c ∈ wit.regions, ∀ dualRet, cr_c.abi = .contified dualRet →
          (∃ pc ∈ cr_c.allPcs, ∃ blk, cm.lookupAddr pc = some blk ∧
            noHaltBlock blk = false) →
          ∀ c s, wordHaltPost A H_L0
            (region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R) c s → H_L1 c s :=
        fun _ _ _ _ _ c s hw => hHalt c s (by rw [ite_eq_right hnz]; exact hw)
      exact contify_contCall_discharge hawf hwf hvwf hwck hBudReg hcl hEntMem hbd hHaltC hSplit Φ
        hNF hEw hCal hMf hRp hSp hlen' hpriv' hr' hsp' hm' (hToNode calleePc ⟨nxt', mConc'⟩ hPhi)
        hCont
    case hAcc =>
      dsimp only [bodyWp]
      exact ⟨slots, hlen, envRel_pushRegsV _ hr, hr, hpriv,
        fun h => by
          have h' : needF = false := h
          simp only [ra₀, h']
          exact hra h,
        hs_sp, hm⟩
  refine ⟨?_, ?_, hRetInt, ?_⟩
  · intro e he rfl s hAnch
    obtain ⟨sA, sB, bs, hlo, hsub⟩ := fromWordContify_plainEntry_sub hfc he
    have heCm : e ∈ cm := by
      dsimp only [residualContifyCodeMap] at he; exact (List.mem_filter.mp he).1
    have hBlkEq := codeMap_entry_eq_of_lookup hcmwf.addrsNodup heCm hlu
    rw [← (fromWordContify_wf hfc).2.2.2.2.2.2.1 e he |>.1]
    exact lowerPlainEntry_bwp hawf hwf hvwf hcl hcmAddr hHaltPlain
      (fun tgt st' s' hPhi hAnch' => hPhiJump tgt st' s' (Or.inl ⟨e, he, trivial⟩) hPhi hAnch')
      (hBudRes e he) hlo hsub hAnch (hBlkEq ▸ hbp)
  · intro cr hcr habi rfl hPriv s hAnch
    exact retEnv_entry_bwp hawf hwf hfc hBudReg hcl hcr habi hPriv hAnch hRetInt
  · intro pre cr post hSplit dualRet habi hpc needF ns isMF sp0_c rp0 ra_ret hwSp slots G s
      hsp0C hrp hlen hr hra hsp hm hRet hHalt_cr
    have hcr : cr ∈ wit.regions := by rw [hSplit]; simp
    have hchk := witness_checkAux_split hwck hSplit
    obtain ⟨pcsInner, hpcsSub, hLeavesChk⟩ := checkContRegion_allPcs_leaf hchk hpc
    obtain ⟨ceBlk, _, _, bs, hluC, hlo, hsub⟩ := fromWordContify_contBlock_sub hfc hcr hpc
    have hceEq : ceBlk = blk := by rw [hluC] at hlu; cases hlu; rfl
    rw [hceEq] at hlo
    rw [hceEq] at hluC
    have hLeavesFacts := checkContBlockLeaves_facts hluC hLeavesChk
    have hBounds := regionFrame_bounds (b := b) hchk hpc hluC
    obtain ⟨_, hMaxBd, hPriv64, hPrivEnv, hNeedCall, hsb_le, hspills, _⟩ := hBounds
    have hPriv0 : cr.privFrame.numSlots = 0 := Decidable.byContradiction fun hp => by
      have := hPrivEnv (Nat.pos_of_ne_zero hp); rw [habi] at this; cases this
    by_cases hmf : isMF = true
    · have hmf' : regionMemFree cm (foldCallees cm [] pre) cr = true := hmf
      have hnoM := regionMemFree_blockNoMem hmf hpc hlu
      have hnoH := noHaltBlock_of_blockNoMem blk hnoM
      have hbp_nf := noHaltBlock_wp_false (H₂ := fun _ _ => False) blk
        (pushRegsV st.regs.toRegsV) st.mem hnoH hbp
      have hbp_emp := regionMemFree_block_wp hmf hpc hlu (m₂ := ∅) (H₂ := fun _ _ => False) hbp_nf
      refine lowerContBlock_bwp hawf hwf hvwf pc
        (sp0 := sp0_c) (rp0 := rp0) (hwSp := hwSp) (ra₀ := ra_ret) (G := G)
        hcl hcmAddr hPriv64 hPrivEnv
        hNeedCall hsb_le hspills ?_ (fun ⟨hEnv, _⟩ => by rw [habi] at hEnv; cases hEnv)
        (fun _ _ _ _ _ _ _ _ hF => False.elim hF) ?_
        (fun hEnv => by rw [habi] at hEnv; cases hEnv)
        blk (innerLabel cr pc) [] st.regs (∅ : Mem 64) (∅ : Mem 64) s hMaxBd
        (fun hp => absurd hp (by simp [hPriv0])) (fun _ => hrp)
        hLeavesFacts.2.1 hLeavesFacts.2.2 hlo hsub hbp_emp ?_
      · intro p nxtR mC mP sl s_t hp hl hr' _ hnr hra' hsp' hpr hm' ⟨hPhi, hspN, hmC⟩
        dsimp only at hspN hmC
        have hpAll := checkContRegion_pcs_mem hchk hpcsSub hp
        have hNodeP := hToNode p ⟨nxtR, st.mem⟩ hPhi
        have hmCP : mC = mP := (stage1PrivSlots_zero_eq hPriv0).mp hpr
        rw [← hmCP, hmC] at hm'
        exact hNodeP.2.2.2 pre cr post hSplit dualRet habi hpAll sp0_c rp0 ra_ret hwSp sl G s_t
          (fun _ => hspN.trans (hsp0C hmf)) (hnr (by simp [habi, RegionAbi.isContified]))
          hl hr' hra' hsp' (by simpa [contMemPred_eq, hmf'] using hm')
          (fun isAlt s_f nxt' m' sl' ha hm'' hsp' hl' hr'' hdu hra'' hsp'' hm''' hPhi' =>
            hRet isAlt s_f nxt' m' sl' ha (fun h => hm'' h) hsp' hl' hr'' hdu hra'' hsp''
              hm''' hPhi')
          hHalt_cr
      · intro dualRet' isAlt s_fin tgtVal nxt' m' slots' a_abi haok htgtEq hlen' hr' hAlt hra' hsp'
          hm' ⟨hPhi, hspN, hmC⟩
        dsimp only at hspN hmC
        have hduEq : dualRet' = dualRet := by rw [habi] at a_abi; cases a_abi; rfl
        subst hduEq
        rw [htgtEq] at hPhi
        rw [hmC] at hm'
        exact hRet isAlt s_fin nxt' st.mem slots' haok (fun _ => rfl)
          (fun _ => hspN.trans (hsp0C hmf)) hlen' hr' hAlt hra' hsp'
          (by simpa [contMemPred_eq, hmf] using hm') hPhi
      · dsimp only [bodyWp]
        exact ⟨slots, hlen, envRel_pushRegsV _ hr, hr, (stage1PrivSlots_zero_eq hPriv0).mpr rfl,
          hra, hsp, by simpa [contMemPred_eq, hmf] using hm⟩
    · have hmfF : isMF = false := Bool.eq_false_iff.mpr hmf
      have hmfF' : regionMemFree cm (foldCallees cm [] pre) cr = false := hmfF
      by_cases hnh : noHaltBlock blk = true
      · have hbp_nf := noHaltBlock_wp_false (H₂ := fun _ _ => False) blk
          (pushRegsV st.regs.toRegsV) st.mem hnh hbp
        refine lowerContBlock_bwp hawf hwf hvwf pc
          (sp0 := sp0_c) (rp0 := rp0) (hwSp := hwSp) (ra₀ := ra_ret) (G := G)
          hcl hcmAddr hPriv64 hPrivEnv
          hNeedCall hsb_le hspills ?_ (fun ⟨hEnv, _⟩ => by rw [habi] at hEnv; cases hEnv)
          (fun _ _ _ _ _ _ _ _ hF => False.elim hF) ?_
          (fun hEnv => by rw [habi] at hEnv; cases hEnv)
          blk (innerLabel cr pc) [] st.regs st.mem st.mem s hMaxBd
          (fun hp => absurd hp (by simp [hPriv0])) (fun _ => hrp)
          hLeavesFacts.2.1 hLeavesFacts.2.2 hlo hsub hbp_nf ?_
        · intro p nxtR mC mP sl s_t hp hl hr' _ hnr hra' hsp' hpr hm' hPhi
          have hpAll := checkContRegion_pcs_mem hchk hpcsSub hp
          have hNodeP := hToNode p ⟨nxtR, mC⟩ hPhi
          have hmCP : mC = mP := (stage1PrivSlots_zero_eq hPriv0).mp hpr
          rw [← hmCP] at hm'
          exact hNodeP.2.2.2 pre cr post hSplit dualRet habi hpAll sp0_c rp0 ra_ret hwSp sl G s_t
            (fun h => absurd h (by rw [hmfF']; simp)) (hnr (by simp [habi, RegionAbi.isContified]))
            hl hr' hra' hsp' (by simpa [contMemPred_eq, hmfF'] using hm')
            (fun isAlt s_f nxt' m' sl' ha _ hsp' hl' hr'' hdu hra'' hsp'' hm''' hPhi' =>
              hRet isAlt s_f nxt' m' sl' ha (fun h => absurd h hmf) hsp' hl'
                hr'' hdu hra'' hsp'' hm''' hPhi')
            hHalt_cr
        · intro dualRet' isAlt s_fin tgtVal nxt' m' slots' a_abi haok htgtEq hlen' hr' hAlt hra'
            hsp' hm' hPhi
          have hduEq : dualRet' = dualRet := by rw [habi] at a_abi; cases a_abi; rfl
          subst hduEq
          rw [htgtEq] at hPhi
          exact hRet isAlt s_fin nxt' m' slots' haok (fun h => absurd h hmf)
            (fun h => absurd h hmf) hlen' hr' hAlt hra' hsp'
            (by simpa [contMemPred_eq, hmfF] using hm') hPhi
        · dsimp only [bodyWp]
          exact ⟨slots, hlen, envRel_pushRegsV _ hr, hr, (stage1PrivSlots_zero_eq hPriv0).mpr rfl,
            hra, hsp, by simpa [contMemPred_eq, hmfF] using hm⟩
      · have hnhF : noHaltBlock blk = false := Bool.eq_false_iff.mpr hnh
        have hExH : ∃ pc_h ∈ cr.allPcs, ∃ blk_h, cm.lookupAddr pc_h = some blk_h ∧
            noHaltBlock blk_h = false := ⟨pc, hpc, blk, hlu, hnhF⟩
        refine lowerContBlock_bwp hawf hwf hvwf pc
          (sp0 := sp0_c) (rp0 := rp0) (hwSp := hwSp) (ra₀ := ra_ret) (G := G)
          hcl hcmAddr hPriv64 hPrivEnv
          hNeedCall hsb_le hspills ?_ (fun ⟨hEnv, _⟩ => by rw [habi] at hEnv; cases hEnv)
          (hHalt_cr hmfF hExH) ?_ (fun hEnv => by rw [habi] at hEnv; cases hEnv)
          blk (innerLabel cr pc) [] st.regs st.mem st.mem s hMaxBd
          (fun hp => absurd hp (by simp [hPriv0])) (fun _ => hrp)
          hLeavesFacts.2.1 hLeavesFacts.2.2 hlo hsub hbp ?_
        · intro p nxtR mC mP sl s_t hp hl hr' _ hnr hra' hsp' hpr hm' hPhi
          have hpAll := checkContRegion_pcs_mem hchk hpcsSub hp
          have hNodeP := hToNode p ⟨nxtR, mC⟩ hPhi
          have hmCP : mC = mP := (stage1PrivSlots_zero_eq hPriv0).mp hpr
          rw [← hmCP] at hm'
          exact hNodeP.2.2.2 pre cr post hSplit dualRet habi hpAll sp0_c rp0 ra_ret hwSp sl G s_t
            (fun h => absurd h (by rw [hmfF']; simp)) (hnr (by simp [habi, RegionAbi.isContified]))
            hl hr' hra' hsp' (by simpa [contMemPred_eq, hmfF'] using hm')
            (fun isAlt s_f nxt' m' sl' ha _ hsp' hl' hr'' hdu hra'' hsp'' hm''' hPhi' =>
              hRet isAlt s_f nxt' m' sl' ha (fun h => absurd h hmf) hsp' hl'
                hr'' hdu hra'' hsp'' hm''' hPhi')
            hHalt_cr
        · intro dualRet' isAlt s_fin tgtVal nxt' m' slots' a_abi haok htgtEq hlen' hr' hAlt hra'
            hsp' hm' hPhi
          have hduEq : dualRet' = dualRet := by rw [habi] at a_abi; cases a_abi; rfl
          subst hduEq
          rw [htgtEq] at hPhi
          exact hRet isAlt s_fin nxt' m' slots' haok (fun h => absurd h hmf)
            (fun h => absurd h hmf) hlen' hr' hAlt hra' hsp'
            (by simpa [contMemPred_eq, hmfF] using hm') hPhi
        · dsimp only [bodyWp]
          exact ⟨slots, hlen, envRel_pushRegsV _ hr, hr, (stage1PrivSlots_zero_eq hPriv0).mpr rfl,
            hra, hsp, by simpa [contMemPred_eq, hmfF] using hm⟩

private theorem codeMap_lookup_of_mem {cm : CodeMap} (hnd : cm.AddrsNodup)
    {e : CodeEntry} (he : e ∈ cm) : cm.lookupAddr e.addr = some e.block := by
  induction cm with
  | nil => cases he
  | cons x xs ih =>
    have hnd' := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp he with rfl | htail
    · simp [CodeMap.lookupAddr]
    · have hne : x.addr ≠ e.addr := fun h => hnd'.1 (List.mem_map.mpr ⟨e, htail, h.symm⟩)
      simp [CodeMap.lookupAddr, beq_false_of_ne hne, ih hnd'.2 htail]

theorem contify_specsClosed_ext {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    (hbd : budget + A.abi.raBytes ≤ 2 ^ 64)
    (hspE_b : budget > 0 → A.abi.spEntry sp0)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hHalt : ∀ c s, wordHaltPost A H_L0 (if budget = 0 then R
      else region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R) c s → H_L1 c s)
    (ExtSpec Inv : BedrockWord.CodeSpec)
    (hExt : ∀ tgt st s, ExtSpec tgt st →
      WordPlainAnchorRel b st sp0 ra0 budget R s → Ψ_L1 tgt s)
    (hInvCl : SpecsClosed cm cm.symEnv Inv H_L0)
    (hInvValid : ((∃ e ∈ residualContifyCodeMap cm wit, True) ∨
      (∃ cr ∈ wit.regions, cr.abi = .retEnvelope ∧
        ((cr.privFrame.dynAliasGuard = true ∧ cr.privFrame.numSlots > 0) ∨
         ∃ ew ∈ cr.edges, match ew.kind with
           | .bailout | .guarded _ | .strideTable _ _ true => True | _ => False))) →
      ∀ tgt st, Inv tgt st →
        (cm.lookupAddr tgt = none ∧ ExtSpec tgt st) ∨
        (∃ e ∈ residualContifyCodeMap cm wit, e.addr = tgt) ∨
        (∃ cr ∈ wit.regions, cr.abi = .retEnvelope ∧ cr.entryPc = tgt ∧
          (cr.privFrame.numSlots > 0 → st.regs.sp = sp0 ∧ cr.privFrame.numSlots ≤ 64 ∧
            ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k)))) :
    SpecsClosed cm cm.symEnv
      (ContifyFixExt A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv) H_L0 := by
  intro pc blk hlu st hbp
  have hwfC := fromWordContify_wf hfc
  let Φ : ContifySpecPred A := fun p =>
    ContifyFixExt A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv p.1 p.2
  have hLfpInv : ∀ pc' st', Φ (pc', st') → Inv pc' st' := fun pc' st' hPhi =>
    (Xcap.Lfp.lfp_post
      (contifyOpenNode_mono A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv)
      (pc', st') hPhi).2
  have hToNode : ∀ pc' st', Φ (pc', st') →
      ContifyNode A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R Φ (pc', st') := by
    intro pc' st' hPhi
    rcases (Xcap.Lfp.lfp_post
      (contifyOpenNode_mono A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv)
      (pc', st') hPhi).1 with hN | ⟨hNone, _⟩
    · exact hN
    · refine ⟨fun e he heq => ?_, fun cr hcr _ heq => ?_, fun cr hcr _ hpc => ?_,
        fun pre cr post hSplit _ _ hpc => ?_⟩
      · have heCm : e ∈ cm := by
          dsimp only [residualContifyCodeMap] at he; exact (List.mem_filter.mp he).1
        have hluE := codeMap_lookup_of_mem hwfC.1.addrsNodup heCm
        rw [heq, hNone] at hluE; cases hluE
      · obtain ⟨pre, post, hSplit⟩ := List.mem_iff_append.mp hcr
        have hchk := witness_checkAux_split hwfC.2.1 hSplit
        obtain ⟨_, _, _, _, hluC, _, _⟩ :=
          fromWordContify_contBlock_sub hfc hcr (checkContRegion_entryPc_mem hchk)
        rw [heq, hNone] at hluC; cases hluC
      · obtain ⟨_, _, _, _, hluC, _, _⟩ := fromWordContify_contBlock_sub hfc hcr hpc
        rw [hNone] at hluC; cases hluC
      · have hcr : cr ∈ wit.regions := by rw [hSplit]; simp
        obtain ⟨_, _, _, _, hluC, _, _⟩ := fromWordContify_contBlock_sub hfc hcr hpc
        rw [hNone] at hluC; cases hluC
  have hInvPc : Inv pc st :=
    hInvCl pc blk hlu st (blockFlat_wp_mono (fun q st' h => hLfpInv q st' h) blk _ _ hbp)
  refine Xcap.Lfp.lfp_closed
    (contifyOpenNode_mono A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv)
    (pc, st) ⟨Or.inl ?_, hInvPc⟩
  refine contify_block_step hawf hwf hfc hSymAgree hBudReg hBudRes hbd hspE_b hcl hHalt Φ
    hToNode ?_ hlu hbp
  intro tgt st' s' hTrig hLfp hAnch'
  rcases hInvValid hTrig tgt st' (hLfpInv tgt st' hLfp) with
    ⟨_, hExtT⟩ | ⟨e, he, heq⟩ | ⟨cr, hcr, habi, heq, hPriv⟩
  · exact hExt tgt st' s' hExtT hAnch'
  · exact (hToNode tgt st' hLfp).1 e he heq s' hAnch'
  · exact (hToNode tgt st' hLfp).2.1 cr hcr habi heq hPriv s' hAnch'

theorem contify_specsClosed {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    (hbd : budget + A.abi.raBytes ≤ 2 ^ 64)
    (hspE_b : budget > 0 → A.abi.spEntry sp0)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hHalt : ∀ c s, wordHaltPost A H_L0 (if budget = 0 then R
      else region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R) c s → H_L1 c s)
    (hNoOpen : ¬ ((∃ e ∈ residualContifyCodeMap cm wit, True) ∨
      (∃ cr ∈ wit.regions, cr.abi = .retEnvelope ∧
        ((cr.privFrame.dynAliasGuard = true ∧ cr.privFrame.numSlots > 0) ∨
         ∃ ew ∈ cr.edges, match ew.kind with
           | .bailout | .guarded _ | .strideTable _ _ true => True | _ => False)))) :
    SpecsClosed cm cm.symEnv
      (ContifyFix A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R) H_L0 :=
  contify_specsClosed_ext hawf hwf hfc hSymAgree hBudReg hBudRes hbd hspE_b hcl hHalt
    (fun _ _ => False) (fun _ _ => True) (fun _ _ _ h => False.elim h)
    (fun _ _ _ _ _ => trivial) (fun hTrig => absurd hTrig hNoOpen)

theorem contifyFixExt_resEntry {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {wit : ContifyWitness} {vcm : VllCodeMap A} (hfc : fromWordContify b cm wit = .ok vcm)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    {sp0 ra0 : BitVec 64} {budget : Nat} {R : Mem 64 → Prop} {ExtSpec Inv : BedrockWord.CodeSpec}
    {e : CodeEntry} (he : e ∈ residualContifyCodeMap cm wit) {st : BedrockWord.State}
    (h : ContifyFixExt A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv
      e.addr st) :
    ∀ s, WordPlainAnchorRel b st sp0 ra0 budget R s → Ψ_L1 e.addr s := by
  rcases (Xcap.Lfp.lfp_post
    (contifyOpenNode_mono A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv)
    (e.addr, st) h).1 with hN | ⟨hNone, _⟩
  · exact hN.1 e he rfl
  · have heCm : e ∈ cm := by
      dsimp only [residualContifyCodeMap] at he; exact (List.mem_filter.mp he).1
    have hlu := codeMap_lookup_of_mem (fromWordContify_wf hfc).1.addrsNodup heCm
    rw [hNone] at hlu; cases hlu

theorem contifyFixExt_retEnvExt {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {wit : ContifyWitness} {vcm : VllCodeMap A} (hfc : fromWordContify b cm wit = .ok vcm)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    {sp0 ra0 : BitVec 64} {budget : Nat} {R : Mem 64 → Prop} {ExtSpec Inv : BedrockWord.CodeSpec}
    {cr : ContifyRegion} (hcr : cr ∈ wit.regions) (habi : cr.abi = .retEnvelope)
    {st : BedrockWord.State}
    (h : ContifyFixExt A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv
      cr.entryPc st)
    (hPriv : cr.privFrame.numSlots > 0 → st.regs.sp = sp0 ∧ cr.privFrame.numSlots ≤ 64 ∧
      ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k)) :
    ∀ s, WordPlainAnchorRel b st sp0 ra0 budget R s → Ψ_L1 cr.entryPc s := by
  rcases (Xcap.Lfp.lfp_post
    (contifyOpenNode_mono A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv)
    (cr.entryPc, st) h).1 with hN | ⟨hNone, _⟩
  · exact hN.2.1 cr hcr habi rfl hPriv
  · obtain ⟨pre, post, hSplit⟩ := List.mem_iff_append.mp hcr
    have hchk := witness_checkAux_split (fromWordContify_wf hfc).2.1 hSplit
    obtain ⟨_, _, _, _, hluC, _, _⟩ :=
      fromWordContify_contBlock_sub hfc hcr (checkContRegion_entryPc_mem hchk)
    rw [hNone] at hluC; cases hluC

theorem contifyFix_resEntry {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {wit : ContifyWitness} {vcm : VllCodeMap A} (hfc : fromWordContify b cm wit = .ok vcm)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    {sp0 ra0 : BitVec 64} {budget : Nat} {R : Mem 64 → Prop}
    {e : CodeEntry} (he : e ∈ residualContifyCodeMap cm wit) {st : BedrockWord.State}
    (h : ContifyFix A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R e.addr st) :
    ∀ s, WordPlainAnchorRel b st sp0 ra0 budget R s → Ψ_L1 e.addr s :=
  contifyFixExt_resEntry hfc he h

theorem contifyFix_retEnvExt {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {wit : ContifyWitness} {vcm : VllCodeMap A} (hfc : fromWordContify b cm wit = .ok vcm)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    {sp0 ra0 : BitVec 64} {budget : Nat} {R : Mem 64 → Prop}
    {cr : ContifyRegion} (hcr : cr ∈ wit.regions) (habi : cr.abi = .retEnvelope)
    {st : BedrockWord.State}
    (h : ContifyFix A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R cr.entryPc st) :
    (cr.privFrame.numSlots > 0 → st.regs.sp = sp0 ∧ cr.privFrame.numSlots ≤ 64 ∧
      ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k)) →
    ∀ s, WordPlainAnchorRel b st sp0 ra0 budget R s → Ψ_L1 cr.entryPc s :=
  contifyFixExt_retEnvExt hfc hcr habi h

def contRegionMemFree (cm : CodeMap) (pre : List ContifyRegion) (cr : ContifyRegion) : Bool :=
  regionMemFree cm (foldCallees cm [] pre) cr

end LeanQbe.T.Vll
