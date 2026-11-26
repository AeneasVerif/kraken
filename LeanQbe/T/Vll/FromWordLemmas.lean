module

public import LeanQbe.T.Vll.FromWord
public import LeanQbe.T.BedrockWord.Exec
public import LeanQbe.T.Xcap.Bridge
import LeanQbe.T.Vll.FromWordLemmas0
import LeanQbe.T.Vll.FromWordLemmas1
import LeanQbe.T.Vll.FromWordLemmas2
import LeanQbe.T.Vll.FromWordLemmas3
import LeanQbe.T.Vll.FromWordLemmas4
import LeanQbe.T.Unified.CfgContifyLemmas
import LeanQbe.T.BedrockWord.Ops
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.TargetLemmas

/-!
# Soundness & XCAP Composition Theorems for `Vll.FromWord` (`Vll.FromWordLemmas`)

Arch-free public theorem layer connecting `BedrockWord` L0 specifications (`CodeMap.wp`,
`SpecsClosed`, `OpenModOk`) to `BedrockMach` L1 (`VllCodeMap A`, `VllHost A`, `Xcap.Bridge`):

* §1. Open `fromWord` XCAP `cptr` soundness & adequacy (`fromWord_open_cptr_sound`,
      `fromWord_cptr_sound`, `fromWord_wp_sound`, `fromWord_adequacy`).
* §2. Stage-1 `fromWordContify` contification, `PrivFrameCfg`, and dual-return `vllCallPre`
      soundness (`contified_open_cptr_spec`, `contified_cptr_spec`,
      `fromWordContify_open_cptr_sound`, `fromWordContify_cptr_sound`,
      `fromWordContify_wp_sound`, `fromWordContify_adequacy`).
* §3. `VllCodeMap.Hosted` small-step `vllStep` bridge (`vllHosted_closed`,
      `vllHosted_closed_noHalt`, `fromWord_hosted_vllStep`, `fromWordContify_hosted_vllStep`,
      `contified_hosted_vllStep`) and `Xcap.Bridge` (`fnSpec_to_cptr` /
      `cptr_of_targetClosed_to_Γ`) composition.

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

/-! ## Private Stage-0/1 & XCAP Helper Lemmas -/

private theorem raBytes_le_eight (A : Arch) : A.abi.raBytes ≤ 8 := by
  cases hkind : A.abi.raKind <;> simp [Abi.raBytes, hkind, RaKind.raBytes]

private theorem add_8_ne_self (x : BitVec 64) : x + 8#64 ≠ x := by
  intro h
  have h2 := congrArg BitVec.toNat h
  have hx := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h2
  omega

private theorem vllWp_closed {A : Arch} {vcm : VllCodeMap A} {H_L1 : Xcap.Halt (MachSt A)} :
    Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode (vcm.wp H_L1) H_L1 :=
  fun pc b hb s hbw Ψ hcl => hcl pc b hb s (Xcap.bwp_mono _ _ H_L1 (fun _ _ hw => hw Ψ hcl) hbw)

/-! ## §1. Open `fromWord` Simulation, XCAP `cptr` Soundness & Adequacy -/

/-- Open-world ranked simulation for `fromWord b cm = .ok vcm`: any open L0 `OpenModOk`
module with external imports `Imp` bridged to `Ψ_L1` via `hImp` validates every exported entry
`Exp r pc st` directly in any closed XCAP spec `(Ψ_L1, H_L1)` over `vllXcapMach A vcm.symAddr`.
-/
theorem fromWord_open_cptr_sound {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hfw : fromWord b cm = .ok vcm)
    {H_L0 : HaltPost} {SymReq : SymEnv → Prop} {Imp Exp : Nat → BedrockWord.CodeSpec}
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hMod : OpenModOk cm H_L0 SymReq Imp Exp) (hSym : SymReq cm.symEnv)
    (hclL1 : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hHalt : ∀ c s, plainHaltPost A H_L0 sp0 ra0 (codeMapMaxBudget b cm) R c s → H_L1 c s)
    (hImp : ∀ r pc st s, Imp r pc st →
      WordPlainEntryRel b st (codeMapMaxBudget b cm) R s →
      (codeMapMaxBudget b cm > 0 →
        s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
        (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 (codeMapMaxBudget b cm) ⋆ R)) →
      Ψ_L1 pc s) :
    ∀ r pc st s, Exp r pc st →
      WordPlainEntryRel b st (codeMapMaxBudget b cm) R s →
      (codeMapMaxBudget b cm > 0 →
        s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
        (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 (codeMapMaxBudget b cm) ⋆ R)) →
      Ψ_L1 pc s := by
  let maxB := codeMapMaxBudget b cm
  obtain ⟨_, hvwf, _, hcmAddr, hEntries⟩ := fromWord_wf hfw
  have hMain : ∀ r pc st s, Exp r pc st →
      WordPlainAnchorRel b st sp0 ra0 maxB R s → Ψ_L1 pc s := by
    intro r
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro pc st s hExp hAnch
      let Ψ_r : BedrockWord.CodeSpec := fun pc' st' =>
        ∀ s', WordPlainAnchorRel b st' sp0 ra0 maxB R s' → Ψ_L1 pc' s'
      have hSub : ∀ r' < r, ∀ pc' st', (Imp r' pc' st' ∨ Exp r' pc' st') → Ψ_r pc' st' := by
        intro r' hr' pc' st' hIE s' hAnch'
        rcases hIE with hIm | hEx
        · have hA := (wordPlainAnchorRel_iff b st' sp0 ra0 maxB R s').mp hAnch'
          refine hImp r' pc' st' s' hIm ⟨hA.1, hA.2.1, fun hp => ?_⟩ ?_
          · obtain ⟨hspE, hbd, hsp, hra, hm⟩ := hA.2.2 hp
            exact ⟨hsp ▸ hspE, hbd, ra0, hra, by simpa [hsp] using hm⟩
          · intro hp; obtain ⟨_, _, hsp, hra, hm⟩ := hA.2.2 hp; exact ⟨hsp, hra, hm⟩
        · exact ih r' hr' pc' st' s' hEx hAnch'
      obtain ⟨blk, hlu, hbp⟩ := hMod cm.symEnv Ψ_r r (SymEnv.Ext.refl _) hSym hSub pc st hExp
      obtain ⟨e, he, rfl, rfl⟩ := codeMap_entry_mem_of_lookup hlu
      obtain ⟨hsa, _⟩ := hEntries e he
      obtain ⟨sA, sB, bs, hlo, hsub⟩ := fromWord_entry_blocks_sub hfw he
      rw [← hsa]
      exact lowerPlainEntry_bwp hawf hwf hvwf hclL1 hcmAddr hHalt
        (fun tgt st' s' hpsi hAnch' => hpsi s' hAnch')
        (plainEntryBudget_le_codeMapMaxBudget b he) hlo hsub hAnch hbp
  intro r pc st s hExp hRel hPre
  refine hMain r pc st s hExp ((wordPlainAnchorRel_iff b st sp0 ra0 maxB R s).mpr
    ⟨hRel.1, hRel.2.1, fun hp => ?_⟩)
  obtain ⟨hspE, hbd, _⟩ := hRel.2.2 hp
  obtain ⟨hsp, hra, hm⟩ := hPre hp
  exact ⟨hsp ▸ hspE, hbd, hsp, hra, hm⟩

/-- Closed XCAP `cptr` soundness for `fromWord b cm = .ok vcm`: every L0 `CodeMap.wp`-verified
entry `(pc, st)` produces a valid `Xcap.cptr` into `vcm.wp (plainHaltPost A H_L0 sp0 ra0
(codeMapMaxBudget b cm) R)` at `pc`. -/
theorem fromWord_cptr_sound {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hfw : fromWord b cm = .ok vcm)
    {H_L0 : HaltPost} {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    {pc : BitVec 64} {st : BedrockWord.State} (hwp : cm.wp H_L0 pc st) :
    Xcap.cptr (vcm.wp (plainHaltPost A H_L0 sp0 ra0 (codeMapMaxBudget b cm) R)) pc
      (fun s => WordRegsRel b st.regs s ∧
        (codeMapMaxBudget b cm = 0 → s.mem =⋆ Eq st.mem ⋆ R) ∧
        (codeMapMaxBudget b cm > 0 →
          A.abi.spEntry sp0 ∧ codeMapMaxBudget b cm + A.abi.raBytes ≤ 2 ^ 64 ∧
          s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
          (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 (codeMapMaxBudget b cm) ⋆ R))) := by
  let maxB := codeMapMaxBudget b cm
  obtain ⟨_, hvwf, _, hcmAddr, hEntries⟩ := fromWord_wf hfw
  intro s hs Ψ_L1 hclL1
  let Ψ_L0 : BedrockWord.CodeSpec := fun pc' st' =>
    ∀ s', WordPlainAnchorRel b st' sp0 ra0 maxB R s' → Ψ_L1 pc' s'
  have hclL0 : SpecsClosed cm cm.symEnv Ψ_L0 H_L0 := by
    intro pc' blk hlu st' hbp s' hAnch'
    obtain ⟨e, he, rfl, rfl⟩ := codeMap_entry_mem_of_lookup hlu
    obtain ⟨hsa, _⟩ := hEntries e he
    obtain ⟨sA, sB, bs, hlo, hsub⟩ := fromWord_entry_blocks_sub hfw he
    rw [← hsa]
    exact lowerPlainEntry_bwp hawf hwf hvwf hclL1 hcmAddr (fun _ _ h => h)
      (fun tgt st'' s'' hpsi hAnch'' => hpsi s'' hAnch'')
      (plainEntryBudget_le_codeMapMaxBudget b he) hlo hsub hAnch' hbp
  exact hwp Ψ_L0 hclL0 s ((wordPlainAnchorRel_iff b st sp0 ra0 maxB R s).mpr hs)

/-- Total-correctness `VllCodeMap.wp` soundness for `fromWord b cm = .ok vcm` from
`WordPlainEntryRel` with anchored hardware return address `ra0`. -/
theorem fromWord_wp_sound {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hfw : fromWord b cm = .ok vcm)
    {H_L0 : HaltPost} {pc : BitVec 64} {st : BedrockWord.State}
    (hwp : cm.wp H_L0 pc st) {R : Mem 64 → Prop} {s : MachSt A} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel b st (codeMapMaxBudget b cm) R s)
    (hanc : codeMapMaxBudget b cm > 0 → (vllFramePreds A).raReg s ra0 ∧
      (s.mem =⋆ Eq st.mem ⋆
        hwStackMem A (s.gpr A.abi.sp) ra0 (codeMapMaxBudget b cm) ⋆ R)) :
    vcm.wp (plainHaltPost A H_L0 (s.gpr A.abi.sp) ra0 (codeMapMaxBudget b cm) R) pc s := by
  refine fromWord_cptr_sound hawf hwf hfw hwp s ⟨hrel.1, hrel.2.1, fun hp => ?_⟩
  obtain ⟨hspE, hbd, _⟩ := hrel.2.2 hp
  obtain ⟨hra, hm⟩ := hanc hp
  exact ⟨hspE, hbd, rfl, hra, hm⟩

/-- Big-step halting adequacy corollary for `fromWord b cm = .ok vcm`: every `cm.wp`-verified
L0 entry halts at L1 in `VllCodeMap.Halts` satisfying `plainHaltPost`. -/
theorem fromWord_adequacy {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hfw : fromWord b cm = .ok vcm)
    {H_L0 : HaltPost} {pc : BitVec 64} {st : BedrockWord.State}
    (hwp : cm.wp H_L0 pc st) {R : Mem 64 → Prop} {s : MachSt A} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel b st (codeMapMaxBudget b cm) R s)
    (hanc : codeMapMaxBudget b cm > 0 → (vllFramePreds A).raReg s ra0 ∧
      (s.mem =⋆ Eq st.mem ⋆
        hwStackMem A (s.gpr A.abi.sp) ra0 (codeMapMaxBudget b cm) ⋆ R)) :
    ∃ c s', vcm.Halts pc s c s' ∧
      plainHaltPost A H_L0 (s.gpr A.abi.sp) ra0 (codeMapMaxBudget b cm) R c s' :=
  VllCodeMap.adequacy (fromWord_wp_sound hawf hwf hfw hwp hrel hanc)

/-! ## §2. Stage-1 `fromWordContify`, `PrivFrameCfg` & Dual-Return `vllCallPre` Soundness -/

private def ContifiedOnlyPred (_A : Arch) : Type := BitVec 64 × BedrockWord.State → Prop

private def ContifiedOnlyNode (A : Arch) (b : WordRegBind A) (cm : CodeMap)
    (vcm : VllCodeMap A) (H_L0 : HaltPost) (Ψ_L1 : Xcap.CodeSpec (MachSt A))
    (H_L1 : Xcap.Halt (MachSt A)) (pre : List ContifyRegion) (cr : ContifyRegion)
    (dualRet : Bool) (sp_c rp0 ra_c hwSp : BitVec 64) (m0 : Mem 64)
    (G : Mem 64 → Prop) (Post_L0 : Bool → BedrockWord.State → Prop)
    (Φ : ContifiedOnlyPred A) : ContifiedOnlyPred A := fun (pc, st) =>
  (pc ∈ cr.allPcs ∧
    ((regionMemFree cm (foldCallees cm [] pre) cr = true → st.mem = m0) →
      (regionMemFree cm (foldCallees cm [] pre) cr = true → st.regs.sp = sp_c) →
      st.regs.rp = rp0 →
      ∀ (slots : List (BitVec 64)) (s : MachSt A),
        slots.length = (if regionNeedFrame b cm cr then regionFrameSlots b cm cr else 0) →
        WordRegsRel b st.regs s →
        (regionNeedFrame b cm cr = false → (vllFramePreds A).raReg s ra_c) →
        s.gpr A.abi.sp = hwSp →
        (array64 hwSp slots ⋆
          (contMemPred (regionMemFree cm (foldCallees cm [] pre) cr) st.mem ⋆ G)) s.mem →
        (∀ (isAlt : Bool) (s_fin : MachSt A) (nxt' : Regs) (m' : Mem 64)
          (slots' : List (BitVec 64)),
          (isAlt = true → dualRet = true) →
          (regionMemFree cm (foldCallees cm [] pre) cr = true → m' = st.mem) →
          (regionMemFree cm (foldCallees cm [] pre) cr = true → nxt'.sp = sp_c) →
          slots'.length = (if regionNeedFrame b cm cr then regionFrameSlots b cm cr else 0) →
          WordRegsRel b nxt' s_fin →
          (dualRet = true → ValHolds64 .bool isAlt (s_fin.gpr b.altRet)) →
          (regionNeedFrame b cm cr = false → (vllFramePreds A).raReg s_fin ra_c) →
          s_fin.gpr A.abi.sp = hwSp →
          (array64 hwSp slots' ⋆
            (contMemPred (regionMemFree cm (foldCallees cm [] pre) cr) m' ⋆ G)) s_fin.mem →
          Φ (rp0 + (if isAlt then 8#64 else 0#64), ⟨nxt', m'⟩) →
          bodyWp A vcm.symAddr
            (if regionNeedFrame b cm cr then [.epilogue (regionFrameSlots b cm cr)] else [])
            (fun s' => termWp A vcm.symAddr .ret Ψ_L1 H_L1 s') Ψ_L1 H_L1 s_fin) →
        (regionMemFree cm (foldCallees cm [] pre) cr = false →
          (∃ pc_h ∈ cr.allPcs, ∃ blk_h, cm.lookupAddr pc_h = some blk_h ∧
            noHaltBlock blk_h = false) →
          ∀ (s_fin : MachSt A) (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
            slots'.length =
              (if regionNeedFrame b cm cr then regionFrameSlots b cm cr else 0) →
            s_fin.gpr b.w0 = cVal → s_fin.gpr A.abi.sp = hwSp →
            (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
            H_L0 cVal m' →
            bodyWp A vcm.symAddr
              (if regionNeedFrame b cm cr then [.epilogue (regionFrameSlots b cm cr)] else [])
              (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin) →
        Ψ_L1 (vcm.symAddr (innerLabel cr pc)) s)) ∨
  (∃ isAlt : Bool,
    (isAlt = true → dualRet = true) ∧
    pc = rp0 + (if isAlt then 8#64 else 0#64) ∧
    (regionMemFree cm (foldCallees cm [] pre) cr = true →
      st.mem = m0 ∧ st.regs.sp = sp_c) ∧
    Post_L0 isAlt st)

private theorem contifiedOnlyNode_mono (A : Arch) (b : WordRegBind A) (cm : CodeMap)
    (vcm : VllCodeMap A) (H_L0 : HaltPost) (Ψ_L1 : Xcap.CodeSpec (MachSt A))
    (H_L1 : Xcap.Halt (MachSt A)) (pre : List ContifyRegion) (cr : ContifyRegion)
    (dualRet : Bool) (sp_c rp0 ra_c hwSp : BitVec 64) (m0 : Mem 64)
    (G : Mem 64 → Prop) (Post_L0 : Bool → BedrockWord.State → Prop) :
    Xcap.Lfp.mono
      (ContifiedOnlyNode A b cm vcm H_L0 Ψ_L1 H_L1 pre cr dualRet sp_c rp0 ra_c hwSp m0
        G Post_L0) := by
  intro Φ₁ Φ₂ hle p hp
  rcases hp with ⟨hpc, hrun⟩ | hRet
  · refine Or.inl ⟨hpc, fun hm0 hsp0 hrp slots s hlen hr hra hsp hm hExtRet hExtHalt => ?_⟩
    exact hrun hm0 hsp0 hrp slots s hlen hr hra hsp hm
      (fun isAlt s_f nxt' m' sl' ha hm' hsp' hl' hr' hdu hra' hsp'' hm'' hPhi =>
        hExtRet isAlt s_f nxt' m' sl' ha hm' hsp' hl' hr' hdu hra' hsp'' hm'' (hle _ hPhi))
      hExtHalt
  · exact Or.inr hRet

private theorem contified_region_entry_bwp {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {pre : List ContifyRegion} {cr : ContifyRegion} {post : List ContifyRegion}
    (hSplit : wit.regions = pre ++ cr :: post) {dualRet : Bool}
    (habi : cr.abi = .contified dualRet)
    {cb : Nat} (hCb : regionStackBudget b cm wit cr ≤ cb)
    (hbd : cb + A.abi.raBytes ≤ 2 ^ 64)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    {sp_c ra_c : BitVec 64} {R_c : Mem 64 → Prop} {st₀ : BedrockWord.State}
    {Post_L0 : Bool → BedrockWord.State → Prop}
    (hHalt : regionMemFree cm (foldCallees cm [] pre) cr = false →
      ∀ c s', wordHaltPost A H_L0 (region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c)
        c s' → H_L1 c s')
    (hrpDisj : st₀.regs.rp ∉ cr.allPcs ∧ (dualRet = true → st₀.regs.rp + 8#64 ∉ cr.allPcs))
    (hL0 : ∀ (Ψ_L0 : BedrockWord.CodeSpec),
      (∀ pc blk, pc ∈ cr.allPcs → cm.lookupAddr pc = some blk →
        ∀ st', blk.wp cm.symEnv Ψ_L0 H_L0 (pushRegsV st'.regs.toRegsV) st'.mem → Ψ_L0 pc st') →
      (∀ isAlt st', (isAlt = true → dualRet = true) →
        (regionMemFree cm (foldCallees cm [] pre) cr = true →
          st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) →
        Post_L0 isAlt st' →
        Ψ_L0 (st₀.regs.rp + (if isAlt then 8#64 else 0#64)) st') →
      Ψ_L0 cr.entryPc st₀)
    {s : MachSt A}
    (hsp0 : regionMemFree cm (foldCallees cm [] pre) cr = true → st₀.regs.sp = sp_c)
    (hsp : s.gpr A.abi.sp = sp_c)
    (hr : WordRegsRel b st₀.regs s)
    (hra : (vllFramePreds A).raReg s ra_c)
    (hm : (s.mem =⋆
      (if regionMemFree cm (foldCallees cm [] pre) cr then emp else Eq st₀.mem) ⋆
      hwStackMem A sp_c ra_c cb ⋆ R_c))
    (hRetCont : Xcap.cptr Ψ_L1 ra_c (fun s' =>
      ∃ (isAlt : Bool) (st' : BedrockWord.State),
        (isAlt = true → dualRet = true) ∧
        (regionMemFree cm (foldCallees cm [] pre) cr = true →
          st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) ∧
        Post_L0 isAlt st' ∧
        WordRegsRel b st'.regs s' ∧
        (dualRet = true → ValHolds64 .bool isAlt (s'.gpr b.altRet)) ∧
        s'.gpr A.abi.sp = sp_c + BitVec.ofNat 64 A.abi.raBytes ∧
        (s'.mem =⋆ (if regionMemFree cm (foldCallees cm [] pre) cr then emp else Eq st'.mem) ⋆
          region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c))) :
    Ψ_L1 (vcm.symAddr cr.name) s := by
  obtain ⟨_, hwck, hvwf, _, _, _, _, hCmAddr_raw⟩ := fromWordContify_wf hfc
  have hcmAddr : ∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a :=
    fun sym a ha => hCmAddr_raw sym a hSymAgree ha
  have hcr : cr ∈ wit.regions := by rw [hSplit]; simp
  have hchk := witness_checkAux_split hwck hSplit
  have hEntPc := checkContRegion_entryPc_mem hchk
  have hPriv0 : cr.privFrame.numSlots = 0 := Decidable.byContradiction fun hne => by
    have := (checkContRegion_priv_facts hchk).2 (Nat.pos_of_ne_zero hne)
    rw [habi] at this; cases this
  obtain ⟨_, hSelfLe, _⟩ := witnessBudgets_split b cm hwck hSplit
  let needFC := regionNeedFrame b cm cr
  let nsC := regionFrameSlots b cm cr
  let isMF := regionMemFree cm (foldCallees cm [] pre) cr
  let hwSp := if needFC then sp_c - BitVec.ofNat 64 (A.abi.frameSize nsC) else sp_c
  let G :=
    if needFC then (vllFramePreds A).Saved sp_c ra_c nsC ⋆
      region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ R_c
    else (vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆ R_c
  let Φ : ContifiedOnlyPred A := Xcap.Lfp.lfp
    (ContifiedOnlyNode A b cm vcm H_L0 Ψ_L1 H_L1 pre cr dualRet sp_c st₀.regs.rp ra_c hwSp
      st₀.mem G Post_L0)
  have hmono := contifiedOnlyNode_mono A b cm vcm H_L0 Ψ_L1 H_L1 pre cr dualRet sp_c st₀.regs.rp
    ra_c hwSp st₀.mem G Post_L0
  let Ψ_L0 : BedrockWord.CodeSpec := fun pc st => Φ (pc, st)
  have hBlks : ∀ pc blk, pc ∈ cr.allPcs → cm.lookupAddr pc = some blk →
      ∀ st', blk.wp cm.symEnv Ψ_L0 H_L0 (pushRegsV st'.regs.toRegsV) st'.mem → Ψ_L0 pc st' := by
    intro pc blk hpc hlu st' hbp
    refine Xcap.Lfp.lfp_closed hmono (pc, st') (Or.inl ⟨hpc, ?_⟩)
    obtain ⟨pcsInner, hpcsSub, hLeavesChk⟩ := checkContRegion_allPcs_leaf hchk hpc
    obtain ⟨ceBlk, _, _, bs, hluC, hlo, hsub⟩ := fromWordContify_contBlock_sub hfc hcr hpc
    have hceEq : ceBlk = blk := by rw [hluC] at hlu; cases hlu; rfl
    rw [hceEq] at hlo hluC
    have hLeavesFacts := checkContBlockLeaves_facts hluC hLeavesChk
    have hBounds := regionFrame_bounds (b := b) hchk hpc hluC
    obtain ⟨_, hMaxBd, hPriv64, hPrivEnv, hNeedCall, hsb_le, hspills, _⟩ := hBounds
    intro hm_st' hsp_st' hrp_st' slots s_cur hlen hr_cur hra_cur hsp_cur hm_cur hExtRet hExtHalt
    by_cases hmf : isMF = true
    · have hmf' : regionMemFree cm (foldCallees cm [] pre) cr = true := hmf
      have hnoM := regionMemFree_blockNoMem hmf hpc hlu
      have hnoH := noHaltBlock_of_blockNoMem blk hnoM
      have hbp_nf := noHaltBlock_wp_false (H₂ := fun _ _ => False) blk
        (pushRegsV st'.regs.toRegsV) st'.mem hnoH hbp
      have hbp_emp := regionMemFree_block_wp hmf hpc hlu (m₂ := (∅ : Mem 64))
        (H₂ := fun _ _ => False) hbp_nf
      refine lowerContBlock_bwp hawf hwf hvwf pc
        (sp0 := sp_c) (rp0 := st₀.regs.rp) (hwSp := hwSp) (ra₀ := ra_c) (G := G)
        hcl hcmAddr hPriv64 hPrivEnv hNeedCall hsb_le hspills
        ?_ (fun ⟨hEnv, _⟩ => by rw [habi] at hEnv; cases hEnv)
        (fun _ _ _ _ _ _ _ _ hF => False.elim hF) ?_
        (fun hEnv => by rw [habi] at hEnv; cases hEnv)
        blk (innerLabel cr pc) [] st'.regs (∅ : Mem 64) (∅ : Mem 64) s_cur hMaxBd
        (fun hp => absurd hp (by simp [hPriv0])) (fun _ => hrp_st')
        hLeavesFacts.2.1 hLeavesFacts.2.2 hlo hsub hbp_emp ?_
      · intro p nxtR mC mP sl s_t hp hl hr' _ hnr hra' hsp' hpr hm' ⟨hPhi, hspN, hmC⟩
        dsimp only at hspN hmC
        have hpAll := checkContRegion_pcs_mem hchk hpcsSub hp
        rcases Xcap.Lfp.lfp_post hmono (p, ⟨nxtR, st'.mem⟩) hPhi with
          ⟨_, hInnerRun⟩ | ⟨isAlt, ha_du, hEqRp, _⟩
        · have hmCP : mC = mP := (stage1PrivSlots_zero_eq hPriv0).mp hpr
          rw [← hmCP, hmC] at hm'
          exact hInnerRun (fun _ => hm_st' hmf) (fun _ => hspN.trans (hsp_st' hmf))
            (hnr (by simp [habi, RegionAbi.isContified])) sl s_t hl hr' hra' hsp'
            (by simpa [contMemPred_eq, hmf'] using hm')
            (fun iA s_f nx' m' sl' ha hm'' hsp'' hl'' hr'' hdu hra'' hsp''' hm''' hPh =>
              hExtRet iA s_f nx' m' sl' ha hm'' hsp'' hl'' hr'' hdu hra'' hsp''' hm''' hPh)
            hExtHalt
        · exfalso
          cases isAlt
          · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero] at hEqRp
            exact hrpDisj.1 (hEqRp ▸ hpAll)
          · simp only [↓reduceIte] at hEqRp
            exact hrpDisj.2 (ha_du rfl) (hEqRp ▸ hpAll)
      · intro dualRet' isAlt s_fin tgtVal nxt' m' slots' a_abi haok htgtEq hlen' hr' hAlt hra'
          hsp' hm' ⟨hPhi, hspN, hmC⟩
        dsimp only at hspN hmC
        have hduEq : dualRet' = dualRet := by rw [habi] at a_abi; cases a_abi; rfl
        subst hduEq
        rw [htgtEq] at hPhi
        rw [hmC] at hm'
        exact hExtRet isAlt s_fin nxt' st'.mem slots' haok (fun _ => rfl)
          (fun _ => hspN.trans (hsp_st' hmf)) hlen' hr' hAlt hra' hsp'
          (by simpa only [contMemPred_eq, hmf', ↓reduceIte] using hm') hPhi
      · dsimp only [bodyWp]
        exact ⟨slots, hlen, envRel_pushRegsV _ hr_cur, hr_cur,
          (stage1PrivSlots_zero_eq hPriv0).mpr rfl, hra_cur, hsp_cur,
          by simpa only [contMemPred_eq, hmf', ↓reduceIte] using hm_cur⟩
    · have hmfF : isMF = false := Bool.eq_false_iff.mpr hmf
      have hmfF' : regionMemFree cm (foldCallees cm [] pre) cr = false := hmfF
      by_cases hnh : noHaltBlock blk = true
      · have hbp_nf := noHaltBlock_wp_false (H₂ := fun _ _ => False) blk
          (pushRegsV st'.regs.toRegsV) st'.mem hnh hbp
        refine lowerContBlock_bwp hawf hwf hvwf pc
          (sp0 := sp_c) (rp0 := st₀.regs.rp) (hwSp := hwSp) (ra₀ := ra_c) (G := G)
          hcl hcmAddr hPriv64 hPrivEnv hNeedCall hsb_le hspills
          ?_ (fun ⟨hEnv, _⟩ => by rw [habi] at hEnv; cases hEnv)
          (fun _ _ _ _ _ _ _ _ hF => False.elim hF) ?_
          (fun hEnv => by rw [habi] at hEnv; cases hEnv)
          blk (innerLabel cr pc) [] st'.regs st'.mem st'.mem s_cur hMaxBd
          (fun hp => absurd hp (by simp [hPriv0])) (fun _ => hrp_st')
          hLeavesFacts.2.1 hLeavesFacts.2.2 hlo hsub hbp_nf ?_
        · intro p nxtR mC mP sl s_t hp hl hr' _ hnr hra' hsp' hpr hm' hPhi
          have hpAll := checkContRegion_pcs_mem hchk hpcsSub hp
          rcases Xcap.Lfp.lfp_post hmono (p, ⟨nxtR, mC⟩) hPhi with
            ⟨_, hInnerRun⟩ | ⟨isAlt, ha_du, hEqRp, _⟩
          · have hmCP : mC = mP := (stage1PrivSlots_zero_eq hPriv0).mp hpr
            rw [← hmCP] at hm'
            exact hInnerRun (fun h => absurd h hmf) (fun h => absurd h hmf)
              (hnr (by simp [habi, RegionAbi.isContified])) sl s_t hl hr' hra' hsp'
              (by simpa [contMemPred_eq, hmfF'] using hm')
              (fun iA s_f nx' m' sl' ha _ hsp'' hl'' hr'' hdu hra'' hsp''' hm''' hPh =>
                hExtRet iA s_f nx' m' sl' ha (fun h => absurd h hmf) hsp'' hl''
                  hr'' hdu hra'' hsp''' hm''' hPh)
              hExtHalt
          · exfalso
            cases isAlt
            · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero] at hEqRp
              exact hrpDisj.1 (hEqRp ▸ hpAll)
            · simp only [↓reduceIte] at hEqRp
              exact hrpDisj.2 (ha_du rfl) (hEqRp ▸ hpAll)
        · intro dualRet' isAlt s_fin tgtVal nxt' m' slots' a_abi haok htgtEq hlen' hr' hAlt hra'
            hsp' hm' hPhi
          have hduEq : dualRet' = dualRet := by rw [habi] at a_abi; cases a_abi; rfl
          subst hduEq
          rw [htgtEq] at hPhi
          exact hExtRet isAlt s_fin nxt' m' slots' haok (fun h => absurd h hmf)
            (fun h => absurd h hmf) hlen' hr' hAlt hra' hsp'
            (by simpa only [contMemPred_eq, hmfF', Bool.false_eq_true, ↓reduceIte] using hm') hPhi
        · dsimp only [bodyWp]
          exact ⟨slots, hlen, envRel_pushRegsV _ hr_cur, hr_cur,
            (stage1PrivSlots_zero_eq hPriv0).mpr rfl, hra_cur, hsp_cur,
            by simpa only [contMemPred_eq, hmfF', Bool.false_eq_true, ↓reduceIte] using hm_cur⟩
      · have hnhF : noHaltBlock blk = false := Bool.eq_false_iff.mpr hnh
        have hExH : ∃ pc_h ∈ cr.allPcs, ∃ blk_h, cm.lookupAddr pc_h = some blk_h ∧
            noHaltBlock blk_h = false := ⟨pc, hpc, blk, hlu, hnhF⟩
        refine lowerContBlock_bwp hawf hwf hvwf pc
          (sp0 := sp_c) (rp0 := st₀.regs.rp) (hwSp := hwSp) (ra₀ := ra_c) (G := G)
          hcl hcmAddr hPriv64 hPrivEnv hNeedCall hsb_le hspills
          ?_ (fun ⟨hEnv, _⟩ => by rw [habi] at hEnv; cases hEnv)
          (hExtHalt hmfF hExH) ?_ (fun hEnv => by rw [habi] at hEnv; cases hEnv)
          blk (innerLabel cr pc) [] st'.regs st'.mem st'.mem s_cur hMaxBd
          (fun hp => absurd hp (by simp [hPriv0])) (fun _ => hrp_st')
          hLeavesFacts.2.1 hLeavesFacts.2.2 hlo hsub hbp ?_
        · intro p nxtR mC mP sl s_t hp hl hr' _ hnr hra' hsp' hpr hm' hPhi
          have hpAll := checkContRegion_pcs_mem hchk hpcsSub hp
          rcases Xcap.Lfp.lfp_post hmono (p, ⟨nxtR, mC⟩) hPhi with
            ⟨_, hInnerRun⟩ | ⟨isAlt, ha_du, hEqRp, _⟩
          · have hmCP : mC = mP := (stage1PrivSlots_zero_eq hPriv0).mp hpr
            rw [← hmCP] at hm'
            exact hInnerRun (fun h => absurd h hmf) (fun h => absurd h hmf)
              (hnr (by simp [habi, RegionAbi.isContified])) sl s_t hl hr' hra' hsp'
              (by simpa [contMemPred_eq, hmfF'] using hm')
              (fun iA s_f nx' m' sl' ha _ hsp'' hl'' hr'' hdu hra'' hsp''' hm''' hPh =>
                hExtRet iA s_f nx' m' sl' ha (fun h => absurd h hmf) hsp'' hl''
                  hr'' hdu hra'' hsp''' hm''' hPh)
              hExtHalt
          · exfalso
            cases isAlt
            · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero] at hEqRp
              exact hrpDisj.1 (hEqRp ▸ hpAll)
            · simp only [↓reduceIte] at hEqRp
              exact hrpDisj.2 (ha_du rfl) (hEqRp ▸ hpAll)
        · intro dualRet' isAlt s_fin tgtVal nxt' m' slots' a_abi haok htgtEq hlen' hr' hAlt hra'
            hsp' hm' hPhi
          have hduEq : dualRet' = dualRet := by rw [habi] at a_abi; cases a_abi; rfl
          subst hduEq
          rw [htgtEq] at hPhi
          exact hExtRet isAlt s_fin nxt' m' slots' haok (fun h => absurd h hmf)
            (fun h => absurd h hmf) hlen' hr' hAlt hra' hsp'
            (by simpa only [contMemPred_eq, hmfF', Bool.false_eq_true, ↓reduceIte] using hm') hPhi
        · dsimp only [bodyWp]
          exact ⟨slots, hlen, envRel_pushRegsV _ hr_cur, hr_cur,
            (stage1PrivSlots_zero_eq hPriv0).mpr rfl, hra_cur, hsp_cur,
            by simpa only [contMemPred_eq, hmfF', Bool.false_eq_true, ↓reduceIte] using hm_cur⟩
  have hRetL0 : ∀ isAlt st', (isAlt = true → dualRet = true) →
      (isMF = true → st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) → Post_L0 isAlt st' →
      Ψ_L0 (st₀.regs.rp + (if isAlt then 8#64 else 0#64)) st' := fun isAlt st' ha hmSp hPost =>
    Xcap.Lfp.lfp_closed hmono _ (Or.inr ⟨isAlt, ha, rfl, hmSp, hPost⟩)
  have hPhi0 : Φ (cr.entryPc, st₀) := hL0 Ψ_L0 hBlks hRetL0
  have hRun0 := (Xcap.Lfp.lfp_post hmono (cr.entryPc, st₀) hPhi0).resolve_right
    (fun ⟨isAlt, ha_du, hEqRp, _⟩ => by
      cases isAlt
      · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero] at hEqRp
        exact hrpDisj.1 (hEqRp ▸ hEntPc)
      · simp only [↓reduceIte] at hEqRp
        exact hrpDisj.2 (ha_du rfl) (hEqRp ▸ hEntPc))
  have hRunEntry := hRun0.2 (fun _ => rfl) hsp0 rfl
  have handleRet : ∀ (isAlt : Bool) (s_fin : MachSt A) (nxt' : Regs) (m' : Mem 64)
      (slots' : List (BitVec 64)),
      (isAlt = true → dualRet = true) →
      (isMF = true → m' = st₀.mem) →
      (isMF = true → nxt'.sp = sp_c) →
      slots'.length = (if needFC then nsC else 0) →
      WordRegsRel b nxt' s_fin →
      (dualRet = true → ValHolds64 .bool isAlt (s_fin.gpr b.altRet)) →
      (needFC = false → (vllFramePreds A).raReg s_fin ra_c) →
      s_fin.gpr A.abi.sp = hwSp →
      (array64 hwSp slots' ⋆ (contMemPred isMF m' ⋆ G)) s_fin.mem →
      Φ (st₀.regs.rp + (if isAlt then 8#64 else 0#64), ⟨nxt', m'⟩) →
      bodyWp A vcm.symAddr (if needFC then [.epilogue nsC] else [])
        (fun s' => termWp A vcm.symAddr .ret Ψ_L1 H_L1 s') Ψ_L1 H_L1 s_fin := by
    intro isAlt s_fin nxt' m' slots' ha hm' hsp' hlen' hr' hdu hra' hsp'' hm'' hPhi
    have hsf : needFC = true → A.abi.frameSize nsC ≤ cb := fun hnf => by
      have hsf0 := hSelfLe
      simp only [show regionNeedFrame b cm cr = true from hnf, ↓reduceIte] at hsf0
      exact Nat.le_trans hsf0 hCb
    have hG_ret : (array64 hwSp slots' ⋆ (contMemPred isMF m' ⋆ G)) =
        (array64 hwSp slots' ⋆ (if needFC then
          ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
            region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆
            contMemPred isMF m' ⋆ R_c)
        else
          ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
            contMemPred isMF m' ⋆ R_c))) := by
      by_cases hnfC : needFC = true
      · simp only [G, ite_eq_left hnfC]; ac_rfl
      · simp only [G, ite_eq_right hnfC]; ac_rfl
    refine contified_epilogue_ret_bwp hawf hwf hsf hbd (fun h => by simp [hwSp, h])
      (fun h => by simp [hwSp, h]) hlen' hra' hsp''
      (G_ret := contMemPred isMF m') (G_outer := R_c) (hG_ret ▸ hm'') ?_
    intro s_ret hkeep hsp_ret hm_ret
    have hAltW : b.altRet ≠ A.abi.sp ∧ b.altRet ∉ A.abi.raRegs :=
      ⟨(work_not_sp hwf).1, (work_not_ra hwf).1⟩
    have hr_ret := wordRegsRel_of_keepNonSpRa hwf hr' hkeep
    have hPost2 : Post_L0 isAlt ⟨nxt', m'⟩ := by
      rcases Xcap.Lfp.lfp_post hmono
        (st₀.regs.rp + (if isAlt then 8#64 else 0#64), ⟨nxt', m'⟩) hPhi with
        ⟨hPcMem, _⟩ | ⟨isAlt2, _, hEqRp, _, hPo⟩
      · exfalso
        cases isAlt
        · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero] at hPcMem
          exact hrpDisj.1 hPcMem
        · simp only [↓reduceIte] at hPcMem
          exact hrpDisj.2 (ha rfl) hPcMem
      · have hAltEq : isAlt = isAlt2 := by
          cases isAlt <;> cases isAlt2
          · rfl
          · exfalso; simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero] at hEqRp
            exact add_8_ne_self st₀.regs.rp hEqRp.symm
          · exfalso; simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero] at hEqRp
            exact add_8_ne_self st₀.regs.rp hEqRp
          · rfl
        exact hAltEq ▸ hPo
    refine hRetCont s_ret ⟨isAlt, ⟨nxt', m'⟩, ha, fun h => ⟨hm' h, hsp' h⟩, hPost2, hr_ret,
      fun hd => by rw [hkeep b.altRet hAltW.1 hAltW.2]; exact hdu hd, hsp_ret, ?_⟩
    cases hmf : isMF
    · have hmfF : regionMemFree cm (foldCallees cm [] pre) cr = false := hmf
      have h1 : (contMemPred isMF m' ⋆
          (region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c)) s_ret.mem :=
        sep_cast hm_ret (by ac_rfl)
      simp only [contMemPred_eq, hmf, Bool.false_eq_true, ↓reduceIte] at h1
      simp only [hmfF, Bool.false_eq_true, ↓reduceIte]
      exact sep_cast h1 (by ac_rfl)
    · have hmfT : regionMemFree cm (foldCallees cm [] pre) cr = true := hmf
      have h1 : (contMemPred isMF m' ⋆
          (region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c)) s_ret.mem :=
        sep_cast hm_ret (by ac_rfl)
      simp only [contMemPred_eq, hmf, eq_empty_eq_emp, ↓reduceIte, emp_sep] at h1
      simp only [hmfT, ↓reduceIte, emp_sep]
      exact sep_cast h1 (by ac_rfl)
  have handleHalt : isMF = false →
      (∃ pc_h ∈ cr.allPcs, ∃ blk_h, cm.lookupAddr pc_h = some blk_h ∧
        noHaltBlock blk_h = false) →
      ∀ (s_fin : MachSt A) (cVal : BitVec 64) (m' : Mem 64) (slots' : List (BitVec 64)),
        slots'.length = (if needFC then nsC else 0) →
        s_fin.gpr b.w0 = cVal → s_fin.gpr A.abi.sp = hwSp →
        (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) s_fin.mem →
        H_L0 cVal m' →
      bodyWp A vcm.symAddr (if needFC then [.epilogue nsC] else [])
        (fun s' => H_L1 (s'.gpr b.w0) s') Ψ_L1 H_L1 s_fin := by
    intro hmfF _ s_fin cVal m' slots' hlen' hw0' hsp'' hm'' hHL0
    have hsf : needFC = true → A.abi.frameSize nsC ≤ cb := fun hnf => by
      have hsf0 := hSelfLe
      simp only [show regionNeedFrame b cm cr = true from hnf, ↓reduceIte] at hsf0
      exact Nat.le_trans hsf0 hCb
    have hG_halt : (array64 hwSp slots' ⋆ (Eq m' ⋆ G)) =
        (array64 hwSp slots' ⋆ (if needFC then
          ((vllFramePreds A).Saved sp_c ra_c nsC ⋆
            region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆ (Eq m' ⋆ R_c))
        else
          ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆
            (Eq m' ⋆ R_c)))) := by
      by_cases hnfC : needFC = true
      · simp only [G, ite_eq_left hnfC]; ac_rfl
      · simp only [G, ite_eq_right hnfC]; ac_rfl
    refine contified_epilogue_halt_bwp hawf hwf hsf hbd (fun h => by simp [hwSp, h])
      (fun h => by simp [hwSp, h]) hlen' hsp'' hw0' (hG_halt ▸ hm'') ?_
    intro s' _ hm_post
    exact hHalt hmfF cVal s' ⟨m', hHL0, sep_cast hm_post (by ac_rfl)⟩
  have hBlk := fromWordContify_entry_block_mem hfc hcr
  refine closed_bwp hvwf hcl hBlk ?_
  dsimp only
  rw [hPriv0]
  simp only [emitPrivFrameInit, beq_self_eq_true, ↓reduceIte, List.append_nil]
  have hm_pre : s.mem =⋆ contMemPred isMF st₀.mem ⋆
      ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆ R_c) := by
    cases hmf : isMF
    · have hmfF : regionMemFree cm (foldCallees cm [] pre) cr = false := hmf
      simp only [contMemPred_eq, hmfF, Bool.false_eq_true, ↓reduceIte, hwStackMem] at hm ⊢
      exact sep_cast hm (by ac_rfl)
    · have hmfT : regionMemFree cm (foldCallees cm [] pre) cr = true := hmf
      simp only [contMemPred_eq, hmfT, eq_empty_eq_emp, ↓reduceIte, hwStackMem] at hm ⊢
      exact sep_cast hm (by ac_rfl)
  by_cases hnf : needFC = true
  · have hnf' : regionNeedFrame b cm cr = true := hnf
    have hsf : A.abi.frameSize nsC ≤ cb := by
      have hsf0 := hSelfLe
      simp only [hnf', ↓reduceIte] at hsf0
      exact Nat.le_trans hsf0 hCb
    have hfsBd : A.abi.frameSize nsC ≤ 2 ^ 64 := by omega
    have hm_pro : s.mem =⋆ (vllFramePreds A).RetAddr (s.gpr A.abi.sp) ra_c ⋆
        region (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize nsC)) (A.abi.frameSize nsC) ⋆
        (region (sp_c - BitVec.ofNat 64 cb) (cb - A.abi.frameSize nsC) ⋆
          contMemPred isMF st₀.mem ⋆ R_c) := by
      rw [region_sub_split (a := sp_c) hsf (by omega)] at hm_pre
      simpa only [hsp] using sep_cast hm_pre (by ac_rfl)
    simp only [hnf', ↓reduceIte]
    refine instrWp_prologue hawf hra hfsBd hm_pro ?_
    intro slots hlen; dsimp only; intro m_pro hm_pro'
    have hr' : WordRegsRel b st₀.regs
        (((s.setGpr A.abi.sp (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize nsC))).setMem
          m_pro).setFlags (A.prologueFlags nsC s.flags)) := by
      simpa only [wordRegsRel_setFlags, wordRegsRel_setMem, wordRegsRel_setSp hwf] using hr
    have hm' : (array64 hwSp slots ⋆ (contMemPred isMF st₀.mem ⋆ G))
        (((s.setGpr A.abi.sp (s.gpr A.abi.sp - BitVec.ofNat 64 (A.abi.frameSize nsC))).setMem
          m_pro).setFlags (A.prologueFlags nsC s.flags)).mem := by
      simp only [MachSt.mem_setFlags, MachSt.mem_setMem, hsp, hwSp, G, ite_eq_left hnf, nsC]
        at hm_pro' ⊢
      exact sep_cast hm_pro' (by ac_rfl)
    dsimp only [bodyWp]
    exact termWp_fall (hRunEntry slots _ (by simpa [hnf'] using hlen) hr'
      (fun h => by simp [hnf'] at h) (by simp [hwSp, hsp, hnf, nsC]) hm' handleRet handleHalt)
  · have hnfF : needFC = false := Bool.eq_false_iff.mpr hnf
    have hnfF' : regionNeedFrame b cm cr = false := hnfF
    simp only [hnfF', Bool.false_eq_true, ↓reduceIte, bodyWp]
    have hpre_eq : contMemPred isMF st₀.mem ⋆
        ((vllFramePreds A).RetAddr sp_c ra_c ⋆ region (sp_c - BitVec.ofNat 64 cb) cb ⋆ R_c) =
        contMemPred (regionMemFree cm (foldCallees cm [] pre) cr) st₀.mem ⋆ G := by
      simp only [G, ite_eq_right hnf]; ac_rfl
    refine termWp_fall (hRunEntry [] s (by simp [hnfF']) hr (fun _ => hra)
      (by simp [hwSp, hsp, hnfF]) (sep_array64_emp _ (hpre_eq ▸ hm_pre)) handleRet handleHalt)

/-- Modular XCAP `vllCallPre` specification for a Stage-1 `.contified dualRet` callee `cr`:
works uniformly for both AAPCS64 `.linkReg lr` (`bl`/`ret`) and SysV `.stack` (`call`/`ret`),
preserving caller's stack budget `cb`, frame `R_c`, and dual-return flag `b.altRet`. -/
theorem contified_open_cptr_spec {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {pre : List ContifyRegion} {cr : ContifyRegion} {post : List ContifyRegion}
    (hSplit : wit.regions = pre ++ cr :: post) {dualRet : Bool}
    (habi : cr.abi = .contified dualRet)
    {cb : Nat} (hCb : regionStackBudget b cm wit cr ≤ cb)
    (hbd : cb + A.abi.raBytes ≤ 2 ^ 64)
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hcl : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (sp_c : BitVec 64) (R_c : Mem 64 → Prop) (st₀ : BedrockWord.State)
    (Post_L0 : Bool → BedrockWord.State → Prop)
    (hHalt : regionMemFree cm (pre.foldl (fun a r =>
        match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = false →
      ∀ c s', wordHaltPost A H_L0 (region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c)
        c s' → H_L1 c s')
    (hsp0 : regionMemFree cm (pre.foldl (fun a r =>
        match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
      st₀.regs.sp = sp_c)
    (hrpDisj : st₀.regs.rp ∉ cr.allPcs ∧ (dualRet = true → st₀.regs.rp + 8#64 ∉ cr.allPcs))
    (hL0 : ∀ (Ψ_L0 : BedrockWord.CodeSpec),
      (∀ pc blk, pc ∈ cr.allPcs → cm.lookupAddr pc = some blk →
        ∀ st', blk.wp cm.symEnv Ψ_L0 H_L0 (pushRegsV st'.regs.toRegsV) st'.mem → Ψ_L0 pc st') →
      (∀ isAlt st', (isAlt = true → dualRet = true) →
        (regionMemFree cm (pre.foldl (fun a r =>
            match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
          st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) →
        Post_L0 isAlt st' →
        Ψ_L0 (st₀.regs.rp + (if isAlt then 8#64 else 0#64)) st') →
      Ψ_L0 cr.entryPc st₀) :
    Xcap.cptr Ψ_L1 (vcm.symAddr cr.name)
      (vllCallPre A
        (fun s => s.gpr A.abi.sp = sp_c ∧ WordRegsRel b st₀.regs s ∧
          ∃ ra₀, (vllFramePreds A).raReg s ra₀ ∧
            (s.mem =⋆
              (if regionMemFree cm (pre.foldl (fun a r =>
                match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr
                then emp else Eq st₀.mem) ⋆
              hwStackMem A sp_c ra₀ cb ⋆ R_c))
        (fun s' => ∃ (isAlt : Bool) (st' : BedrockWord.State),
          (isAlt = true → dualRet = true) ∧
          (regionMemFree cm (pre.foldl (fun a r =>
              match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
            st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) ∧
          Post_L0 isAlt st' ∧
          WordRegsRel b st'.regs s' ∧
          (dualRet = true → ValHolds64 .bool isAlt (s'.gpr b.altRet)) ∧
          s'.gpr A.abi.sp = sp_c + BitVec.ofNat 64 A.abi.raBytes ∧
          (s'.mem =⋆
            (if regionMemFree cm (pre.foldl (fun a r =>
              match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr
              then emp else Eq st'.mem) ⋆
            region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c))
        Ψ_L1) := by
  have heqF := foldl_toCalleeMeta_eq cm pre []
  let hHalt' : regionMemFree cm (foldCallees cm [] pre) cr = false →
      ∀ c s', wordHaltPost A H_L0 (region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c)
        c s' → H_L1 c s' := fun h => hHalt (heqF ▸ h)
  let hsp0' : regionMemFree cm (foldCallees cm [] pre) cr = true → st₀.regs.sp = sp_c :=
    fun h => hsp0 (heqF ▸ h)
  let hL0' : ∀ (Ψ_L0 : BedrockWord.CodeSpec),
      (∀ pc blk, pc ∈ cr.allPcs → cm.lookupAddr pc = some blk →
        ∀ st', blk.wp cm.symEnv Ψ_L0 H_L0 (pushRegsV st'.regs.toRegsV) st'.mem → Ψ_L0 pc st') →
      (∀ isAlt st', (isAlt = true → dualRet = true) →
        (regionMemFree cm (foldCallees cm [] pre) cr = true →
          st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) →
        Post_L0 isAlt st' →
        Ψ_L0 (st₀.regs.rp + (if isAlt then 8#64 else 0#64)) st') →
      Ψ_L0 cr.entryPc st₀ := fun Ψ hb hr =>
    hL0 Ψ hb (fun iA st' ha hmSt hf => hr iA st' ha (heqF ▸ hmSt) hf)
  intro s hs
  cases hkind : A.abi.raKind with
  | linkReg lr =>
    simp only [vllCallPre, hkind, Xcap.callPre] at hs
    rcases hs with ⟨⟨hsp, hr, ra₀, hra₀, hm⟩, hRet⟩
    have hEqRa : s.gpr lr = ra₀ := by simpa [vllFramePreds, hkind] using hra₀
    rw [hEqRa] at hRet
    exact contified_region_entry_bwp hawf hwf hfc hSymAgree hSplit habi hCb hbd hcl
      hHalt' hrpDisj hL0' hsp0' hsp hr hra₀ (heqF ▸ hm) (heqF ▸ hRet)
  | stack =>
    simp only [vllCallPre, hkind] at hs
    rcases hs with ⟨⟨hsp, hr, ra₀, hra₀, hm⟩, ra, hld, hRet⟩
    have hm_cell : (cell64 sp_c ra₀ ⋆
        ((if regionMemFree cm (foldCallees cm [] pre) cr then emp else Eq st₀.mem) ⋆
          region (sp_c - BitVec.ofNat 64 cb) cb ⋆ R_c)) s.mem := by
      simp only [hwStackMem, vllFramePreds, hkind] at hm
      exact heqF ▸ sep_cast hm (by ac_rfl)
    have hld0 : loadVal s.mem i64 (s.gpr A.abi.sp) = some ra₀ := by
      rw [hsp]; exact loadVal_cell64 hm_cell
    have hEqRa : ra = ra₀ := Option.some.inj (hld.symm.trans hld0)
    subst hEqRa
    exact contified_region_entry_bwp hawf hwf hfc hSymAgree hSplit habi hCb hbd hcl
      hHalt' hrpDisj hL0' hsp0' hsp hr hra₀ (heqF ▸ hm) (heqF ▸ hRet)

/-- Closed-`VllCodeMap.wp` specialization of `contified_open_cptr_spec` for a `.contified`
region `cr`. -/
theorem contified_cptr_spec {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {pre : List ContifyRegion} {cr : ContifyRegion} {post : List ContifyRegion}
    (hSplit : wit.regions = pre ++ cr :: post) {dualRet : Bool}
    (habi : cr.abi = .contified dualRet)
    {cb : Nat} (hCb : regionStackBudget b cm wit cr ≤ cb)
    (hbd : cb + A.abi.raBytes ≤ 2 ^ 64)
    {H_L0 : HaltPost} (H_L1 : Xcap.Halt (MachSt A))
    (sp_c : BitVec 64) (R_c : Mem 64 → Prop) (st₀ : BedrockWord.State)
    (Post_L0 : Bool → BedrockWord.State → Prop)
    (hHalt : regionMemFree cm (pre.foldl (fun a r =>
        match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = false →
      ∀ c s', wordHaltPost A H_L0 (region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c)
        c s' → H_L1 c s')
    (hsp0 : regionMemFree cm (pre.foldl (fun a r =>
        match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
      st₀.regs.sp = sp_c)
    (hrpDisj : st₀.regs.rp ∉ cr.allPcs ∧ (dualRet = true → st₀.regs.rp + 8#64 ∉ cr.allPcs))
    (hL0 : ∀ (Ψ_L0 : BedrockWord.CodeSpec),
      (∀ pc blk, pc ∈ cr.allPcs → cm.lookupAddr pc = some blk →
        ∀ st', blk.wp cm.symEnv Ψ_L0 H_L0 (pushRegsV st'.regs.toRegsV) st'.mem → Ψ_L0 pc st') →
      (∀ isAlt st', (isAlt = true → dualRet = true) →
        (regionMemFree cm (pre.foldl (fun a r =>
            match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
          st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) →
        Post_L0 isAlt st' →
        Ψ_L0 (st₀.regs.rp + (if isAlt then 8#64 else 0#64)) st') →
      Ψ_L0 cr.entryPc st₀) :
    Xcap.cptr (vcm.wp H_L1) (vcm.symAddr cr.name)
      (vllCallPre A
        (fun s => s.gpr A.abi.sp = sp_c ∧ WordRegsRel b st₀.regs s ∧
          ∃ ra₀, (vllFramePreds A).raReg s ra₀ ∧
            (s.mem =⋆
              (if regionMemFree cm (pre.foldl (fun a r =>
                match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr
                then emp else Eq st₀.mem) ⋆
              hwStackMem A sp_c ra₀ cb ⋆ R_c))
        (fun s' => ∃ (isAlt : Bool) (st' : BedrockWord.State),
          (isAlt = true → dualRet = true) ∧
          (regionMemFree cm (pre.foldl (fun a r =>
              match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
            st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) ∧
          Post_L0 isAlt st' ∧
          WordRegsRel b st'.regs s' ∧
          (dualRet = true → ValHolds64 .bool isAlt (s'.gpr b.altRet)) ∧
          s'.gpr A.abi.sp = sp_c + BitVec.ofNat 64 A.abi.raBytes ∧
          (s'.mem =⋆
            (if regionMemFree cm (pre.foldl (fun a r =>
              match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr
              then emp else Eq st'.mem) ⋆
            region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c))
        (vcm.wp H_L1)) :=
  contified_open_cptr_spec hawf hwf hfc hSymAgree hSplit habi hCb hbd vllWp_closed
    sp_c R_c st₀ Post_L0 hHalt hsp0 hrpDisj hL0

/-- Open-world Stage-1 simulation theorem for `fromWordContify b cm wit = .ok vcm`, supporting
residual cold code (`wRes`), open bailouts/guards (`ExtSpec` + pure-L0 invariant `Inv`), and
`PrivFrameCfg` private slot promotion (`[sp - 8*(k+1)]`). -/
theorem fromWordContify_open_cptr_sound {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hclL1 : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hHalt : ∀ c s, wordHaltPost A H_L0 (if budget = 0 then R
      else region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R) c s → H_L1 c s)
    (ExtSpec Inv : BedrockWord.CodeSpec)
    (hExt : ∀ tgt st s, ExtSpec tgt st →
      WordPlainEntryRel b st budget R s →
      (budget > 0 → s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
        (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 budget ⋆ R)) →
      Ψ_L1 tgt s)
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
            ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k))))
    {pc : BitVec 64} {st : BedrockWord.State} {s : MachSt A}
    (hEntry : (∃ e ∈ residualContifyCodeMap cm wit, e.addr = pc) ∨
      (∃ cr ∈ wit.regions, cr.abi = .retEnvelope ∧ cr.entryPc = pc ∧
        (cr.privFrame.numSlots > 0 → st.regs.sp = sp0 ∧ cr.privFrame.numSlots ≤ 64 ∧
          ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k))))
    (hInv0 : Inv pc st) (hwp : cm.wp H_L0 pc st)
    (hrel : WordPlainEntryRel b st budget R s)
    (hanc : budget > 0 → s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
      (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 budget ⋆ R)) :
    Ψ_L1 pc s := by
  have hbd : budget + A.abi.raBytes ≤ 2 ^ 64 := by
    by_cases hp : budget > 0
    · exact (hrel.2.2 hp).2.1
    · have hz : budget = 0 := Nat.eq_zero_of_not_pos hp
      have h8 := raBytes_le_eight A
      omega
  have hspE_b : budget > 0 → A.abi.spEntry sp0 := fun hp => by
    rw [← (hanc hp).1]; exact (hrel.2.2 hp).1
  have hExt' : ∀ tgt st s', ExtSpec tgt st →
      WordPlainAnchorRel b st sp0 ra0 budget R s' → Ψ_L1 tgt s' := by
    intro tgt st' s' hE hAnch
    have hA := (wordPlainAnchorRel_iff b st' sp0 ra0 budget R s').mp hAnch
    refine hExt tgt st' s' hE ⟨hA.1, hA.2.1, fun hp => ?_⟩
      (fun hp => (hA.2.2 hp).2.2)
    obtain ⟨hspE, hbd', hsp', hra', hm'⟩ := hA.2.2 hp
    exact ⟨hsp' ▸ hspE, hbd', ra0, hra', by simpa [hsp'] using hm'⟩
  have hFix : ContifyFixExt A b cm wit vcm H_L0 Ψ_L1 H_L1 sp0 ra0 budget R ExtSpec Inv pc st :=
    hwp _ (contify_specsClosed_ext hawf hwf hfc hSymAgree hBudReg hBudRes hbd hspE_b hclL1 hHalt
      ExtSpec Inv hExt' hInvCl (fun hTrig tgt st' hI => hInvValid hTrig tgt st' hI))
  have hAnch : WordPlainAnchorRel b st sp0 ra0 budget R s :=
    (wordPlainAnchorRel_iff b st sp0 ra0 budget R s).mpr ⟨hrel.1, hrel.2.1, fun hp => by
      obtain ⟨hsp, hra, hm⟩ := hanc hp
      exact ⟨hspE_b hp, hbd, hsp, hra, hm⟩⟩
  rcases hEntry with ⟨e, he, rfl⟩ | ⟨cr, hcr, habi, rfl, hPriv⟩
  · exact contifyFixExt_resEntry hfc he hFix s hAnch
  · exact contifyFixExt_retEnvExt hfc hcr habi hFix hPriv s hAnch

/-- Closed-world Stage-1 XCAP `cptr` soundness for `fromWordContify b cm wit = .ok vcm` on any
`.retEnvelope` entry region `cr ∈ wit.regions`. -/
theorem fromWordContify_cptr_sound {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    (hNoRes : residualContifyCodeMap cm wit = [])
    (hNoDyn : ∀ cr' ∈ wit.regions, cr'.abi = .retEnvelope →
      cr'.privFrame.dynAliasGuard = false ∨ cr'.privFrame.numSlots = 0)
    (hNoOpenEdge : ∀ cr' ∈ wit.regions, cr'.abi = .retEnvelope → ∀ ew ∈ cr'.edges,
      match ew.kind with | .bailout | .guarded _ | .strideTable _ _ true => False | _ => True)
    {H_L0 : HaltPost} {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    {cr : ContifyRegion} (hcr : cr ∈ wit.regions) (habi : cr.abi = .retEnvelope)
    {st : BedrockWord.State} (hwp : cm.wp H_L0 cr.entryPc st)
    (hPriv : cr.privFrame.numSlots > 0 → st.regs.sp = sp0 ∧ cr.privFrame.numSlots ≤ 64 ∧
      ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k)) :
    Xcap.cptr
      (vcm.wp (wordHaltPost A H_L0 (if budget = 0 then R
        else region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R)))
      cr.entryPc
      (fun s => WordRegsRel b st.regs s ∧
        (budget = 0 → s.mem =⋆ Eq st.mem ⋆ R) ∧
        (budget > 0 → A.abi.spEntry sp0 ∧ budget + A.abi.raBytes ≤ 2 ^ 64 ∧
          s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
          (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 budget ⋆ R))) := by
  intro s hs Ψ_L1 hclL1
  have hbd : budget + A.abi.raBytes ≤ 2 ^ 64 := by
    by_cases hp : budget > 0
    · exact (hs.2.2 hp).2.1
    · have hz : budget = 0 := Nat.eq_zero_of_not_pos hp
      have h8 := raBytes_le_eight A
      omega
  have hspE_b : budget > 0 → A.abi.spEntry sp0 := fun hp => (hs.2.2 hp).1
  have hNoOpen : ¬ ((∃ e ∈ residualContifyCodeMap cm wit, True) ∨
      (∃ cr ∈ wit.regions, cr.abi = .retEnvelope ∧
        ((cr.privFrame.dynAliasGuard = true ∧ cr.privFrame.numSlots > 0) ∨
         ∃ ew ∈ cr.edges, match ew.kind with
           | .bailout | .guarded _ | .strideTable _ _ true => True | _ => False))) := by
    rintro (⟨e, he, _⟩ | ⟨cr', hcr', habi', hOr⟩)
    · rw [hNoRes] at he; cases he
    · rcases hOr with ⟨hdyn, hpos⟩ | ⟨ew, hew, hBad⟩
      · rcases hNoDyn cr' hcr' habi' with hf | hz
        · rw [hf] at hdyn; cases hdyn
        · omega
      · have hOk := hNoOpenEdge cr' hcr' habi' ew hew
        cases hk : ew.kind with
        | bailout | guarded _ => rw [hk] at hOk; exact False.elim hOk
        | strideTable _ _ ng =>
          rw [hk] at hBad hOk
          cases ng <;> simp only at hBad hOk <;>
            first | exact False.elim hBad | exact False.elim hOk
        | _ => rw [hk] at hBad; exact False.elim hBad
  have hclL0 := contify_specsClosed (ra0 := ra0) hawf hwf hfc hSymAgree hBudReg hBudRes hbd
    hspE_b hclL1 (fun _ _ h => h) hNoOpen
  exact contifyFix_retEnvExt hfc hcr habi (hwp _ hclL0) hPriv s
    ((wordPlainAnchorRel_iff b st sp0 ra0 budget R s).mpr hs)

/-- Total-correctness `VllCodeMap.wp` soundness for closed Stage-1 `fromWordContify`. -/
theorem fromWordContify_wp_sound {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    (hNoRes : residualContifyCodeMap cm wit = [])
    (hNoDyn : ∀ cr' ∈ wit.regions, cr'.abi = .retEnvelope →
      cr'.privFrame.dynAliasGuard = false ∨ cr'.privFrame.numSlots = 0)
    (hNoOpenEdge : ∀ cr' ∈ wit.regions, cr'.abi = .retEnvelope → ∀ ew ∈ cr'.edges,
      match ew.kind with | .bailout | .guarded _ | .strideTable _ _ true => False | _ => True)
    {H_L0 : HaltPost} {R : Mem 64 → Prop} {cr : ContifyRegion}
    (hcr : cr ∈ wit.regions) (habi : cr.abi = .retEnvelope)
    {st : BedrockWord.State} (hwp : cm.wp H_L0 cr.entryPc st)
    {s : MachSt A} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel b st budget R s)
    (hanc : budget > 0 → (vllFramePreds A).raReg s ra0 ∧
      (s.mem =⋆ Eq st.mem ⋆ hwStackMem A (s.gpr A.abi.sp) ra0 budget ⋆ R))
    (hPriv : cr.privFrame.numSlots > 0 →
      st.regs.sp = s.gpr A.abi.sp ∧ cr.privFrame.numSlots ≤ 64 ∧
      ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k)) :
    vcm.wp (wordHaltPost A H_L0 (if budget = 0 then R
      else region (s.gpr A.abi.sp - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R))
      cr.entryPc s := by
  refine fromWordContify_cptr_sound (b := b) (ra0 := ra0) hawf hwf hfc hSymAgree hBudReg
    hBudRes hNoRes hNoDyn hNoOpenEdge hcr habi hwp hPriv s ⟨hrel.1, hrel.2.1, fun hp => ?_⟩
  obtain ⟨hspE, hbd, _⟩ := hrel.2.2 hp
  obtain ⟨hra, hm⟩ := hanc hp
  exact ⟨hspE, hbd, rfl, hra, hm⟩

/-- Big-step halting adequacy corollary for closed Stage-1 `fromWordContify`: every
`cm.wp`-verified `.retEnvelope` entry halts at L1 in `VllCodeMap.Halts`. -/
theorem fromWordContify_adequacy {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    (hNoRes : residualContifyCodeMap cm wit = [])
    (hNoDyn : ∀ cr' ∈ wit.regions, cr'.abi = .retEnvelope →
      cr'.privFrame.dynAliasGuard = false ∨ cr'.privFrame.numSlots = 0)
    (hNoOpenEdge : ∀ cr' ∈ wit.regions, cr'.abi = .retEnvelope → ∀ ew ∈ cr'.edges,
      match ew.kind with | .bailout | .guarded _ | .strideTable _ _ true => False | _ => True)
    {H_L0 : HaltPost} {R : Mem 64 → Prop} {cr : ContifyRegion}
    (hcr : cr ∈ wit.regions) (habi : cr.abi = .retEnvelope)
    {st : BedrockWord.State} (hwp : cm.wp H_L0 cr.entryPc st)
    {s : MachSt A} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel b st budget R s)
    (hanc : budget > 0 → (vllFramePreds A).raReg s ra0 ∧
      (s.mem =⋆ Eq st.mem ⋆ hwStackMem A (s.gpr A.abi.sp) ra0 budget ⋆ R))
    (hPriv : cr.privFrame.numSlots > 0 →
      st.regs.sp = s.gpr A.abi.sp ∧ cr.privFrame.numSlots ≤ 64 ∧
      ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k)) :
    ∃ c s', vcm.Halts cr.entryPc s c s' ∧
      wordHaltPost A H_L0 (if budget = 0 then R
        else region (s.gpr A.abi.sp - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R)
        c s' :=
  VllCodeMap.adequacy (fromWordContify_wp_sound hawf hwf hfc hSymAgree hBudReg hBudRes hNoRes
    hNoDyn hNoOpenEdge hcr habi hwp hrel hanc hPriv)

/-! ## §3. `VllCodeMap.Hosted` Small-Step Bridge & `Xcap.Bridge` Interoperability -/

/-- Host layout invariant linking a structured `VllCodeMap A` to a flat `VllHost A` program so
every `Xcap.Closed` invariant over `vllXcapMach A vcm.symAddr` discharges small-step `vllStep`
execution. -/
structure VllCodeMap.Hosted {A : Arch} (vcm : VllCodeMap A) (h : VllHost A) : Prop where
  labelAddr_eq : ∀ sym, h.labelAddr sym = vcm.symAddr sym
  blocks_ok : ∀ b ∈ vcm.blocks,
    (∀ i ∈ b.body, !i.isControl && !i.isNative = true) ∧
    ∃ (k : Nat) (nextLabel? : Option Sym),
      h.addrOf k = vcm.symAddr b.label ∧
      (b.toInstrs nextLabel?).IsInfixAt h.prog k ∧
      (let kTerm := k + 1 + (if b.pad?.isSome then 1 else 0) + b.body.length
       match b.term with
       | .fall n => nextLabel? = some n → h.addrOf kTerm = vcm.symAddr n
       | .jmp l => nextLabel? = some l → h.addrOf kTerm = vcm.symAddr l
       | .jcc _ _ f | .jnzGpr _ _ f => nextLabel? = some f → h.addrOf (kTerm + 1) = vcm.symAddr f
       | .call _ retL | .icall _ retL =>
         nextLabel? = some retL ∧ h.addrOf (kTerm + 1) = vcm.symAddr retL
       | .nativeTerm _ => False
       | _ => True)

private theorem instrRel_straight_nextPc {A : Arch} {symAddr : Sym → BitVec 64}
    {np₁ np₂ : BitVec 64} {i : Instr A} {s : MachSt A} {o : InstrOut A}
    (hok : !i.isControl && !i.isNative = true) :
    instrRel A symAddr np₁ i s o ↔ instrRel A symAddr np₂ i s o := by
  cases i <;> simp [Instr.isControl, Instr.isNative] at hok <;> simp [instrRel]

private theorem instrRel_straight_symAddr {A : Arch} {symAddr₁ symAddr₂ : Sym → BitVec 64}
    {np : BitVec 64} {i : Instr A} {s : MachSt A} {o : InstrOut A}
    (hok : !i.isControl && !i.isNative = true) (hSym : ∀ sym, symAddr₁ sym = symAddr₂ sym) :
    instrRel A symAddr₁ np i s o ↔ instrRel A symAddr₂ np i s o := by
  cases i <;> simp [Instr.isControl, Instr.isNative] at hok <;> simp [instrRel, hSym]

private theorem instrRel_straight_det {A : Arch} {symAddr : Sym → BitVec 64} {np : BitVec 64}
    {i : Instr A} {s : MachSt A} {o₁ : InstrOut A}
    (hok : !i.isControl && !i.isNative = true) (h1 : instrRel A symAddr np i s o₁) :
    (∃ s₁, o₁ = .fall s₁) ∧ (∀ o₂, instrRel A symAddr np i s o₂ → o₂ = o₁) := by
  cases i with
  | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _ | test _ _ _
  | clearFlags | setcc _ _ | canonAbi _ _ | symAddr _ _ =>
    dsimp only [instrRel] at h1
    exact ⟨⟨_, h1⟩, fun o₂ h2 => h2.trans h1.symm⟩
  | load _ _ _ _ | slotLd _ _ =>
    dsimp only [instrRel] at h1
    rcases h1 with ⟨v₁, hv₁, ho₁⟩
    refine ⟨⟨_, ho₁⟩, fun o₂ h2 => ?_⟩
    rcases h2 with ⟨v₂, hv₂, ho₂⟩
    have : v₁ = v₂ := Option.some.inj (hv₁.symm.trans hv₂)
    subst this; exact ho₂.trans ho₁.symm
  | store _ _ _ | slotSt _ _ =>
    dsimp only [instrRel] at h1
    rcases h1 with ⟨_, ho₁⟩
    refine ⟨⟨_, ho₁⟩, fun o₂ h2 => h2.2.trans ho₁.symm⟩
  | prologue _ =>
    dsimp only [instrRel] at h1
    cases hkind : A.abi.raKind <;> simp only [hkind] at h1
    · refine ⟨⟨_, h1⟩, fun o₂ h2 => by simp only [instrRel, hkind] at h2; exact h2.trans h1.symm⟩
    · rcases h1 with ⟨_, ho₁⟩
      refine ⟨⟨_, ho₁⟩, fun o₂ h2 => by
        simp only [instrRel, hkind] at h2; exact h2.2.trans ho₁.symm⟩
  | epilogue _ =>
    dsimp only [instrRel] at h1
    cases hkind : A.abi.raKind <;> simp only [hkind] at h1
    · refine ⟨⟨_, h1⟩, fun o₂ h2 => by simp only [instrRel, hkind] at h2; exact h2.trans h1.symm⟩
    · rcases h1 with ⟨ra₁, hra₁, ho₁⟩
      refine ⟨⟨_, ho₁⟩, fun o₂ h2 => ?_⟩
      simp only [instrRel, hkind] at h2
      rcases h2 with ⟨ra₂, hra₂, ho₂⟩
      have : ra₁ = ra₂ := Option.some.inj (hra₁.symm.trans hra₂)
      subst this; exact ho₂.trans ho₁.symm
  | jmp _ | jcc _ _ | jnzGpr _ _ | call _ | icall _ | ret | exitJmp _ | tailJmpR _
  | ijmp _ | native _ =>
    simp [Instr.isControl, Instr.isNative] at hok

private theorem straightLine_execBody_det {A : Arch} {symAddr : Sym → BitVec 64} :
    ∀ {is : List (Instr A)} {s : MachSt A} {o₁ o₂ : InstrOut A},
      (∀ i ∈ is, !i.isControl && !i.isNative = true) →
      ExecBody A symAddr is s o₁ → ExecBody A symAddr is s o₂ →
      (∃ s₁, o₁ = .fall s₁) ∧ o₂ = o₁
  | [], _, _, _, _, .nil, .nil => ⟨⟨_, rfl⟩, rfl⟩
  | i :: _, _, _, _, hok, .cons_fall hr₁ hex₁, h2 => by
    have hi := hok i List.mem_cons_self
    have hrest := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    cases h2 with
    | cons_fall hr₂ hex₂ =>
      have heq := (instrRel_straight_det hi hr₁).2 (.fall _) hr₂
      cases heq
      exact straightLine_execBody_det hrest hex₁ hex₂
    | cons_jump hr₂ =>
      have := (instrRel_straight_det hi hr₁).2 (.jump _ _) hr₂; cases this
    | cons_halt hr₂ =>
      have := (instrRel_straight_det hi hr₁).2 (.halt _ _) hr₂; cases this
  | i :: _, _, _, _, hok, .cons_jump hr₁, _ => by
    obtain ⟨⟨_, hf⟩, _⟩ := instrRel_straight_det (hok i List.mem_cons_self) hr₁; cases hf
  | i :: _, _, _, _, hok, .cons_halt hr₁, _ => by
    obtain ⟨⟨_, hf⟩, _⟩ := instrRel_straight_det (hok i List.mem_cons_self) hr₁; cases hf

private theorem straightLine_run_of_body {A : Arch} {h : VllHost A} {symAddr : Sym → BitVec 64}
    {post : Config A → Prop} (hSym : ∀ sym, h.labelAddr sym = symAddr sym) :
    ∀ (is : List (Instr A)) (k : Nat) (s : MachSt A),
      (∀ i ∈ is, !i.isControl && !i.isNative = true) →
      is.IsInfixAt h.prog k →
      (∃ o, ExecBody A symAddr is s o) →
      (∀ s₁, ExecBody A symAddr is s (.fall s₁) →
        (vllMach A).Run h (k + is.length) s₁ post) →
      (vllMach A).Run h k s post
  | [], k, s, _, _, _, hCont => by
    simpa only [List.length_nil, Nat.add_zero] using hCont s .nil
  | i :: is, k, s, hok, hinf, ⟨o₀, ho₀⟩, hCont => by
    obtain ⟨hk, hinf'⟩ := List.IsInfixAt.cons hinf
    have hi := hok i List.mem_cons_self
    have hrest := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    cases ho₀ with
    | cons_jump hr =>
      obtain ⟨⟨_, hf⟩, _⟩ := instrRel_straight_det hi hr; cases hf
    | cons_halt hr =>
      obtain ⟨⟨_, hf⟩, _⟩ := instrRel_straight_det hi hr; cases hf
    | cons_fall hr hEx =>
      rename_i sMid
      have hrH : instrRel A h.labelAddr (h.addrOf (k + 1)) i s (.fall sMid) :=
        (instrRel_straight_symAddr hi hSym).mpr ((instrRel_straight_nextPc hi).mpr hr)
      refine step_cps (vllStep h) post ⟨s, h.addrOf k⟩ ⟨k, i, hk, rfl, ⟨.fall sMid, hrH⟩,
        fun s₁ hr₁ => ?_, fun pc' s' hr₁ => ?_, fun c s' hr₁ => ?_⟩
      · have heq := (instrRel_straight_det hi hrH).2 (.fall s₁) hr₁
        cases heq
        refine straightLine_run_of_body hSym is (k + 1) sMid hrest hinf' ⟨_, hEx⟩
          fun sEnd hExEnd => ?_
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 is.length] using
          hCont sEnd (.cons_fall hr hExEnd)
      · exact False.elim (by cases (instrRel_straight_det hi hrH).2 (.jump pc' s') hr₁)
      · exact False.elim (by cases (instrRel_straight_det hi hrH).2 (.halt c s') hr₁)

private theorem vllHosted_pad_run {A : Arch} {h : VllHost A} {post : Config A → Prop} :
    ∀ (pad? : Option PadKind) (k : Nat) (s : MachSt A),
      ((match pad? with | some pk => [.pad pk] | none => []) : List (Instr A)).IsInfixAt
        h.prog k →
      (vllMach A).Run h (k + (if pad?.isSome then 1 else 0)) s post →
      (vllMach A).Run h k s post
  | none, k, s, _, hCont => by
    simpa only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using hCont
  | some pk, k, s, hinf, hCont => by
    have hk := List.isInfixAt_singleton.mp hinf
    refine step_cps (vllStep h) post ⟨s, h.addrOf k⟩
      ⟨k, .pad pk, hk, rfl, ⟨.fall s, rfl⟩, ?_, ?_, ?_⟩
    · intro s₁ hr; try dsimp only [instrRel] at hr
      cases hr; exact hCont
    · intro _ _ hr; try dsimp only [instrRel] at hr
      cases hr
    · intro _ _ hr; try dsimp only [instrRel] at hr
      cases hr

private theorem vllHosted_term_run {A : Arch} {vcm : VllCodeMap A} {h : VllHost A}
    (hh : vcm.Hosted h) {H_L1 : Xcap.Halt (MachSt A)} {post : Config A → Prop}
    (hHalt : ∀ b ∈ vcm.blocks, ∀ r k nextLabel? s₁,
      b.term = .halt r →
      h.addrOf k = vcm.symAddr b.label →
      (b.toInstrs nextLabel?).IsInfixAt h.prog k →
      H_L1 (s₁.gpr r) s₁ →
      post ⟨s₁, h.addrOf (k + 1 + (if b.pad?.isSome then 1 else 0) + b.body.length)⟩)
    {b : Block A} (hb : b ∈ vcm.blocks) (k : Nat) (nextLabel? : Option Sym)
    (hkLabel : h.addrOf k = vcm.symAddr b.label)
    (hinfBlock : (b.toInstrs nextLabel?).IsInfixAt h.prog k)
    (kTerm : Nat) (hkTerm : kTerm = k + 1 + (if b.pad?.isSome then 1 else 0) + b.body.length)
    (hinfTerm : (b.term.toInstrs nextLabel?).IsInfixAt h.prog kTerm)
    (hTermProp : match b.term with
      | .fall n => nextLabel? = some n → h.addrOf kTerm = vcm.symAddr n
      | .jmp l => nextLabel? = some l → h.addrOf kTerm = vcm.symAddr l
      | .jcc _ _ f | .jnzGpr _ _ f => nextLabel? = some f → h.addrOf (kTerm + 1) = vcm.symAddr f
      | .call _ retL | .icall _ retL =>
        nextLabel? = some retL ∧ h.addrOf (kTerm + 1) = vcm.symAddr retL
      | .nativeTerm _ => False
      | _ => True)
    {s₁ : MachSt A}
    (htWp : termWp A vcm.symAddr b.term (fun pc' s' => Eventually (vllStep h) post ⟨s', pc'⟩)
      H_L1 s₁) :
    (vllMach A).Run h kTerm s₁ post := by
  have hSym := hh.labelAddr_eq
  cases ht : b.term with
  | fall n =>
    rw [ht] at hinfTerm hTermProp htWp
    by_cases hnext : nextLabel? = some n
    · have hpc := hTermProp hnext
      change Eventually (vllStep h) post ⟨s₁, h.addrOf kTerm⟩
      rw [hpc]; exact htWp.2.1 (vcm.symAddr n) s₁ rfl
    · have hbf : (nextLabel? == some n) = false := beq_false_of_ne hnext
      simp only [Term.toInstrs, hbf, Bool.false_eq_true, ↓reduceIte] at hinfTerm
      exact step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩
        ⟨kTerm, .jmp n, List.isInfixAt_singleton.mp hinfTerm, rfl, ⟨.jump (h.labelAddr n) s₁, rfl⟩,
          (fun _ hr => by cases hr),
          (fun pc' s' hr => by cases hr; rw [hSym n]; exact htWp.2.1 (vcm.symAddr n) s₁ rfl),
          (fun _ _ hr => by cases hr)⟩
  | jmp l =>
    rw [ht] at hinfTerm hTermProp htWp
    by_cases hnext : nextLabel? = some l
    · have hpc := hTermProp hnext
      change Eventually (vllStep h) post ⟨s₁, h.addrOf kTerm⟩
      rw [hpc]; exact htWp.2.1 (vcm.symAddr l) s₁ rfl
    · have hbf : (nextLabel? == some l) = false := beq_false_of_ne hnext
      simp only [Term.toInstrs, hbf, Bool.false_eq_true, ↓reduceIte] at hinfTerm
      exact step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩
        ⟨kTerm, .jmp l, List.isInfixAt_singleton.mp hinfTerm, rfl, ⟨.jump (h.labelAddr l) s₁, rfl⟩,
          (fun _ hr => by cases hr),
          (fun pc' s' hr => by cases hr; rw [hSym l]; exact htWp.2.1 (vcm.symAddr l) s₁ rfl),
          (fun _ _ hr => by cases hr)⟩
  | jcc c t f =>
    rw [ht] at hinfTerm hTermProp htWp
    dsimp only [Term.toInstrs] at hinfTerm
    obtain ⟨hkJcc, hinfTail⟩ := List.IsInfixAt.cons hinfTerm
    have hTaken := htWp.2.1 (vcm.symAddr t) s₁
    have hFall := htWp.2.1 (vcm.symAddr f) s₁
    cases hev : A.evalCond s₁.flags c
    · refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .jcc c t, hkJcc, rfl,
        ⟨.fall s₁, by simp [instrRel, hev]⟩,
        fun s' hr => ?_, fun _ _ hr => by simp [instrRel, hev] at hr,
        fun _ _ hr => by simp [instrRel, hev] at hr⟩
      simp only [instrRel, hev, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hr
      subst s'
      have hfWp : Eventually (vllStep h) post ⟨s₁, vcm.symAddr f⟩ :=
        hFall (by simp [termExec, hev])
      by_cases hnext : nextLabel? = some f
      · have hpc := hTermProp hnext
        change Eventually (vllStep h) post ⟨s₁, h.addrOf (kTerm + 1)⟩
        rw [hpc]; exact hfWp
      · have hbf : (nextLabel? == some f) = false := beq_false_of_ne hnext
        simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hinfTail
        exact step_cps (vllStep h) post ⟨s₁, h.addrOf (kTerm + 1)⟩
          ⟨kTerm + 1, .jmp f, List.isInfixAt_singleton.mp hinfTail, rfl,
            ⟨.jump (h.labelAddr f) s₁, rfl⟩,
            (fun _ hr => by cases hr),
            (fun pc' s' hr => by cases hr; rw [hSym f]; exact hfWp),
            (fun _ _ hr => by cases hr)⟩
    · refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .jcc c t, hkJcc, rfl,
        ⟨.jump (h.labelAddr t) s₁, by simp [instrRel, hev]⟩,
        fun _ hr => by simp [instrRel, hev] at hr,
        fun pc' s' hr => ?_, fun _ _ hr => by simp [instrRel, hev] at hr⟩
      simp only [instrRel, hev, ↓reduceIte, InstrOut.jump.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rw [hSym t]
      exact hTaken (by simp [termExec, hev])
  | jnzGpr r t f =>
    rw [ht] at hinfTerm hTermProp htWp
    dsimp only [Term.toInstrs] at hinfTerm
    obtain ⟨hkJnz, hinfTail⟩ := List.IsInfixAt.cons hinfTerm
    let s₂ := s₁.setFlags (A.jnzGprFlags (s₁.gpr r) s₁.flags)
    cases hnz : ((s₁.gpr r).setWidth 8 != 0#8)
    · refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .jnzGpr r t, hkJnz, rfl,
        ⟨.fall s₂, by simp [instrRel, hnz, s₂]⟩,
        fun s' hr => ?_, fun _ _ hr => by simp [instrRel, hnz] at hr,
        fun _ _ hr => by simp [instrRel, hnz] at hr⟩
      simp only [instrRel, hnz, Bool.false_eq_true, ↓reduceIte, InstrOut.fall.injEq] at hr
      subst s'
      have hfWp : Eventually (vllStep h) post ⟨s₂, vcm.symAddr f⟩ :=
        htWp.2.1 (vcm.symAddr f) s₂ (by simp [termExec, hnz, s₂])
      by_cases hnext : nextLabel? = some f
      · have hpc := hTermProp hnext
        change Eventually (vllStep h) post ⟨s₂, h.addrOf (kTerm + 1)⟩
        rw [hpc]; exact hfWp
      · have hbf : (nextLabel? == some f) = false := beq_false_of_ne hnext
        simp only [hbf, Bool.false_eq_true, ↓reduceIte] at hinfTail
        exact step_cps (vllStep h) post ⟨s₂, h.addrOf (kTerm + 1)⟩
          ⟨kTerm + 1, .jmp f, List.isInfixAt_singleton.mp hinfTail, rfl,
            ⟨.jump (h.labelAddr f) s₂, rfl⟩,
            (fun _ hr => by cases hr),
            (fun pc' s' hr => by cases hr; rw [hSym f]; exact hfWp),
            (fun _ _ hr => by cases hr)⟩
    · refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .jnzGpr r t, hkJnz, rfl,
        ⟨.jump (h.labelAddr t) s₂, by simp [instrRel, hnz, s₂]⟩,
        fun _ hr => by simp [instrRel, hnz] at hr,
        fun pc' s' hr => ?_, fun _ _ hr => by simp [instrRel, hnz] at hr⟩
      simp only [instrRel, hnz, ↓reduceIte, InstrOut.jump.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      rw [hSym t]
      exact htWp.2.1 (vcm.symAddr t) s₂ (by simp [termExec, hnz, s₂])
  | call sym retL =>
    rw [ht] at hinfTerm hTermProp htWp
    obtain ⟨rfl, hkNext⟩ := hTermProp
    simp only [Term.toInstrs, beq_self_eq_true, ↓reduceIte] at hinfTerm
    have hkCall : h.prog[kTerm]? = some (.call sym) := List.isInfixAt_singleton.mp hinfTerm
    cases hkind : A.abi.raKind with
    | linkReg lr =>
      have hCallOut := htWp.2.1 (vcm.symAddr sym) (s₁.setGpr lr (vcm.symAddr retL))
        (by simp [termExec, hkind])
      refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .call sym, hkCall, rfl,
        ⟨.jump (h.labelAddr sym) (s₁.setGpr lr (h.addrOf (kTerm + 1))),
          by simp [instrRel, hkind]⟩,
        fun _ hr => by simp [instrRel, hkind] at hr,
        fun pc' s' hr => ?_, fun _ _ hr => by simp [instrRel, hkind] at hr⟩
      simp only [instrRel, hkind, InstrOut.jump.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      rw [hSym sym, hkNext]; exact hCallOut
    | stack =>
      have hst : storeOk s₁.mem i64 (s₁.gpr A.abi.sp - 8#64) := by
        obtain ⟨o₀, ho₀⟩ := htWp.1
        simp only [termExec, hkind] at ho₀
        exact ho₀.1
      let s₂ := (s₁.setGpr A.abi.sp (s₁.gpr A.abi.sp - 8#64)).setMem
        (storeMem s₁.mem i64 (s₁.gpr A.abi.sp - 8#64) (vcm.symAddr retL))
      have hCallOut := htWp.2.1 (vcm.symAddr sym) s₂ (by simp [termExec, hkind, hst, s₂])
      refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .call sym, hkCall, rfl,
        ⟨.jump (h.labelAddr sym)
          ((s₁.setGpr A.abi.sp (s₁.gpr A.abi.sp - 8#64)).setMem
            (storeMem s₁.mem i64 (s₁.gpr A.abi.sp - 8#64) (h.addrOf (kTerm + 1)))),
          by simp [instrRel, hkind, hst]⟩,
        fun _ hr => by simp [instrRel, hkind] at hr,
        fun pc' s' hr => ?_, fun _ _ hr => by simp [instrRel, hkind] at hr⟩
      simp only [instrRel, hkind, InstrOut.jump.injEq] at hr
      rcases hr with ⟨_, rfl, rfl⟩
      rw [hSym sym, hkNext]; exact hCallOut
  | icall r retL =>
    rw [ht] at hinfTerm hTermProp htWp
    obtain ⟨rfl, hkNext⟩ := hTermProp
    simp only [Term.toInstrs, beq_self_eq_true, ↓reduceIte] at hinfTerm
    have hkIcall : h.prog[kTerm]? = some (.icall r) := List.isInfixAt_singleton.mp hinfTerm
    cases hkind : A.abi.raKind with
    | linkReg lr =>
      have hCallOut := htWp.2.1 (s₁.gpr r) (s₁.setGpr lr (vcm.symAddr retL))
        (by simp [termExec, hkind])
      refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .icall r, hkIcall, rfl,
        ⟨.jump (s₁.gpr r) (s₁.setGpr lr (h.addrOf (kTerm + 1))), by simp [instrRel, hkind]⟩,
        fun _ hr => by simp [instrRel, hkind] at hr,
        fun pc' s' hr => ?_, fun _ _ hr => by simp [instrRel, hkind] at hr⟩
      simp only [instrRel, hkind, InstrOut.jump.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩
      rw [hkNext]; exact hCallOut
    | stack =>
      have hst : storeOk s₁.mem i64 (s₁.gpr A.abi.sp - 8#64) := by
        obtain ⟨o₀, ho₀⟩ := htWp.1
        simp only [termExec, hkind] at ho₀
        exact ho₀.1
      let s₂ := (s₁.setGpr A.abi.sp (s₁.gpr A.abi.sp - 8#64)).setMem
        (storeMem s₁.mem i64 (s₁.gpr A.abi.sp - 8#64) (vcm.symAddr retL))
      have hCallOut := htWp.2.1 (s₁.gpr r) s₂ (by simp [termExec, hkind, hst, s₂])
      refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .icall r, hkIcall, rfl,
        ⟨.jump (s₁.gpr r)
          ((s₁.setGpr A.abi.sp (s₁.gpr A.abi.sp - 8#64)).setMem
            (storeMem s₁.mem i64 (s₁.gpr A.abi.sp - 8#64) (h.addrOf (kTerm + 1)))),
          by simp [instrRel, hkind, hst]⟩,
        fun _ hr => by simp [instrRel, hkind] at hr,
        fun pc' s' hr => ?_, fun _ _ hr => by simp [instrRel, hkind] at hr⟩
      simp only [instrRel, hkind, InstrOut.jump.injEq] at hr
      rcases hr with ⟨_, rfl, rfl⟩
      rw [hkNext]; exact hCallOut
  | ret =>
    rw [ht] at hinfTerm htWp
    have hkRet : h.prog[kTerm]? = some .ret :=
      List.isInfixAt_singleton.mp (by simpa [Term.toInstrs] using hinfTerm)
    cases hkind : A.abi.raKind with
    | linkReg lr =>
      have hRetOut := htWp.2.1 (s₁.gpr lr) s₁ (by simp [termExec, hkind])
      refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .ret, hkRet, rfl,
        ⟨.jump (s₁.gpr lr) s₁, by simp [instrRel, hkind]⟩,
        fun _ hr => by simp [instrRel, hkind] at hr,
        fun pc' s' hr => by
          simp only [instrRel, hkind, InstrOut.jump.injEq] at hr
          rcases hr with ⟨rfl, rfl⟩; exact hRetOut,
        fun _ _ hr => by simp [instrRel, hkind] at hr⟩
    | stack =>
      have hExists : ∃ ra : BitVec 64, loadVal s₁.mem i64 (s₁.gpr A.abi.sp) = some ra := by
        obtain ⟨o₀, ho₀⟩ := htWp.1
        simp only [termExec, hkind] at ho₀
        exact ⟨ho₀.choose, ho₀.choose_spec.1⟩
      obtain ⟨ra, hra⟩ := hExists
      have hRetOut := htWp.2.1 ra (s₁.setGpr A.abi.sp (s₁.gpr A.abi.sp + 8#64))
        (by simp [termExec, hkind, hra])
      refine step_cps (vllStep h) post ⟨s₁, h.addrOf kTerm⟩ ⟨kTerm, .ret, hkRet, rfl,
        ⟨.jump ra (s₁.setGpr A.abi.sp (s₁.gpr A.abi.sp + 8#64)),
          by simp [instrRel, hkind, hra]⟩,
        fun _ hr => by simp [instrRel, hkind] at hr,
        fun pc' s' hr => by
          simp only [instrRel, hkind, hra, Option.some.injEq, exists_eq_left',
            InstrOut.jump.injEq] at hr
          rcases hr with ⟨rfl, rfl⟩; exact hRetOut,
        fun _ _ hr => by simp [instrRel, hkind] at hr⟩
  | exitJmp sym =>
    rw [ht] at hinfTerm htWp
    exact vllMach_exitJmp_spec hinfTerm (by rw [hSym sym]; exact htWp.2.1 (vcm.symAddr sym) s₁ rfl)
  | tailJmpR r =>
    rw [ht] at hinfTerm htWp
    exact vllMach_tailJmpR_spec hinfTerm (htWp.2.1 (s₁.gpr r) s₁ rfl)
  | ijmp r =>
    rw [ht] at hinfTerm htWp
    exact vllMach_ijmp_spec hinfTerm (htWp.2.1 (s₁.gpr r) s₁ rfl)
  | halt r =>
    rw [ht] at htWp
    have hH : H_L1 (s₁.gpr r) s₁ := htWp.2.2 (s₁.gpr r) s₁ rfl
    exact Eventually.done _ (hkTerm ▸ hHalt b hb r k nextLabel? s₁ ht hkLabel hinfBlock hH)
  | nativeTerm d =>
    rw [ht] at hTermProp
    exact False.elim hTermProp

/-- Any hosted `VllCodeMap A` satisfies `Xcap.Closed` for small-step `Eventually (vllStep h)
post` (terminating cleanly at halt block ends via `hHalt`). -/
theorem vllHosted_closed {A : Arch} {vcm : VllCodeMap A} {h : VllHost A}
    (hh : vcm.Hosted h) {H_L1 : Xcap.Halt (MachSt A)} {post : Config A → Prop}
    (hHalt : ∀ b ∈ vcm.blocks, ∀ r k nextLabel? s₁,
      b.term = .halt r →
      h.addrOf k = vcm.symAddr b.label →
      (b.toInstrs nextLabel?).IsInfixAt h.prog k →
      H_L1 (s₁.gpr r) s₁ →
      post ⟨s₁, h.addrOf (k + 1 + (if b.pad?.isSome then 1 else 0) + b.body.length)⟩) :
    Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode
      (fun pc s => Eventually (vllStep h) post ⟨s, pc⟩) H_L1 := by
  intro pc b hlu s hbwp
  obtain ⟨hbMem, hpcEq⟩ := VllCodeMap.lookupPc_mem hlu
  obtain ⟨hBodyOk, k, nextLabel?, hkAddr, hinfBlock, hTermProp⟩ := hh.blocks_ok b hbMem
  have hinfFull := hinfBlock
  dsimp only [Block.toInstrs] at hinfBlock
  obtain ⟨hkLbl, hinfRest⟩ := List.IsInfixAt.cons hinfBlock
  obtain ⟨hinfPadBody, hinfTerm0⟩ := List.IsInfixAt.append hinfRest
  obtain ⟨hinfPad, hinfBody0⟩ := List.IsInfixAt.append hinfPadBody
  have hinfBody : b.body.IsInfixAt h.prog (k + 1 + (if b.pad?.isSome then 1 else 0)) := by
    have hEqB : k + 1 + (match b.pad? with
        | some pk => ([.pad pk] : List (Instr A)) | none => []).length =
        k + 1 + (if b.pad?.isSome then 1 else 0) := by
      cases b.pad? <;> rfl
    exact hEqB ▸ hinfBody0
  have hinfTerm : (b.term.toInstrs nextLabel?).IsInfixAt h.prog
      (k + 1 + (if b.pad?.isSome then 1 else 0) + b.body.length) := by
    have hEqT : k + 1 + ((match b.pad? with
        | some pk => ([.pad pk] : List (Instr A)) | none => []).append b.body).length =
        k + 1 + (if b.pad?.isSome then 1 else 0) + b.body.length := by
      cases b.pad? <;> simp <;> omega
    exact hEqT ▸ hinfTerm0
  have hexBody : ∃ o, ExecBody A vcm.symAddr b.body s o := by
    obtain ⟨o₀, ho₀⟩ := hbwp.1
    cases ho₀ with
    | fall hex _ => exact ⟨_, hex⟩
    | earlyJump hex => exact ⟨_, hex⟩
    | earlyHalt hex => exact ⟨_, hex⟩
  rw [← hpcEq, ← hkAddr]
  refine step_cps (vllStep h) post ⟨s, h.addrOf k⟩
    ⟨k, .label b.label, hkLbl, rfl, ⟨.fall s, rfl⟩, ?_, ?_, ?_⟩
  · intro s' hr
    try dsimp only [instrRel] at hr
    cases hr
    refine vllHosted_pad_run b.pad? (k + 1) s hinfPad ?_
    refine straightLine_run_of_body hh.labelAddr_eq b.body
      (k + 1 + (if b.pad?.isSome then 1 else 0)) s hBodyOk hinfBody hexBody fun s₁ hex₁ => ?_
    have htEx : ∃ ot, termExec A vcm.symAddr b.term s₁ ot := by
      obtain ⟨o₀, ho₀⟩ := hbwp.1
      cases ho₀ with
      | fall hex₀ ht₀ =>
        have heq := (straightLine_execBody_det hBodyOk hex₁ hex₀).2
        cases heq; exact ⟨o₀, ht₀⟩
      | earlyJump hex₀ =>
        obtain ⟨⟨_, hf⟩, _⟩ := straightLine_execBody_det hBodyOk hex₀ hex₁
        cases hf
      | earlyHalt hex₀ =>
        obtain ⟨⟨_, hf⟩, _⟩ := straightLine_execBody_det hBodyOk hex₀ hex₁
        cases hf
    have htWp : termWp A vcm.symAddr b.term
        (fun pc' s' => Eventually (vllStep h) post ⟨s', pc'⟩) H_L1 s₁ :=
      ⟨htEx, fun pc' s' hte => hbwp.2.1 pc' s' (.fall hex₁ hte),
        fun c s' hte => hbwp.2.2 c s' (.fall hex₁ hte)⟩
    exact vllHosted_term_run hh hHalt hbMem k nextLabel? hkAddr hinfFull
      (k + 1 + (if b.pad?.isSome then 1 else 0) + b.body.length) rfl hinfTerm hTermProp htWp
  · intro _ _ hr; try dsimp only [instrRel] at hr
    cases hr
  · intro _ _ hr; try dsimp only [instrRel] at hr
    cases hr

/-- Non-halting specialization of `vllHosted_closed` (`H_L1 := fun _ _ => False`). -/
theorem vllHosted_closed_noHalt {A : Arch} {vcm : VllCodeMap A} {h : VllHost A}
    (hh : vcm.Hosted h) (post : Config A → Prop) :
    Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode
      (fun pc s => Eventually (vllStep h) post ⟨s, pc⟩) (fun _ _ => False) :=
  vllHosted_closed hh (fun _ _ _ _ _ _ _ _ _ hFalse => False.elim hFalse)

/-- Hosted `vllStep` small-step execution corollary for `fromWord` (`fromWord_cptr_sound` +
`vllHosted_closed`). -/
theorem fromWord_hosted_vllStep {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} {h : VllHost A}
    (hfw : fromWord b cm = .ok vcm) (hh : vcm.Hosted h)
    {H_L0 : HaltPost} {R : Mem 64 → Prop} {pc : BitVec 64} {st : BedrockWord.State}
    (hwp : cm.wp H_L0 pc st) {s : MachSt A} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel b st (codeMapMaxBudget b cm) R s)
    (hanc : codeMapMaxBudget b cm > 0 → (vllFramePreds A).raReg s ra0 ∧
      (s.mem =⋆ Eq st.mem ⋆
        hwStackMem A (s.gpr A.abi.sp) ra0 (codeMapMaxBudget b cm) ⋆ R))
    {post : Config A → Prop}
    (hHalt : ∀ blk ∈ vcm.blocks, ∀ r k nextLabel? s₁,
      blk.term = .halt r →
      h.addrOf k = vcm.symAddr blk.label →
      (blk.toInstrs nextLabel?).IsInfixAt h.prog k →
      plainHaltPost A H_L0 (s.gpr A.abi.sp) ra0 (codeMapMaxBudget b cm) R (s₁.gpr r) s₁ →
      post ⟨s₁, h.addrOf (k + 1 + (if blk.pad?.isSome then 1 else 0) + blk.body.length)⟩) :
    Eventually (vllStep h) post ⟨s, pc⟩ :=
  fromWord_wp_sound hawf hwf hfw hwp hrel hanc
    (fun pc' s' => Eventually (vllStep h) post ⟨s', pc'⟩) (vllHosted_closed hh hHalt)

/-- Hosted `vllStep` small-step execution corollary for closed `fromWordContify`
(`fromWordContify_wp_sound` + `vllHosted_closed`). -/
theorem fromWordContify_hosted_vllStep {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A} {h : VllHost A}
    (hfc : fromWordContify b cm wit = .ok vcm) (hh : vcm.Hosted h)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    (hNoRes : residualContifyCodeMap cm wit = [])
    (hNoDyn : ∀ cr' ∈ wit.regions, cr'.abi = .retEnvelope →
      cr'.privFrame.dynAliasGuard = false ∨ cr'.privFrame.numSlots = 0)
    (hNoOpenEdge : ∀ cr' ∈ wit.regions, cr'.abi = .retEnvelope → ∀ ew ∈ cr'.edges,
      match ew.kind with | .bailout | .guarded _ | .strideTable _ _ true => False | _ => True)
    {H_L0 : HaltPost} {R : Mem 64 → Prop} {cr : ContifyRegion}
    (hcr : cr ∈ wit.regions) (habi : cr.abi = .retEnvelope)
    {st : BedrockWord.State} (hwp : cm.wp H_L0 cr.entryPc st)
    {s : MachSt A} {ra0 : BitVec 64}
    (hrel : WordPlainEntryRel b st budget R s)
    (hanc : budget > 0 → (vllFramePreds A).raReg s ra0 ∧
      (s.mem =⋆ Eq st.mem ⋆ hwStackMem A (s.gpr A.abi.sp) ra0 budget ⋆ R))
    (hPriv : cr.privFrame.numSlots > 0 →
      st.regs.sp = s.gpr A.abi.sp ∧ cr.privFrame.numSlots ≤ 64 ∧
      ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k))
    {post : Config A → Prop}
    (hHalt : ∀ blk ∈ vcm.blocks, ∀ r k nextLabel? s₁,
      blk.term = .halt r →
      h.addrOf k = vcm.symAddr blk.label →
      (blk.toInstrs nextLabel?).IsInfixAt h.prog k →
      wordHaltPost A H_L0 (if budget = 0 then R
        else region (s.gpr A.abi.sp - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R)
        (s₁.gpr r) s₁ →
      post ⟨s₁, h.addrOf (k + 1 + (if blk.pad?.isSome then 1 else 0) + blk.body.length)⟩) :
    Eventually (vllStep h) post ⟨s, cr.entryPc⟩ :=
  fromWordContify_wp_sound hawf hwf hfc hSymAgree hBudReg hBudRes hNoRes hNoDyn hNoOpenEdge
    hcr habi hwp hrel hanc hPriv
    (fun pc' s' => Eventually (vllStep h) post ⟨s', pc'⟩) (vllHosted_closed hh hHalt)

/-- Hosted `vllStep` small-step execution corollary for modular `.contified` `vllCallPre`. -/
theorem contified_hosted_vllStep {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A} {h : VllHost A}
    (hfc : fromWordContify b cm wit = .ok vcm) (hh : vcm.Hosted h)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {pre : List ContifyRegion} {cr : ContifyRegion} {post : List ContifyRegion}
    (hSplit : wit.regions = pre ++ cr :: post) {dualRet : Bool}
    (habi : cr.abi = .contified dualRet)
    {cb : Nat} (hCb : regionStackBudget b cm wit cr ≤ cb)
    (hbd : cb + A.abi.raBytes ≤ 2 ^ 64)
    {H_L0 : HaltPost} {postCfg : Config A → Prop} {H_L1 : Xcap.Halt (MachSt A)}
    (hHaltBlk : ∀ blk ∈ vcm.blocks, ∀ r k nextLabel? s₁,
      blk.term = .halt r →
      h.addrOf k = vcm.symAddr blk.label →
      (blk.toInstrs nextLabel?).IsInfixAt h.prog k →
      H_L1 (s₁.gpr r) s₁ →
      postCfg ⟨s₁, h.addrOf (k + 1 + (if blk.pad?.isSome then 1 else 0) + blk.body.length)⟩)
    (sp_c : BitVec 64) (R_c : Mem 64 → Prop) (st₀ : BedrockWord.State)
    (Post_L0 : Bool → BedrockWord.State → Prop)
    (hHalt : regionMemFree cm (pre.foldl (fun a r =>
        match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = false →
      ∀ c s', wordHaltPost A H_L0 (region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c)
        c s' → H_L1 c s')
    (hsp0 : regionMemFree cm (pre.foldl (fun a r =>
        match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
      st₀.regs.sp = sp_c)
    (hrpDisj : st₀.regs.rp ∉ cr.allPcs ∧ (dualRet = true → st₀.regs.rp + 8#64 ∉ cr.allPcs))
    (hL0 : ∀ (Ψ_L0 : BedrockWord.CodeSpec),
      (∀ pc blk, pc ∈ cr.allPcs → cm.lookupAddr pc = some blk →
        ∀ st', blk.wp cm.symEnv Ψ_L0 H_L0 (pushRegsV st'.regs.toRegsV) st'.mem → Ψ_L0 pc st') →
      (∀ isAlt st', (isAlt = true → dualRet = true) →
        (regionMemFree cm (pre.foldl (fun a r =>
            match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
          st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) →
        Post_L0 isAlt st' →
        Ψ_L0 (st₀.regs.rp + (if isAlt then 8#64 else 0#64)) st') →
      Ψ_L0 cr.entryPc st₀) :
    Xcap.cptr (fun pc s => Eventually (vllStep h) postCfg ⟨s, pc⟩) (vcm.symAddr cr.name)
      (vllCallPre A
        (fun s => s.gpr A.abi.sp = sp_c ∧ WordRegsRel b st₀.regs s ∧
          ∃ ra₀, (vllFramePreds A).raReg s ra₀ ∧
            (s.mem =⋆
              (if regionMemFree cm (pre.foldl (fun a r =>
                match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr
                then emp else Eq st₀.mem) ⋆
              hwStackMem A sp_c ra₀ cb ⋆ R_c))
        (fun s' => ∃ (isAlt : Bool) (st' : BedrockWord.State),
          (isAlt = true → dualRet = true) ∧
          (regionMemFree cm (pre.foldl (fun a r =>
              match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr = true →
            st'.mem = st₀.mem ∧ st'.regs.sp = sp_c) ∧
          Post_L0 isAlt st' ∧
          WordRegsRel b st'.regs s' ∧
          (dualRet = true → ValHolds64 .bool isAlt (s'.gpr b.altRet)) ∧
          s'.gpr A.abi.sp = sp_c + BitVec.ofNat 64 A.abi.raBytes ∧
          (s'.mem =⋆
            (if regionMemFree cm (pre.foldl (fun a r =>
              match r.toCalleeMeta? cm a with | some c => c :: a | none => a) []) cr
              then emp else Eq st'.mem) ⋆
            region (sp_c - BitVec.ofNat 64 cb) (cb + A.abi.raBytes) ⋆ R_c))
        (fun pc s => Eventually (vllStep h) postCfg ⟨s, pc⟩)) :=
  contified_open_cptr_spec hawf hwf hfc hSymAgree hSplit habi hCb hbd
    (vllHosted_closed hh hHaltBlk) sp_c R_c st₀ Post_L0 hHalt hsp0 hrpDisj hL0

/-- Lift any SSA-compiled `Target.FnSpec` callee via `Xcap.Bridge.fnSpec_to_cptr` into an
external `Xcap.cptr` hypothesis compatible with `Vll` (`fromWord_open_cptr_sound` /
`fromWordContify_open_cptr_sound`). -/
theorem target_fnSpec_to_vll_entry {A : Arch} {T : Target} (C : Xcap.AddrCodec T)
    {host : T.mach.Host} {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hfn : T.FnSpec host sym spec n nX)
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)}
    {Ψ_T : Xcap.CodeSpec T.mach.MData} {H_T : T.mach.State → Prop}
    (hclT : Xcap.TargetClosed T C host Ψ_T H_T)
    {pc : BitVec 64} (hpc : pc = C.toBits (T.mach.labelAddr host sym))
    {P : MachSt A → Prop}
    (hliftPre : ∀ s, P s → ∃ d : T.mach.MData,
      Xcap.targetCallPre T C host spec n nX Ψ_T d ∧ (Ψ_T pc d → Ψ_L1 pc s)) :
    Xcap.cptr Ψ_L1 pc P := by
  intro s hs
  obtain ⟨d, hpre, hback⟩ := hliftPre s hs
  have hcptr := Xcap.fnSpec_to_cptr C hfn hclT
  rw [← hpc] at hcptr
  exact hback (hcptr d hpre)

/-- Lift any `TargetClosed`-polymorphic `Xcap.cptr` back into a `Target.FnSpec` via
`Xcap.Bridge.cptr_of_targetClosed_to_Γ`. -/
theorem vll_cptr_to_target_fnSpec {T : Target} (C : Xcap.AddrCodec T)
    {host : T.mach.Host} {sym : Sym} {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hcptr : ∀ (Ψ_T : Xcap.CodeSpec T.mach.MData) (H_T : T.mach.State → Prop),
      Xcap.TargetClosed T C host Ψ_T H_T →
      Xcap.cptr Ψ_T (C.toBits (T.mach.labelAddr host sym))
        (Xcap.targetCallPre T C host spec n nX Ψ_T)) :
    T.FnSpec host sym spec n nX :=
  Xcap.cptr_of_targetClosed_to_Γ C hcptr

/-- Open `fromWord` composition directly linking an L0 module (`OpenModOk`) with an
SSA-compiled `Target.FnSpec` external callee via `Xcap.Bridge.fnSpec_to_cptr`. -/
theorem fromWord_open_cptr_with_fnSpec {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {cm : CodeMap} {vcm : VllCodeMap A} (hfw : fromWord b cm = .ok vcm)
    {H_L0 : HaltPost} {SymReq : SymEnv → Prop} {Imp Exp : Nat → BedrockWord.CodeSpec}
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hMod : OpenModOk cm H_L0 SymReq Imp Exp) (hSym : SymReq cm.symEnv)
    (hclL1 : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hHalt : ∀ c s, plainHaltPost A H_L0 sp0 ra0 (codeMapMaxBudget b cm) R c s → H_L1 c s)
    {T : Target} (C : Xcap.AddrCodec T) {host : T.mach.Host} {sym : Sym}
    {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hfn : T.FnSpec host sym spec n nX)
    {Ψ_T : Xcap.CodeSpec T.mach.MData} {H_T : T.mach.State → Prop}
    (hclT : Xcap.TargetClosed T C host Ψ_T H_T)
    (hImpBridge : ∀ r pc st s, Imp r pc st →
      WordPlainEntryRel b st (codeMapMaxBudget b cm) R s →
      (codeMapMaxBudget b cm > 0 →
        s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
        (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 (codeMapMaxBudget b cm) ⋆ R)) →
      pc = C.toBits (T.mach.labelAddr host sym) ∧
        ∃ d : T.mach.MData, Xcap.targetCallPre T C host spec n nX Ψ_T d ∧ (Ψ_T pc d → Ψ_L1 pc s)) :
    ∀ r pc st s, Exp r pc st →
      WordPlainEntryRel b st (codeMapMaxBudget b cm) R s →
      (codeMapMaxBudget b cm > 0 →
        s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
        (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 (codeMapMaxBudget b cm) ⋆ R)) →
      Ψ_L1 pc s := by
  refine fromWord_open_cptr_sound hawf hwf hfw hMod hSym hclL1 hHalt ?_
  intro r pc st s hImp hRel hPre
  obtain ⟨hpc, d, hd, hback⟩ := hImpBridge r pc st s hImp hRel hPre
  exact target_fnSpec_to_vll_entry C hfn hclT hpc (P := fun x => x = s)
    (fun _ hs => hs ▸ ⟨d, hd, hback⟩) s rfl

/-- Open `fromWordContify` composition directly linking a Stage-1 contified L0 module with an
SSA-compiled `Target.FnSpec` external callee via `Xcap.Bridge.fnSpec_to_cptr`. -/
theorem fromWordContify_open_cptr_with_fnSpec {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {cm : CodeMap} {wit : ContifyWitness} {vcm : VllCodeMap A}
    (hfc : fromWordContify b cm wit = .ok vcm)
    (hSymAgree : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {budget : Nat}
    (hBudReg : ∀ cr ∈ wit.regions, regionStackBudget b cm wit cr ≤ budget)
    (hBudRes : ∀ e ∈ residualContifyCodeMap cm wit, plainEntryBudget b e.block ≤ budget)
    {sp0 ra0 : BitVec 64} {R : Mem 64 → Prop}
    {H_L0 : HaltPost} {Ψ_L1 : Xcap.CodeSpec (MachSt A)} {H_L1 : Xcap.Halt (MachSt A)}
    (hclL1 : Xcap.Closed (vllXcapMach A vcm.symAddr) vcm.toXcapCode Ψ_L1 H_L1)
    (hHalt : ∀ c s, wordHaltPost A H_L0 (if budget = 0 then R
      else region (sp0 - BitVec.ofNat 64 budget) (budget + A.abi.raBytes) ⋆ R) c s → H_L1 c s)
    {T : Target} (C : Xcap.AddrCodec T) {host : T.mach.Host} {sym : Sym}
    {as bs : List Ty} {spec : Spec as bs} {n nX : Nat}
    (hfn : T.FnSpec host sym spec n nX)
    {Ψ_T : Xcap.CodeSpec T.mach.MData} {H_T : T.mach.State → Prop}
    (hclT : Xcap.TargetClosed T C host Ψ_T H_T)
    (ExtSpec Inv : BedrockWord.CodeSpec)
    (hExtBridge : ∀ tgt st s, ExtSpec tgt st →
      WordPlainEntryRel b st budget R s →
      (budget > 0 → s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
        (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 budget ⋆ R)) →
      tgt = C.toBits (T.mach.labelAddr host sym) ∧
        ∃ d : T.mach.MData, Xcap.targetCallPre T C host spec n nX Ψ_T d ∧ (Ψ_T tgt d → Ψ_L1 tgt s))
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
            ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k))))
    {pc : BitVec 64} {st : BedrockWord.State} {s : MachSt A}
    (hEntry : (∃ e ∈ residualContifyCodeMap cm wit, e.addr = pc) ∨
      (∃ cr ∈ wit.regions, cr.abi = .retEnvelope ∧ cr.entryPc = pc ∧
        (cr.privFrame.numSlots > 0 → st.regs.sp = sp0 ∧ cr.privFrame.numSlots ≤ 64 ∧
          ∀ k < cr.privFrame.numSlots, storeOk st.mem i64 (slotAddr st.regs.sp k))))
    (hInv0 : Inv pc st) (hwp : cm.wp H_L0 pc st)
    (hrel : WordPlainEntryRel b st budget R s)
    (hanc : budget > 0 → s.gpr A.abi.sp = sp0 ∧ (vllFramePreds A).raReg s ra0 ∧
      (s.mem =⋆ Eq st.mem ⋆ hwStackMem A sp0 ra0 budget ⋆ R)) :
    Ψ_L1 pc s := by
  refine fromWordContify_open_cptr_sound hawf hwf hfc hSymAgree hBudReg hBudRes hclL1 hHalt
    ExtSpec Inv ?_ hInvCl hInvValid hEntry hInv0 hwp hrel hanc
  intro tgt st' s' hE hRel hPre
  obtain ⟨hpc, d, hd, hback⟩ := hExtBridge tgt st' s' hE hRel hPre
  exact target_fnSpec_to_vll_entry C hfn hclT hpc (P := fun x => x = s')
    (fun _ hs => hs ▸ ⟨d, hd, hback⟩) s' rfl

end LeanQbe.T.Vll
