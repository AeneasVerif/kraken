module

public import LeanQbe.T.Bootstrap0.Sound0Part9
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.IselLemmas4

/-!
# Bootstrap Stage B (`Sound0Part10`): Machine Runners & `compileFn0_fnSpec`

Proves end-to-end `x64ScalarTarget.FnSpec` semantic soundness for every compiled function
`compileFn0 fnIdx fn` satisfying `WfNode0` and `fn.okGuardsFull = true`:
1. `fnPost0` target postcondition, worklist program-slice splitting, & label/live helpers.
2. Terminator runners (`emitJump0_run_ok`, `stepRet0_run_ok`, `stepTail0_run_ok`) and
   shared straight-line result binder (`stepLinear_bind_ok`).
3. Straight-line & structured control-flow runners (`let1_run_ok`, `umulw_run_ok`,
   `load_run_ok`, `store_run_ok`, `call_run_ok`, `jnz_run_ok`, `group_run_ok`).
4. Inductive soundness `regaTask0_run_ok` and per-function `compileFn0_fnSpec` /
   `compileFn0_defined`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 1. Target Postcondition, Worklist Splitting, & Frame Helpers -/

/-- Exact `Target.FnSpec` postcondition for `x64ScalarTarget` anchored at `(s0, ra0, n, Rf)`. -/
@[expose] def fnPost0 (h : Host) (rs : List Ty0) (Q : Post (ty0ListToTy rs)) (X : XPost)
    (s0 : MachineData) (ra0 : Int64) (n nX : Nat) (Rf : Mem 64 → Prop) :
    MachineState → Prop :=
  fun st =>
    (st.pc = ra0 ∧ ∃ (rets : Tup Val (ty0ListToTy rs)) (m' : Mem 64),
      Q rets m' ∧ x64ScalarTarget.RetsIn rets st.data ∧ x64ScalarTarget.Restored s0 st.data ∧
      (st.data.dmem =⋆ Eq m' ⋆ x64ScalarTarget.Exit (s0.regs.get64 .rsp) n ⋆ Rf)) ∨
    (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
      X sym' cs xs m' ∧ x64ScalarTarget.Defined h sym' ∧ st.pc = hostLabel h sym' ∧
      x64ScalarTarget.ArgsIn xs st.data ∧
      x64ScalarTarget.frameSpec.spEntry (st.data.regs.get64 .rsp) ∧
      ∃ (ra' : Int64) (n' : Nat) (F : Mem 64 → Prop),
        nX ≤ n' ∧ n' + 8 ≤ 2 ^ 64 ∧ x64ScalarTarget.frameSpec.raReg st.data ra' ∧
        (st.data.dmem =⋆ Eq m' ⋆
          x64ScalarTarget.Entry (st.data.regs.get64 .rsp) ra' n' ⋆ F ⋆ Rf))

theorem u32_ofNat_toNat_lt10 {n : Nat} (h : n < 2 ^ 32) :
    (UInt32.ofNat n).toNat = n :=
  u32_ofNat_toNat_lt9 h

theorem workNodeCount0_singleton (t : RegaTask0) :
    workNodeCount0 ([t].map RegaTask0.node) = nodeCount0 t.node := by
  rw [List.map_singleton]; dsimp only [workNodeCount0]; exact Nat.add_zero _

theorem listGet?_eq_getElem10 {α : Type} :
    ∀ (xs : List α) (i : Nat) (hi : i < xs.length), listGet? xs i = some (xs[i]'hi)
  | [], _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: xs, k + 1, hi => listGet?_eq_getElem10 xs k (Nat.lt_of_succ_lt_succ hi)

theorem listNoSpZero0_emitFwd0 {ds : List Dir0} (h : ListNoSpZero0 ds) :
    ListNoSpZero0 (emitFwd0 ds) := by
  dsimp only [emitFwd0]; exact listNoSpZero0_reverse h

theorem regaRunAux0_step_once {fuel : UInt32} {esc : Array Nat} {st : RegaSt0}
    {ctrl : CtrlSt0} {cur : RegaTask0} {rest : List RegaTask0}
    (hf : 0 < fuel.toNat) :
    let st0 := regaPrependLbl0 cur st ctrl
    let ls := regaStep0 esc cur st0 ctrl rest
    regaRunAux0 fuel esc st ctrl (cur :: rest) =
      regaRunAux0 (fuel - 1) esc ls.st ls.ctrl ls.work := by
  have hne : fuel ≠ 0 := fun h => by
    have := congrArg UInt32.toNat h; rw [UInt32.toNat_zero] at this; omega
  exact regaRunAux0_succ hne esc st ctrl cur rest

theorem regaRunAux0_nil_eq (fuel : UInt32) (esc : Array Nat) (st : RegaSt0)
    (ctrl : CtrlSt0) :
    regaRunAux0 fuel esc st ctrl [] = (st, ctrl) :=
  regaRunAux0_nil fuel esc st ctrl

theorem regaRunAux0_clean_maxSlots {fuel : UInt32} {esc : Array Nat} {st : RegaSt0}
    {ctrl : CtrlSt0} {work : List RegaTask0} :
    (regaRunAux0 fuel esc { st with revDirs := [] } ctrl work).1.maxSlots =
      (regaRunAux0 fuel esc st ctrl work).1.maxSlots := by
  have hr := regaRunAux0_revDirs_append fuel esc st ctrl work
  rw [hr]

theorem taskMetaOk0_args_live {ctx : LegalCtx0} {fnIdx : UInt32} {fnMaxJump : Nat}
    {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0} {curPre : PreItem0}
    {restPre : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {rest : List RegaTask0} {mCur : TaskMeta0} {restMeta : List TaskMeta0}
    (h : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: restPre) seenJnz st ctrl
      (cur :: rest) (mCur :: restMeta))
    {args : List Arg0}
    (hm_use : ∀ a ∈ args, ∀ idx, a = .var idx →
      0 < nodeArgsUses0 (listGetU32 cur.venv idx) cur.venv cur.node)
    (hargs_ok : ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < cur.venv.length) :
    ∀ a ∈ args, ∀ idx, a = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
  fun a ha idx heq =>
    liveInTask0_of_nodeArg h (hargs_ok a ha idx heq) (hm_use a ha idx heq)

theorem abiRegAt0_not_calleeSaved (useRet : Bool) (i : UInt32) :
    ∀ r ∈ x64Frame.calleeSaved, r ≠ abiRegAt0 useRet i := by
  intro r hr heq
  exact calleeSaved_not_mem_scratchAndAbi r hr (heq ▸ abiRegAt0_mem_scratchAndAbi useRet i)

theorem argsSlotVal64_mono {venv : List UInt32} {vslot : Array Nat}
    {σ σ' : List (BitVec 64)} (hlen : σ'.length = σ.length) :
    ∀ {args : List Arg0} {vals : List (BitVec 64)},
      (∀ a ∈ args, ∀ idx, a = .var idx →
        ∀ hsl : (arrGetU0 vslot (listGetU32 venv idx)).toNat < σ.length,
          σ'[(arrGetU0 vslot (listGetU32 venv idx)).toNat]'(hlen ▸ hsl) =
            σ[(arrGetU0 vslot (listGetU32 venv idx)).toNat]'hsl) →
      ArgsSlotVal64 venv vslot σ args vals → ArgsSlotVal64 venv vslot σ' args vals
  | [], [], _, h => h
  | [], _ :: _, _, h => False.elim h
  | _ :: _, [], _, h => False.elim h
  | a :: rest, v :: vRest, hmem, ⟨ha, hr⟩ => by
    refine ⟨?_, argsSlotVal64_mono hlen (fun b hb => hmem b (List.mem_cons_of_mem _ hb)) hr⟩
    cases a with
    | immBool _ | immBits _ _ => exact ha
    | var idx =>
      obtain ⟨hsl, heq⟩ := ha
      refine ⟨hlen ▸ hsl, ?_⟩
      exact (hmem (.var idx) List.mem_cons_self idx rfl hsl).trans heq

theorem regaPrependLbl0_run {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) (fSz : UInt64)
    (restProg : List Directive) (s : MachineData) (post : MachineState → Prop)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hinf : (toAmd64Program symName (patchEpilogues0 fSz
        (emitFwd0 (regaPrependLbl0 cur { st with revDirs := [] } ctrl).revDirs) []) ++
      restProg).IsInfixAt (x64ScalarMach.prog h) k)
    (hk : (cur.lblId ≠ 0 →
        x64ScalarTarget.Defined h (label0ToSym symName (.loc ctrl.fnIdx cur.lblId)) ∧
        x64ScalarMach.labelAddr h (label0ToSym symName (.loc ctrl.fnIdx cur.lblId)) =
          x64ScalarMach.addrOf h k) →
      restProg.IsInfixAt (x64ScalarMach.prog h)
        (k + (if cur.lblId = 0 then 0 else 1)) →
      x64ScalarMach.Run h (k + (if cur.lblId = 0 then 0 else 1)) s post) :
    x64ScalarMach.Run h k s post := by
  rw [regaPrependLbl0_dirs_eq] at hinf
  by_cases hlbl : cur.lblId = 0
  · have hinf' : restProg.IsInfixAt (x64ScalarMach.prog h) k := by
      simpa only [hlbl, ↓reduceIte, emitFwd0, revDirAux0_eq, List.reverse_nil, List.append_nil,
        patchEpilogues0_eq, List.flatMap_nil, toAmd64Program, List.nil_append] using hinf
    have hk' := hk (fun hne => absurd hlbl hne)
    simp only [hlbl, ↓reduceIte, Nat.add_zero] at hk' ⊢
    exact hk' hinf'
  · simp only [hlbl, ↓reduceIte, emitFwd0, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_nil, patchEpilogues0_eq, List.flatMap_cons, List.flatMap_nil,
      patchDir0, toAmd64Program, dir0ToAmd64, List.singleton_append] at hinf
    have hlab_at := (List.IsInfixAt.cons hinf).1
    have hrest_inf := (List.IsInfixAt.cons hinf).2
    have hdef : x64ScalarTarget.Defined h (label0ToSym symName (.loc ctrl.fnIdx cur.lblId)) :=
      ⟨k, hlab_at⟩
    have hadr : x64ScalarMach.labelAddr h (label0ToSym symName (.loc ctrl.fnIdx cur.lblId)) =
        x64ScalarMach.addrOf h k :=
      infix_labelAddr_eq hu hinf rfl
    have hk' := hk (fun _ => ⟨hdef, hadr⟩)
    simp only [hlbl, ↓reduceIte] at hk' ⊢
    exact x64ScalarTarget.frameSpec.label_spec hlab_at (hk' hrest_inf)

theorem fnFrameInv0_mem_of_slots {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {mCur : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (h : s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆
      (Eq mCur ⋆ x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
        region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf)) :
    s.dmem =⋆ Eq mCur ⋆ array64 (s.regs.get64 .rsp) σ ⋆
      x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
      region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf := by
  rwa [← sep_assoc (array64 (s.regs.get64 .rsp) σ),
    ← sep_assoc (array64 (s.regs.get64 .rsp) σ) (Eq mCur ⋆ _),
    ← sep_assoc (array64 (s.regs.get64 .rsp) σ) (Eq mCur),
    sep_comm (array64 (s.regs.get64 .rsp) σ) (Eq mCur)] at h

theorem fnFrameInv0_mem_entry {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat}
    {Rf : Mem 64 → Prop} {mCur : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCur s σ) :
    s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ Eq mCur ⋆
      x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
      region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf :=
  sep_cast hfr.2.2.2 (by ac_rfl)

theorem epilogue_reconstruct_entry {sp0 : BitVec 64} {ra0 : Int64} {ns : UInt32}
    {n : Nat} {hle : x64FrameSize ns.toNat ≤ n} {hn : n + 8 ≤ 2 ^ 64} {mCur : Mem 64}
    {Rf : Mem 64 → Prop} {dmem : Mem 64}
    (hm : dmem =⋆ x64ScalarFramePreds.RetAddr (sp0 - BitVec.ofNat 64 (x64FrameSize ns.toNat) +
        BitVec.ofNat 64 (x64FrameSize ns.toNat)) ra0 ⋆
      region (sp0 - BitVec.ofNat 64 (x64FrameSize ns.toNat)) (x64FrameSize ns.toNat) ⋆
      Eq mCur ⋆ region (sp0 - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf) :
    dmem =⋆ Eq mCur ⋆ x64ScalarTarget.Entry sp0 ra0 n ⋆ Rf := by
  have hsp : sp0 - BitVec.ofNat 64 (x64FrameSize ns.toNat) +
      BitVec.ofNat 64 (x64FrameSize ns.toNat) = sp0 := BitVec.sub_add_cancel _ _
  have hadd : (sp0 - BitVec.ofNat 64 n) + BitVec.ofNat 64 (n - x64FrameSize ns.toNat) =
      sp0 - BitVec.ofNat 64 (x64FrameSize ns.toNat) := by
    have h1 := sub_add_ofNat_le sp0 (n := n) (k := n - x64FrameSize ns.toNat) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hle] at h1
    exact h1
  have hsplit : region (sp0 - BitVec.ofNat 64 n) n =
      (region (sp0 - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆
        region (sp0 - BitVec.ofNat 64 (x64FrameSize ns.toNat)) (x64FrameSize ns.toNat)) := by
    have hs := region_split (a := sp0 - BitVec.ofNat 64 n)
      (n1 := n - x64FrameSize ns.toNat) (n2 := x64FrameSize ns.toNat) (by omega)
    rw [hadd] at hs
    rw [show n - x64FrameSize ns.toNat + x64FrameSize ns.toNat = n from by omega] at hs
    exact hs
  rw [hsp] at hm
  change dmem =⋆ Eq mCur ⋆
    (region (sp0 - BitVec.ofNat 64 n) n ⋆ x64ScalarFramePreds.RetAddr sp0 ra0) ⋆ Rf
  rw [hsplit]
  exact sep_cast hm (by ac_rfl)

theorem epilogue_reconstruct_exit {sp0 : BitVec 64} {ra0 : Int64} {n : Nat}
    {hn : n + 8 ≤ 2 ^ 64} {mCur : Mem 64} {Rf : Mem 64 → Prop} {dmem : Mem 64}
    (hm : dmem =⋆ Eq mCur ⋆ x64ScalarTarget.Entry sp0 ra0 n ⋆ Rf) :
    dmem =⋆ Eq mCur ⋆ x64ScalarTarget.Exit sp0 n ⋆ Rf :=
  Target.exit_of_entry x64ScalarTarget hn hm

theorem call_split_frame_region {sp0 : BitVec 64} {n bound xSz : Nat}
    (hle : xSz + 8 + bound ≤ n) (hn : n + 8 ≤ 2 ^ 64) :
    region (sp0 - BitVec.ofNat 64 n) (n - xSz) =
      (region ((sp0 - BitVec.ofNat 64 xSz) - 8#64) 8 ⋆
        (region (((sp0 - BitVec.ofNat 64 xSz) - 8#64) - BitVec.ofNat 64 bound) bound ⋆
          region (sp0 - BitVec.ofNat 64 n) (n - xSz - 8 - bound))) := by
  have ha1 : (sp0 - BitVec.ofNat 64 n) + BitVec.ofNat 64 (n - xSz - 8 - bound) =
      ((sp0 - BitVec.ofNat 64 xSz) - 8#64) - BitVec.ofNat 64 bound := by
    have h1 := sub_add_ofNat_le sp0 (n := n) (k := n - xSz - 8 - bound) (by omega)
    rw [show n - (n - xSz - 8 - bound) = xSz + 8 + bound from by omega] at h1
    rw [h1]; grind
  have ha2 : (((sp0 - BitVec.ofNat 64 xSz) - 8#64) - BitVec.ofNat 64 bound) +
      BitVec.ofNat 64 bound = (sp0 - BitVec.ofNat 64 xSz) - 8#64 := BitVec.sub_add_cancel _ _
  have h1 := region_split (a := sp0 - BitVec.ofNat 64 n)
    (n1 := n - xSz - 8 - bound) (n2 := bound + 8) (by omega)
  have h2 := region_split (a := ((sp0 - BitVec.ofNat 64 xSz) - 8#64) - BitVec.ofNat 64 bound)
    (n1 := bound) (n2 := 8) (by omega)
  rw [ha1] at h1
  rw [ha2] at h2
  rw [show n - xSz - 8 - bound + (bound + 8) = n - xSz from by omega] at h1
  rw [h1, h2]
  ac_rfl

theorem abiRegs_in_scratchAndAbi (useRet : Bool) (n : Nat) :
    ∀ r ∈ (.r10 :: (List.range n).map (fun j => abiRegAt0 useRet (UInt32.ofNat j))),
      r ∈ x64ScratchAndAbi := by
  intro r hr
  simp only [List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨_, _, rfl⟩
  · simp [x64ScratchAndAbi]
  · exact abiRegAt0_mem_scratchAndAbi useRet _

theorem x64Scratch_frame_rsp_cs {s1 s2 : MachineData}
    (hfr : x64ScalarMach.Frame x64CondReads s1 s2 x64Scratch [] maskNone) :
    s2.regs.get64 .rsp = s1.regs.get64 .rsp ∧
    (∀ r ∈ x64Frame.calleeSaved, s2.regs.get64 r = s1.regs.get64 r) :=
  ⟨hfr.1 .rsp (by simp [x64Scratch]), fun r hr =>
    hfr.1 r (fun hm => calleeSaved_not_in_rsp_scratch r hr (List.mem_cons_of_mem _ hm))⟩

theorem fnFrameInv0_weaken_scratchAndAbi {ns : UInt32} {s0 : MachineData} {ra0 : Int64}
    {n : Nat} {Rf : Mem 64 → Prop} {mCur : Mem 64} {s1 s2 : MachineData} {σ : List (BitVec 64)}
    {fClob : FlagMask}
    (h : FnFrameInv0 ns s0 ra0 n Rf mCur s1 σ)
    (hfr : x64ScalarMach.Frame x64CondReads s1 s2 x64ScratchAndAbi [] fClob)
    (hmem : s2.dmem = s1.dmem) :
    FnFrameInv0 ns s0 ra0 n Rf mCur s2 σ :=
  fnFrameInv0_of_eq h hfr rsp_not_mem_scratchAndAbi calleeSaved_not_mem_scratchAndAbi hmem

/-! ## 2. Terminator Runners & Shared Result Binder -/

theorem glEntriesSem0_get? {h : Host} {symName : Sym0 → Sym} {post : MachineState → Prop}
    {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat} {Rf : Mem 64 → Prop}
    {esc : Array Nat} {st : RegaSt0} {cur : RegaTask0} {mCur : TaskMeta0}
    {vs : List ((ty : Ty) × Val ty)} {fnIdx : UInt32} :
    ∀ {gl : List LblInfo0} {ls : List ((ts : List Ty) × Cont ts)} {j : Nat}
      {info : LblInfo0},
      GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx gl ls →
      listGet? gl j = some info →
      ∃ lentry, listGet? ls j = some lentry ∧
        GlEntrySem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx info lentry
  | [], _, j, _, _, hl => by cases j <;> (dsimp only [listGet?] at hl; cases hl)
  | _ :: _, [], _, _, hgl, _ => False.elim hgl
  | info :: glRest, lentry :: lsRest, 0, info', hgl, hl => by
    dsimp only [GlEntriesSem0] at hgl
    dsimp only [listGet?] at hl ⊢
    injection hl with he; subst he; exact ⟨lentry, rfl, hgl.1⟩
  | _ :: glRest, _ :: lsRest, j + 1, info', hgl, hl => by
    dsimp only [GlEntriesSem0] at hgl
    dsimp only [listGet?] at hl ⊢
    exact glEntriesSem0_get? (gl := glRest) (ls := lsRest) (j := j) hgl.2 hl

theorem listGet?_gl_of_lT {h : Host} {symName : Sym0 → Sym} {post : MachineState → Prop}
    {ns : UInt32} {s0 : MachineData} {ra0 : Int64} {n : Nat} {Rf : Mem 64 → Prop}
    {esc : Array Nat} {preSt : PreSt0} {st : RegaSt0} {ctrl : CtrlSt0}
    {curPre : PreItem0} {cur : RegaTask0} {mCur : TaskMeta0}
    {vs : List ((ty : Ty) × Val ty)} {ls : List ((ts : List Ty) × Cont ts)}
    {fnIdx : UInt32} {maxBd : Nat} {ctx : LegalCtx0}
    {j : UInt32} {pts : List Ty0}
    (htm : TaskMetaOk0 ctx maxBd esc preSt st ctrl curPre cur mCur)
    (hgl : GlEntriesSem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx mCur.gl ls)
    (hlg : listGetSig0 mCur.lT j = some pts) :
    ∃ (info : LblInfo0) (lentry : (ts : List Ty) × Cont ts),
      info ∈ mCur.gl ∧ info.lbl = listGetU32 cur.lenv j ∧ info.pts = pts ∧
      LblInfoOk0 esc st ctrl info ∧ listGet? ls j.toNat = some lentry ∧
      GlEntrySem0 h symName post ns s0 ra0 n Rf esc st cur mCur vs fnIdx info lentry := by
  obtain ⟨_, _, _, _, hllen, hgl_len, hgi, _, _, _, _, _, _, hinfo_ok, _, _, _⟩ := htm
  rw [listGetSig0_eq_listGet?] at hlg
  have hjn : j.toNat < mCur.lT.length := Nat.lt_of_not_le fun hge => False.elim <| by
    have hnone : ∀ (xs : List (List Ty0)) (k : Nat), xs.length ≤ k → listGet? xs k = none := by
      intro xs; induction xs with
      | nil => intro k _; cases k <;> rfl
      | cons _ _ ih => intro k hk; cases k with
        | zero => simp at hk
        | succ k' => simp at hk; exact ih k' (by omega)
    rw [hnone mCur.lT j.toNat hge] at hlg; cases hlg
  have h1 : j.toNat < mCur.gl.length := by rw [hgl_len, hllen]; exact hjn
  have h2 : j.toNat < cur.lenv.length := by rw [hllen]; exact hjn
  have hgi_j := hgi j.toNat h1 h2 hjn
  have hmem : mCur.gl[j.toNat]'h1 ∈ mCur.gl := List.getElem_mem h1
  have hpts : (mCur.gl[j.toNat]'h1).pts = pts := by
    rw [listGet?_eq_getElem10 mCur.lT j.toNat hjn] at hlg
    injection hlg with he; rw [hgi_j.2, he]
  have hlbl : (mCur.gl[j.toNat]'h1).lbl = listGetU32 cur.lenv j := by
    rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 cur.lenv 0 j.toNat h2, hgi_j.1]
  obtain ⟨lentry, hl_ls, hl_sem⟩ :=
    glEntriesSem0_get? hgl (listGet?_eq_getElem10 mCur.gl j.toNat h1)
  exact ⟨mCur.gl[j.toNat]'h1, lentry, hmem, hlbl, hpts, hinfo_ok _ hmem, hl_ls, hl_sem⟩

private theorem jumpStageLoop0_spec {symName : Sym0 → Sym} {h : Host}
    {st : RegaSt0} {cur : RegaTask0} {G : Mem 64 → Prop} {post : MachineState → Prop} :
    ∀ (args : List Arg0) (k : Nat) (tmpBase : UInt32) (vals : List (BitVec 64))
      (σ : List (BitVec 64)) (s : MachineData),
      (hlen : args.length = vals.length) →
      (hσ_bd : tmpBase.toNat + args.length ≤ σ.length) →
      (h32 : tmpBase.toNat + args.length < 2 ^ 32) →
      ArgsSlotVal64 cur.venv st.vslot σ args vals →
      (∀ a ∈ args, ∀ idx, a = .var idx →
        (arrGetU0 st.vslot (listGetU32 cur.venv idx)).toNat < tmpBase.toNat) →
      (s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) →
      x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (jumpStageLoop0 args tmpBase cur.venv st.vslot [])))
        x64ScratchAndAbi [] maskNone s
        (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = σ.length),
          (∀ q, q < tmpBase.toNat → ∀ hq : q < σ.length,
            σ'[q]'(hσ' ▸ hq) = σ[q]'hq) ∧
          (∀ (q : Nat) (hq : q < vals.length),
            σ'[tmpBase.toNat + q]'(hσ' ▸ by omega) = vals[q]'hq) ∧
          (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post := by
  intro args
  induction args with
  | nil =>
    intro k tmpBase vals σ s hlen _ _ _ _ hmem
    cases vals with
    | nil =>
      dsimp only [jumpStageLoop0, emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
      refine Machine.FallsTo.nil ⟨σ, rfl, fun _ _ _ => rfl,
        fun _ hq => absurd hq (Nat.not_lt_zero _), hmem⟩
    | cons _ _ => simp at hlen
  | cons a rest ih =>
    intro k tmpBase vals σ s hlen hσ_bd h32 hvals hdisj hmem
    cases vals with
    | nil => simp at hlen
    | cons v vRest =>
      simp only [List.length_cons] at hlen hσ_bd h32
      obtain ⟨hva, hvr⟩ := hvals
      have htb1 : (tmpBase + 1).toNat = tmpBase.toNat + 1 := by
        rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
      have htb_lt : tmpBase.toNat < σ.length := by omega
      have hsplit1 : jumpStageLoop0 (a :: rest) tmpBase cur.venv st.vslot [] =
          jumpStageLoop0 rest (tmpBase + 1) cur.venv st.vslot [] ++
            (emitSlotMem0 false .rax tmpBase [] ++ emitLoadArg0 .rax a cur.venv st.vslot []) := by
        dsimp only [jumpStageLoop0]
        rw [(jumpStageLoop0_acc rest (tmpBase + 1) cur.venv st.vslot _).1,
          (emitSlotMem0_acc false .rax tmpBase _).1]
      rw [hsplit1, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
      have hld := emitLoadArg0_spec (symName := symName) (h := h) (k := k) (post := post)
        .rax (by decide) a cur.venv st.vslot hva hmem
      have hone :
          x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (emitLoadArg0 .rax a cur.venv st.vslot [])) ++
              toAmd64Program symName (emitFwd0 (emitSlotMem0 false .rax tmpBase [])))
            ([.rax, .r10] ++ [.r10]) ([] ++ []) (maskNone ||| maskNone) s
            (fun s2 => s2.dmem =⋆
              array64 (s2.regs.get64 .rsp) (σ.set tmpBase.toNat v) ⋆ G) post :=
        Machine.FallsTo.comp hld fun s1 ⟨hr1, hm1⟩ hfr1 => by
          have hrsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp := hfr1.1 .rsp (by simp)
          have hmem1 : s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ G := by
            rw [hm1, hrsp1]; exact hmem
          have hst := emitSlotMem0_st_spec (symName := symName) (h := h)
            (k := k + (toAmd64Program symName
              (emitFwd0 (emitLoadArg0 .rax a cur.venv st.vslot []))).length)
            (post := post) .rax (by decide) tmpBase htb_lt hmem1
          refine Machine.FallsTo.conseq hst fun s2 hm2 hfr2 => ?_
          have hrsp2 : s2.regs.get64 .rsp = s1.regs.get64 .rsp := hfr2.1 .rsp (by simp)
          rw [hr1, ← hrsp2] at hm2; exact hm2
      have hone_wk :
          x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (emitLoadArg0 .rax a cur.venv st.vslot [])) ++
              toAmd64Program symName (emitFwd0 (emitSlotMem0 false .rax tmpBase [])))
            x64ScratchAndAbi [] maskNone s
            (fun s2 => s2.dmem =⋆
              array64 (s2.regs.get64 .rsp) (σ.set tmpBase.toNat v) ⋆ G) post :=
        Machine.FallsTo.weaken hone
          (fun r hr => by
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with (rfl | rfl) | rfl <;> simp [x64ScratchAndAbi])
          (fun _ hv => nomatch hv) (by decide)
      have hvr1 : ArgsSlotVal64 cur.venv st.vslot (σ.set tmpBase.toNat v) rest vRest :=
        argsSlotVal64_mono List.length_set (fun b hb idx heq hsl => by
          have hlt := hdisj b (List.mem_cons_of_mem _ hb) idx heq
          exact List.getElem_set_ne (Nat.ne_of_gt hlt) (by rw [List.length_set]; exact hsl)) hvr
      have hcomp := Machine.FallsTo.comp hone_wk fun s2 hm2 _ =>
        ih (k + (toAmd64Program symName (emitFwd0 (emitLoadArg0 .rax a cur.venv st.vslot [])) ++
          toAmd64Program symName (emitFwd0 (emitSlotMem0 false .rax tmpBase []))).length)
          (tmpBase + 1) vRest (σ.set tmpBase.toNat v) s2
          (Nat.succ.inj hlen) (by rw [List.length_set, htb1]; omega)
          (by rw [htb1]; omega)
          hvr1 (fun b hb idx heq => Nat.lt_of_lt_of_le
            (hdisj b (List.mem_cons_of_mem _ hb) idx heq) (by rw [htb1]; omega)) hm2
      have hwk :
          x64ScalarMach.FallsTo x64CondReads h k
            (toAmd64Program symName (emitFwd0 (emitLoadArg0 .rax a cur.venv st.vslot [])) ++
              toAmd64Program symName (emitFwd0 (emitSlotMem0 false .rax tmpBase [])) ++
              toAmd64Program symName
                (emitFwd0 (jumpStageLoop0 rest (tmpBase + 1) cur.venv st.vslot [])))
            x64ScratchAndAbi [] maskNone s
            (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = (σ.set tmpBase.toNat v).length),
              (∀ q, q < (tmpBase + 1).toNat → ∀ hq : q < (σ.set tmpBase.toNat v).length,
                σ'[q]'(hσ' ▸ hq) = (σ.set tmpBase.toNat v)[q]'hq) ∧
              (∀ (q : Nat) (hq : q < vRest.length),
                σ'[(tmpBase + 1).toNat + q]'(hσ' ▸ by
                  have hls_len : (σ.set tmpBase.toNat v).length = σ.length := List.length_set
                  have := hlen; omega) = vRest[q]'hq) ∧
              (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post :=
        Machine.FallsTo.weaken hcomp (fun r hr => (List.mem_append.mp hr).elim id id)
          (fun _ hv => nomatch hv) (by decide)
      refine Machine.FallsTo.conseq hwk fun s' ⟨σ', hσ', hlow, hvals', hmem'⟩ _ => ?_
      refine ⟨σ', hσ'.trans List.length_set, fun q hq hqσ => ?_, fun q hq => ?_, hmem'⟩
      · have hne : tmpBase.toNat ≠ q := by omega
        exact (hlow q (by rw [htb1]; omega) (by rw [List.length_set]; exact hqσ)).trans
          (List.getElem_set_ne hne (by rw [List.length_set]; exact hqσ))
      · cases q with
        | zero =>
          simp only [Nat.add_zero, List.getElem_cons_zero]
          have h1 := hlow tmpBase.toNat (by rw [htb1]; omega)
            (by rw [List.length_set]; exact htb_lt)
          exact h1.trans (List.getElem_set_self ..)
        | succ q' =>
          simp only [List.getElem_cons_succ]
          have h' := hvals' q' (Nat.lt_of_succ_lt_succ hq)
          simpa only [htb1, Nat.add_assoc, Nat.add_comm 1 q'] using h'

private theorem jumpCopyLoop0_spec {symName : Sym0 → Sym} {h : Host} {G : Mem 64 → Prop}
    {post : MachineState → Prop} :
    ∀ (tgts : List UInt32) (k : Nat) (tmpBase : UInt32) (σ : List (BitVec 64)) (s : MachineData),
      tgts.Nodup →
      (∀ t ∈ tgts, t.toNat < tmpBase.toNat) →
      (hσ_bd : tmpBase.toNat + tgts.length ≤ σ.length) →
      (h32 : tmpBase.toNat + tgts.length < 2 ^ 32) →
      (s.dmem =⋆ array64 (s.regs.get64 .rsp) σ ⋆ G) →
      x64ScalarMach.FallsTo x64CondReads h k
        (toAmd64Program symName (emitFwd0 (jumpCopyLoop0 tgts tmpBase [])))
        x64ScratchAndAbi [] maskNone s
        (fun s' => ∃ (σ' : List (BitVec 64)) (hσ' : σ'.length = σ.length),
          (∀ q : Nat, (∀ t ∈ tgts, t.toNat ≠ q) → ∀ hq : q < σ.length,
            σ'[q]'(hσ' ▸ hq) = σ[q]'hq) ∧
          (∀ (j : Nat) (hj : j < tgts.length),
            ∃ hsl : tgts[j].toNat < σ'.length, ∃ hs : tmpBase.toNat + j < σ.length,
              σ'[tgts[j].toNat]'hsl = σ[tmpBase.toNat + j]'hs) ∧
          (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post := by
  intro tgts
  induction tgts with
  | nil =>
    intro k tmpBase σ s _ _ _ _ hmem
    dsimp only [jumpCopyLoop0, emitFwd0, List.reverse_nil, toAmd64Program, List.flatMap_nil]
    exact Machine.FallsTo.nil ⟨σ, rfl, fun _ _ _ => rfl,
      fun _ hj => absurd hj (Nat.not_lt_zero _), hmem⟩
  | cons t rest ih =>
    intro k tmpBase σ s hnd hlt hσ_bd h32 hmem
    obtain ⟨hnin, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.length_cons] at hσ_bd h32
    have htb1 : (tmpBase + 1).toNat = tmpBase.toNat + 1 := by
      rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
    have ht_lt : t.toNat < tmpBase.toNat := hlt t List.mem_cons_self
    have ht_ltσ : t.toNat < σ.length := by omega
    have htb_ltσ : tmpBase.toNat < σ.length := by omega
    have hsplit1 : jumpCopyLoop0 (t :: rest) tmpBase [] =
        jumpCopyLoop0 rest (tmpBase + 1) [] ++
          (emitSlotMem0 false .rax t [] ++ emitSlotMem0 true .rax tmpBase []) := by
      dsimp only [jumpCopyLoop0]
      rw [(jumpCopyLoop0_acc rest (tmpBase + 1) _).1, (emitSlotMem0_acc false .rax t _).1]
    rw [hsplit1, emitFwd0_append, emitFwd0_append, toAmd64Program_append, toAmd64Program_append]
    have hld := emitSlotMem0_ld_spec (symName := symName) (h := h) (k := k) (post := post)
      .rax (by decide) tmpBase htb_ltσ hmem
    have hone :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitSlotMem0 true .rax tmpBase [])) ++
            toAmd64Program symName (emitFwd0 (emitSlotMem0 false .rax t [])))
          ([.rax, .r10] ++ [.r10]) ([] ++ []) (maskNone ||| maskNone) s
          (fun s2 => s2.dmem =⋆
            array64 (s2.regs.get64 .rsp) (σ.set t.toNat σ[tmpBase.toNat]) ⋆ G) post :=
      Machine.FallsTo.comp hld fun s1 ⟨hr1, hm1⟩ hfr1 => by
        have hrsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp := hfr1.1 .rsp (by simp)
        have hmem1 : s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ G := by
          rw [hm1, hrsp1]; exact hmem
        have hst := emitSlotMem0_st_spec (symName := symName) (h := h)
          (k := k + (toAmd64Program symName
            (emitFwd0 (emitSlotMem0 true .rax tmpBase []))).length)
          (post := post) .rax (by decide) t ht_ltσ hmem1
        refine Machine.FallsTo.conseq hst fun s2 hm2 hfr2 => ?_
        have hrsp2 : s2.regs.get64 .rsp = s1.regs.get64 .rsp := hfr2.1 .rsp (by simp)
        rw [hr1, ← hrsp2] at hm2; exact hm2
    have hone_wk :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitSlotMem0 true .rax tmpBase [])) ++
            toAmd64Program symName (emitFwd0 (emitSlotMem0 false .rax t [])))
          x64ScratchAndAbi [] maskNone s
          (fun s2 => s2.dmem =⋆
            array64 (s2.regs.get64 .rsp) (σ.set t.toNat σ[tmpBase.toNat]) ⋆ G) post :=
      Machine.FallsTo.weaken hone
        (fun r hr => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with (rfl | rfl) | rfl <;> simp [x64ScratchAndAbi])
        (fun _ hv => nomatch hv) (by decide)
    have hcomp := Machine.FallsTo.comp hone_wk fun s2 hm2 _ =>
      ih (k + (toAmd64Program symName (emitFwd0 (emitSlotMem0 true .rax tmpBase [])) ++
        toAmd64Program symName (emitFwd0 (emitSlotMem0 false .rax t []))).length)
        (tmpBase + 1) (σ.set t.toNat σ[tmpBase.toNat]) s2 hnd'
        (fun q hq => by
          have := hlt q (List.mem_cons_of_mem _ hq); rw [htb1]; omega)
        (by rw [List.length_set, htb1]; omega)
        (by rw [htb1]; omega)
        hm2
    have hwk :
        x64ScalarMach.FallsTo x64CondReads h k
          (toAmd64Program symName (emitFwd0 (emitSlotMem0 true .rax tmpBase [])) ++
            toAmd64Program symName (emitFwd0 (emitSlotMem0 false .rax t [])) ++
            toAmd64Program symName (emitFwd0 (jumpCopyLoop0 rest (tmpBase + 1) [])))
          x64ScratchAndAbi [] maskNone s
          (fun s' => ∃ (σ' : List (BitVec 64))
              (hσ' : σ'.length = (σ.set t.toNat σ[tmpBase.toNat]).length),
            (∀ q : Nat, (∀ u ∈ rest, u.toNat ≠ q) →
              ∀ hq : q < (σ.set t.toNat σ[tmpBase.toNat]).length,
                σ'[q]'(hσ' ▸ hq) = (σ.set t.toNat σ[tmpBase.toNat])[q]'hq) ∧
            (∀ (j : Nat) (hj : j < rest.length),
              ∃ hsl : rest[j].toNat < σ'.length,
                ∃ hs : (tmpBase + 1).toNat + j < (σ.set t.toNat σ[tmpBase.toNat]).length,
                  σ'[rest[j].toNat]'hsl =
                    (σ.set t.toNat σ[tmpBase.toNat])[(tmpBase + 1).toNat + j]'hs) ∧
            (s'.dmem =⋆ array64 (s'.regs.get64 .rsp) σ' ⋆ G)) post :=
      Machine.FallsTo.weaken hcomp (fun r hr => (List.mem_append.mp hr).elim id id)
        (fun _ hv => nomatch hv) (by decide)
    refine Machine.FallsTo.conseq hwk fun s' ⟨σ', hσ', hpres, htgts, hmem'⟩ _ => ?_
    refine ⟨σ', hσ'.trans List.length_set, fun q hq hqσ => ?_, fun j hj => ?_, hmem'⟩
    · have hne_t : t.toNat ≠ q := hq t List.mem_cons_self
      have hpres_r := hpres q (fun u hu => hq u (List.mem_cons_of_mem _ hu))
        (by rw [List.length_set]; exact hqσ)
      exact hpres_r.trans (List.getElem_set_ne hne_t (by rw [List.length_set]; exact hqσ))
    · cases j with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        have hpres_t := hpres t.toNat (fun u hu htu => hnin (u32_ext7 htu ▸ hu))
          (by rw [List.length_set]; exact ht_ltσ)
        refine ⟨hσ' ▸ (by rw [List.length_set]; exact ht_ltσ), htb_ltσ, ?_⟩
        exact hpres_t.trans (List.getElem_set_self ..)
      | succ j' =>
        simp only [List.getElem_cons_succ]
        simp only [List.length_cons] at hj
        obtain ⟨hsl, hs, heq⟩ := htgts j' (Nat.lt_of_succ_lt_succ hj)
        have hne_idx : t.toNat ≠ (tmpBase + 1).toNat + j' := by rw [htb1]; omega
        refine ⟨hsl, by omega, ?_⟩
        exact heq.trans (by
          simpa only [htb1, Nat.add_assoc, Nat.add_comm 1 j'] using
            List.getElem_set_ne hne_idx hs)

private theorem tupInSlots0_of_list {σ : List (BitVec 64)} :
    ∀ {tgts : List UInt32} {pts : List Ty0} (xs : Tup Val (ty0ListToTy pts)),
      (hlen : tgts.length = pts.length) →
      (∀ (j : Nat) (hj : j < pts.length),
        ∃ hsl : (tgts[j]'(by omega)).toNat < σ.length,
          σ[(tgts[j]'(by omega)).toNat]'hsl =
            (tupToCanon64s pts xs)[j]'(by rw [tupToCanon64s_length]; exact hj)) →
      TupInSlots0 σ tgts pts xs
  | [], [], (), _, _ => trivial
  | [], _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | s :: ss, t :: ts, (v, vs), hlen, hget => by
    refine ⟨?_, tupInSlots0_of_list vs (Nat.succ.inj hlen) fun j hj => ?_⟩
    · obtain ⟨hsl, heq⟩ := hget 0 (Nat.zero_lt_succ _)
      exact ⟨hsl, heq⟩
    · obtain ⟨hsl, heq⟩ := hget (j + 1) (Nat.succ_lt_succ hj)
      exact ⟨hsl, heq⟩

private theorem tupInSlots0_nil {σ : List (BitVec 64)} :
    ∀ (pts : List Ty0) (xs : Tup Val (ty0ListToTy pts)), pts.length = 0 → TupInSlots0 σ [] pts xs
  | [], (), _ => trivial

private theorem tupInSlots0_singleton_of_eq {σ : List (BitVec 64)} {s_tgt : UInt32}
    (hsl : s_tgt.toNat < σ.length) :
    ∀ (pts : List Ty0) (xs : Tup Val (ty0ListToTy pts)),
      (hlen : pts.length = 1) →
      (σ[s_tgt.toNat]'hsl = (tupToCanon64s pts xs)[0]'(by rw [tupToCanon64s_length]; omega)) →
      TupInSlots0 σ [s_tgt] pts xs
  | [_], (_, ()), _, hσ => ⟨⟨hsl, hσ⟩, trivial⟩

theorem emitJump0_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {j : UInt32} {args : List Arg0} {k : Nat} {fuel : UInt32}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .jump j args)
    (hfuel : workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat)
    (hns_eq : (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
        ctrl [cur]).1.revDirs) [])).IsInfixAt (x64ScalarMach.prog h) k)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hwp : wp0 Γ symName rs vs ls Q X cur.node mCurMem)
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ)
    (hag : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ)
    (hgl : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped st cur mCur vs fnIdx mCur.gl ls) :
    x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  have hcur_ok_cp := hcur_ok
  obtain ⟨hpn, _, hvlen, hvlt, _, _, _, hwf, hfit, _, _, hpool, hnxt_nv, hinfo_ok,
    _, _, hlive⟩ := hcur_ok
  rw [hnd] at hwf hfit
  have ⟨pts, hlg, hcargs⟩ : ∃ pts, listGetSig0 mCur.lT j = some pts ∧
      checkArgs0 mCur.vT pts args = true := by
    cases hwf; exact ⟨‹_›, ‹_›, ‹_›⟩
  obtain ⟨info, lentry, hinfo_mem, hinfo_lbl, rfl, hinfo_ok, hl_ls, hl_sem⟩ :=
    listGet?_gl_of_lT hcur_ok_cp hgl hlg
  obtain ⟨hnxt_le, hdef_lbl, outerVs, pLen, hplen, hov, hvt, hovs, J, rfl, hJ⟩ := hl_sem
  rw [hnd, wp0_jump, hl_ls] at hwp
  dsimp only at hwp
  cases hev : evalArgs0Ty vs (ty0ListToTy info.pts) args with
  | none => rw [hev] at hwp; exact False.elim hwp
  | some argv =>
    rw [hev] at hwp
    have hargs_ok : ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < cur.venv.length := by
      have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva; exact hva
    have hlive_args : ∀ a ∈ args, ∀ idx, a = .var idx →
        LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
      taskMetaOk0_args_live hinv (fun a ha idx heq => by
        rw [hnd]; exact nodeArgsUses0_pos_lin_term (heq ▸ ha)) hargs_ok
    have hvals := argsSlotVal64_of_evalArgs0Ty hcargs hag hev hlive_args
    have hc_specs := checkArgs0_spec hcargs
    have hesc_outer0 : EscOuterAgree0 preRes.escaped st.vslot info outerVs σ :=
      escOuterAgree0_of_slotsAgree0 hag hplen hov hvt hovs
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    let stClean := emitJump0 j args cur st0Clean ctrl
    have hrun1 :
        regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] } ctrl [cur] =
          (stClean, ctrl) := by
      have hd := regaRunAux0_step_once (fuel := (1 : UInt32)) (esc := preRes.escaped)
        (st := { st with revDirs := [] }) (ctrl := ctrl) (cur := cur) (rest := []) (by decide)
      dsimp only at hd
      have hst_eq : regaStep0 preRes.escaped cur st0Clean ctrl [] =
          LoopStep0.mk stClean ctrl [] := by
        dsimp only [regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
      rw [hd, hst_eq]; dsimp only; exact regaRunAux0_nil_eq ..
    have hrun_rev :
        (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
          ctrl [cur]).1.revDirs = stClean.revDirs :=
      congrArg (fun p => p.1.revDirs) hrun1
    have hstClean_acc := emitJump0_revDirs j args cur st0Clean ctrl
    dsimp only at hstClean_acc
    let stJ := emitJump0 j args cur { st0Clean with revDirs := [] } ctrl
    have hsplit_clean :
        patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
            ctrl [cur]).1.revDirs) [] =
        patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 st0Clean.revDirs) [] ++
          emitFwd0 stJ.revDirs := by
      rw [hrun_rev]
      dsimp only [stClean]
      rw [hstClean_acc.1, emitFwd0_append, patchEpilogues0_append,
        patchEpilogues0_of_listNoSpZero0 (x64FrameSizeU0 ns)
          (listNoSpZero0_emitFwd0 (ds := stJ.revDirs) hstClean_acc.2)]
    rw [hsplit_clean, toAmd64Program_append] at hcode
    refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns)
      (toAmd64Program symName (emitFwd0 stJ.revDirs)) s (fnPost0 h rs Q X s0 ra0 n nX Rf)
      hu hcode fun _ hprog_j => ?_
    have h_jmp_run : ∀ (s' : MachineData) (σ' : List (BitVec 64)) (k_j : Nat),
        FnFrameInv0 ns s0 ra0 n Rf mCurMem s' σ' →
        EscOuterAgree0 preRes.escaped st.vslot info outerVs σ' →
        TupInSlots0 σ' info.tgts info.pts argv →
        (toAmd64Program symName (emitFwd0 [.jmp (.loc ctrl.fnIdx info.lbl)])).IsInfixAt
          (x64ScalarMach.prog h) k_j →
        x64ScalarMach.Run h k_j s' (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
      intro s' σ' k_j hfr' hesc' htup' hinf_j
      have hjmp_eq : toAmd64Program symName (emitFwd0 [.jmp (.loc ctrl.fnIdx info.lbl)]) =
          x64ScalarIsa.gpr.jmp (label0ToSym symName (.loc ctrl.fnIdx info.lbl)) := rfl
      rw [hjmp_eq] at hinf_j
      have hjmp_def :
          x64ScalarTarget.Defined h (label0ToSym symName (.loc ctrl.fnIdx info.lbl)) := by
        rw [hinv.ctrl_fn]; exact hdef_lbl
      obtain ⟨j_lbl, _, hjmp_adr⟩ := defined_labelAddr_eq hu hjmp_def
      refine x64Scalar_gprSpec.jmp_spec hinf_j hjmp_adr fun s'' hfr_jmp hm'' => ?_
      have hfr'' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s'' σ' :=
        fnFrameInv0_of_eq hfr' hfr_jmp (by simp [x64Scratch])
          (fun r hr => calleeSaved_not_in_rsp_scratch r hr ∘ List.mem_cons_of_mem _) hm''
      have htgts := hJ argv mCurMem hwp s'' σ' hfr'' hesc' htup'
      change Eventually (x64ScalarMach.step h) (fnPost0 h rs Q X s0 ra0 n nX Rf)
        ⟨s'', x64ScalarMach.addrOf h j_lbl⟩
      rw [← hjmp_adr, hinv.ctrl_fn]
      exact htgts
    have hstJ_vsl : st0Clean.vslot = st.vslot := by
      dsimp only [st0Clean, regaPrependLbl0]; split <;> rfl
    obtain ⟨_, _, htgts_eq, htgts_len, htgts_nd, _, _, hinfo_nxt_ms, htgts_lt, _, hov_lt,
      htgts_disj⟩ := hinfo_ok
    have hmax_step : stClean.maxSlots.toNat ≤ ns.toNat := by
      have h1 := regaRunAux0_step_prefix 1 fuel ctx fnIdx fnMaxJump preRes nextSc preSt
        [curPre] pw₂ seenJnz st ctrl [cur] w₂ [mCur] m₂
        (by rw [List.map_singleton, hnd]; dsimp only [workNodeCount0, nodeCount0])
        (by rw [List.map_cons] at hfuel; dsimp only [workNodeCount0] at hfuel
            have := nodeCount0_pos cur.node; omega)
        rfl rfl (by simpa only [List.singleton_append] using hinv)
      dsimp only at h1
      have hm1 := h1.2.2.1
      simp only [List.singleton_append] at hm1
      change (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] } ctrl
        [cur]).1.maxSlots.toNat ≤ _ at hm1
      rw [hrun1, hns_eq] at hm1
      exact hm1
    have hσ_len : σ.length = ns.toNat := hfr.1
    cases args with
    | nil =>
      have hpts_len0 : info.pts.length = 0 := hc_specs.1
      have htgts_nil : info.tgts = [] :=
        List.eq_nil_of_length_eq_zero (by rw [htgts_len, hpts_len0])
      have hstJ_eq : stJ.revDirs = [.jmp (.loc ctrl.fnIdx info.lbl)] := by
        dsimp only [stJ, emitJump0]; rw [← hinfo_lbl]
      rw [hstJ_eq] at hprog_j
      have htup_nil : TupInSlots0 σ info.tgts info.pts argv := by
        rw [htgts_nil]; exact tupInSlots0_nil info.pts argv hpts_len0
      exact h_jmp_run s σ _ hfr hesc_outer0 htup_nil hprog_j
    | cons a rest =>
      cases rest with
      | nil =>
        have hpts_len1 : info.pts.length = 1 := hc_specs.1
        rcases htgts_s : info.tgts with _ | ⟨s_tgt, tgt_rest⟩
        · rw [htgts_s] at htgts_len; simp at htgts_len; omega
        · cases tgt_rest with
          | cons _ _ => rw [htgts_s] at htgts_len; simp at htgts_len; omega
          | nil =>
            obtain ⟨w0, hw0⟩ : ∃ w0, tupToCanon64s info.pts argv = [w0] := by
              cases hL : tupToCanon64s info.pts argv with
              | nil =>
                have hlenL := congrArg List.length hL
                rw [tupToCanon64s_length, hpts_len1] at hlenL; cases hlenL
              | cons w0 tl =>
                cases tl with
                | nil => exact ⟨w0, rfl⟩
                | cons _ _ =>
                  have hlenL := congrArg List.length hL
                  rw [tupToCanon64s_length, hpts_len1] at hlenL; cases hlenL
            rw [hw0] at hvals
            have hst_ms_le : st.maxSlots.toNat ≤ ns.toNat := by
              have hms_eq : stClean.maxSlots = st.maxSlots := by
                dsimp only [stClean, emitJump0, emitJumpOne0, st0Clean, regaPrependLbl0]
                split <;> rfl
              rw [← hms_eq]; exact hmax_step
            have hs_lt_σ : s_tgt.toNat < σ.length := by
              rw [hσ_len]
              have := htgts_lt s_tgt (by rw [htgts_s]; simp)
              omega
            have hstJ_eq : stJ.revDirs = .jmp (.loc ctrl.fnIdx info.lbl) ::
                (emitSlotMem0 false .rax s_tgt [] ++
                  emitLoadArg0 .rax a cur.venv st.vslot []) := by
              dsimp only [stJ, emitJump0, emitJumpOne0, emitJumpOneDir0, arrGetLL0]
              rw [← hinfo_lbl, htgts_eq, htgts_s, hstJ_vsl]
              dsimp only [emitJumpOneStore0]
              rw [(emitSlotMem0_acc false .rax s_tgt
                (emitLoadArg0 .rax a cur.venv st.vslot [])).1]
            rw [hstJ_eq, emitFwd0_cons, emitFwd0_append, toAmd64Program_append,
              toAmd64Program_append] at hprog_j
            have hld := emitLoadArg0_spec (symName := symName) (h := h)
              (k := k + (if cur.lblId = 0 then 0 else 1))
              (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
              .rax (by decide) a cur.venv st.vslot hvals.1 (fnFrameInv0_mem_slots hfr)
            refine hld hprog_j.append.1.append.1 fun s1 ⟨hr1, hm1⟩ hfr1 => ?_
            have hfr1' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s1 σ :=
              fnFrameInv0_of_eq hfr hfr1 (by simp) (fun r hr he =>
                calleeSaved_not_mem_scratchAndAbi r hr (by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
                  rcases he with rfl | rfl <;> simp [x64ScratchAndAbi]))
                hm1
            have hst := emitSlotMem0_st_spec (symName := symName) (h := h)
              (k := k + (if cur.lblId = 0 then 0 else 1) +
                (toAmd64Program symName
                  (emitFwd0 (emitLoadArg0 .rax a cur.venv st.vslot []))).length)
              (post := fnPost0 h rs Q X s0 ra0 n nX Rf) .rax (by decide) s_tgt hs_lt_σ
              (fnFrameInv0_mem_slots hfr1')
            refine hst hprog_j.append.1.append.2 fun s2 hm2 hfr2 => ?_
            let σ2 := σ.set s_tgt.toNat w0
            have hfr2' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s2 σ2 := by
              obtain ⟨hlen1, hrsp1, hcs1, _⟩ := hfr1'
              have hrsp2 : s2.regs.get64 .rsp = s1.regs.get64 .rsp := hfr2.1 .rsp (by simp)
              refine ⟨by simp [σ2, hlen1], hrsp2.trans hrsp1,
                fun r hr => (hfr2.1 r (fun he => calleeSaved_not_in_rsp_scratch r hr
                  (by simp at he; subst he; simp))).trans (hcs1 r hr), ?_⟩
              rw [hr1, ← hrsp2] at hm2
              exact fnFrameInv0_mem_of_slots hm2
            have hesc2 : EscOuterAgree0 preRes.escaped st.vslot info outerVs σ2 := by
              refine escOuterAgree0_mem_congr List.length_set (fun idx hi hesc hsl => ?_)
                hesc_outer0
              have hne : s_tgt.toNat ≠ (arrGetU0 st.vslot (info.outerVenv[idx]'hi)).toNat := by
                intro heq
                have hnd_u : (info.outerVenv[idx]'hi).toNat < info.outerNextVid.toNat :=
                  hov_lt _ (List.getElem_mem hi)
                have heq32 := htgts_disj s_tgt (by rw [htgts_s]; simp)
                  (info.outerVenv[idx]'hi).toNat hnd_u hesc
                  (by rw [UInt32.ofNat_toNat]; exact List.getElem_mem hi)
                rw [UInt32.ofNat_toNat] at heq32
                exact heq32 (u32_ext7 heq.symm)
              exact List.getElem_set_ne hne (by rw [List.length_set]; exact hsl)
            have htup2 : TupInSlots0 σ2 info.tgts info.pts argv := by
              rw [htgts_s]
              refine tupInSlots0_singleton_of_eq (by simp [σ2, hs_lt_σ]) info.pts argv
                hpts_len1 ?_
              simp only [σ2, List.getElem_set_self, hw0]; rfl
            exact h_jmp_run s2 σ2 _ hfr2' hesc2 htup2 (by
              simpa only [List.length_append, Nat.add_assoc, emitFwd0,
                List.reverse_singleton] using hprog_j.append.2)
      | cons b rest' =>
        have hlen_args : (a :: b :: rest').length = info.pts.length := hc_specs.1.symm
        have hvals_len : (tupToCanon64s info.pts argv).length = (a :: b :: rest').length := by
          rw [tupToCanon64s_length, hlen_args]
        have hstJ_eq : stJ.revDirs = .jmp (.loc ctrl.fnIdx info.lbl) ::
            (jumpCopyLoop0 info.tgts cur.nextSlot [] ++
              jumpStageLoop0 (a :: b :: rest') cur.nextSlot cur.venv st.vslot []) := by
          dsimp only [stJ, emitJump0, emitJumpMulti0, arrGetLL0]
          rw [← hinfo_lbl, htgts_eq, hstJ_vsl,
            (jumpCopyLoop0_acc info.tgts cur.nextSlot _).1,
            (jumpStageLoop0_acc (a :: b :: rest') cur.nextSlot cur.venv st.vslot _).1]
        have hmax_multi : (stJ.maxSlots).toNat ≤ ns.toNat := by
          dsimp only [stClean, emitJump0, emitJumpMulti0] at hmax_step
          have hns_st : stJ.maxSlots = stClean.maxSlots := rfl
          rw [hns_st]; exact hmax_step
        have harg_bd : (a :: b :: rest').length ≤ fnMaxJump := by
          have hm := hinv.maxJump_bd
          rw [List.map_cons, hnd] at hm; dsimp only [workMaxJumpArity0, maxJumpArity0] at hm
          omega
        have hsum32 : cur.nextSlot.toNat + (a :: b :: rest').length < 2 ^ 31 := by
          have := hinv.preRes_uses_lt_bd
          have := hinv.maxBd_lt
          omega
        have htmp_bd : cur.nextSlot.toNat + (a :: b :: rest').length ≤ ns.toNat := by
          have h1 : (stJ.maxSlots).toNat = max (st0Clean.maxSlots.toNat)
              ((cur.nextSlot + argLenU0 (a :: b :: rest') 0).toNat) := by
            dsimp only [stJ, emitJump0, emitJumpMulti0]; rw [u32Max0_toNat]
          have hlen_lt32 : (a :: b :: rest').length < 2 ^ 32 := by omega
          have hsum_eq : (cur.nextSlot + argLenU0 (a :: b :: rest') 0).toNat =
              cur.nextSlot.toNat + (a :: b :: rest').length := by
            rw [UInt32.toNat_add, argLenU0_eq_of_lt hlen_lt32, Nat.mod_eq_of_lt (by omega)]
          rw [hsum_eq] at h1
          omega
        have h32_multi : cur.nextSlot.toNat + (a :: b :: rest').length < 2 ^ 32 := by omega
        have hdisj_args : ∀ x ∈ (a :: b :: rest'), ∀ idx, x = .var idx →
            (arrGetU0 st.vslot (listGetU32 cur.venv idx)).toNat < cur.nextSlot.toNat := by
          intro x hx idx heq
          have hlv := hlive_args x hx idx heq
          have hvid_lt : (listGetU32 cur.venv idx).toNat < st.nextVid.toNat := by
            apply hvlt
            rw [listGetU32_eq_listGetD, listGetD_eq_getElem7 _ _ _ (hargs_ok x hx idx heq)]
            exact List.getElem_mem _
          have := hlive _ hvid_lt (by simpa [UInt32.ofNat_toNat] using hlv)
          simpa [UInt32.ofNat_toNat] using this.1
        rw [hstJ_eq, emitFwd0_cons, emitFwd0_append, toAmd64Program_append,
          toAmd64Program_append] at hprog_j
        have hstage := jumpStageLoop0_spec (symName := symName) (h := h) (st := st) (cur := cur)
          (G := Eq mCurMem ⋆ x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
            region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf)
          (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
          (a :: b :: rest') (k + (if cur.lblId = 0 then 0 else 1)) cur.nextSlot
          (tupToCanon64s info.pts argv) σ s hvals_len.symm (by omega) h32_multi hvals hdisj_args
          (fnFrameInv0_mem_slots hfr)
        refine hstage hprog_j.append.1.append.1 fun s1 ⟨σ1, hσ1, hlow1, hst_vals1, hmem1⟩ hfr1 => ?_
        have hfr1' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s1 σ1 := by
          obtain ⟨hlen0, hrsp0, hcs0, _⟩ := hfr
          have hrsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp :=
            hfr1.1 .rsp rsp_not_mem_scratchAndAbi
          refine ⟨hσ1.trans hlen0, hrsp1.trans hrsp0,
            fun r hr => (hfr1.1 r (calleeSaved_not_mem_scratchAndAbi r hr)).trans (hcs0 r hr), ?_⟩
          exact fnFrameInv0_mem_of_slots hmem1
        have htgts_lt_tb : ∀ t ∈ info.tgts, t.toNat < cur.nextSlot.toNat := fun t ht =>
          Nat.lt_of_lt_of_le (htgts_lt t ht) hnxt_le
        have hcopy := jumpCopyLoop0_spec (symName := symName) (h := h)
          (G := Eq mCurMem ⋆ x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
            region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf)
          (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
          info.tgts
          (k + (if cur.lblId = 0 then 0 else 1) + (toAmd64Program symName
            (emitFwd0 (jumpStageLoop0 (a :: b :: rest') cur.nextSlot cur.venv st.vslot []))).length)
          cur.nextSlot σ1 s1 htgts_nd htgts_lt_tb
          (by rw [hσ1, hσ_len, htgts_len, ← hlen_args]; exact htmp_bd)
          (by rw [htgts_len, ← hlen_args]; exact h32_multi)
          (fnFrameInv0_mem_slots hfr1')
        refine hcopy hprog_j.append.1.append.2 fun s2 ⟨σ2, hσ2, hpres2, htgts2, hmem2⟩ hfr2 => ?_
        have hfr2' : FnFrameInv0 ns s0 ra0 n Rf mCurMem s2 σ2 := by
          obtain ⟨hlen1, hrsp1, hcs1, _⟩ := hfr1'
          have hrsp2 : s2.regs.get64 .rsp = s1.regs.get64 .rsp :=
            hfr2.1 .rsp rsp_not_mem_scratchAndAbi
          refine ⟨hσ2.trans hlen1, hrsp2.trans hrsp1,
            fun r hr => (hfr2.1 r (calleeSaved_not_mem_scratchAndAbi r hr)).trans (hcs1 r hr), ?_⟩
          exact fnFrameInv0_mem_of_slots hmem2
        have hesc2 : EscOuterAgree0 preRes.escaped st.vslot info outerVs σ2 := by
          refine escOuterAgree0_mem_congr (hσ2.trans hσ1) (fun idx hi hesc hsl => ?_)
            hesc_outer0
          have hmem_ov : info.outerVenv[idx]'hi ∈ info.outerVenv := List.getElem_mem hi
          have hmem_drop : info.outerVenv[idx]'hi ∈ cur.venv.drop pLen := by
            rw [hov]; exact hmem_ov
          have hmem_cv : info.outerVenv[idx]'hi ∈ cur.venv := List.mem_of_mem_drop hmem_drop
          have hvid_lt : (info.outerVenv[idx]'hi).toNat < st.nextVid.toNat := hvlt _ hmem_cv
          have hslot_lt :
              (arrGetU0 st.vslot (info.outerVenv[idx]'hi)).toNat < cur.nextSlot.toNat := by
            have hlv : LiveInTask0 preRes.escaped preSt st curPre cur
                (info.outerVenv[idx]'hi).toNat := Or.inl ⟨hesc, by
              simpa only [UInt32.ofNat_toNat] using hmem_cv⟩
            have := hlive _ hvid_lt hlv
            simpa only [UInt32.ofNat_toNat] using this.1
          have hnt : ∀ t ∈ info.tgts,
              t.toNat ≠ (arrGetU0 st.vslot (info.outerVenv[idx]'hi)).toNat := by
            intro t ht heq
            have hnd_u : (info.outerVenv[idx]'hi).toNat < info.outerNextVid.toNat :=
              hov_lt _ hmem_ov
            have heq32 := htgts_disj t ht (info.outerVenv[idx]'hi).toNat hnd_u hesc
              (by rw [UInt32.ofNat_toNat]; exact hmem_ov)
            rw [UInt32.ofNat_toNat] at heq32
            exact heq32 (u32_ext7 heq.symm)
          exact (hpres2 _ hnt (hσ1 ▸ hsl)).trans (hlow1 _ hslot_lt hsl)
        have htup2 : TupInSlots0 σ2 info.tgts info.pts argv := by
          refine tupInSlots0_of_list argv htgts_len fun j hj => ?_
          obtain ⟨hsl2, hs1, heq2⟩ := htgts2 j (htgts_len ▸ hj)
          have hst1 := hst_vals1 j (by rw [tupToCanon64s_length]; exact hj)
          refine ⟨hsl2, heq2.trans hst1⟩
        exact h_jmp_run s2 σ2 _ hfr2' hesc2 htup2 (by
          simpa only [List.length_append, Nat.add_assoc, emitFwd0,
            List.reverse_singleton] using hprog_j.append.2)

theorem stepRet0_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {vs' : List Arg0} {k : Nat}
    {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = .ret vs')
    (hrs_len : rs.length ≤ 7) (hctx_rs : ctx.curRs = rs)
    (hframe_le : x64FrameSize ns.toNat ≤ n) (hn_bd : n + 8 ≤ 2 ^ 64)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
        ctrl [cur]).1.revDirs) [])).IsInfixAt (x64ScalarMach.prog h) k)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hwp : wp0 Γ symName rs vs ls Q X cur.node mCurMem)
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ)
    (hag : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ) :
    x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨_, _, hvlen, _, _, _, _, hwf, _, _, _, _, _, _, _, _, _⟩ := hcur_ok
  rw [hnd] at hwf
  have hcargs : checkArgs0 mCur.vT rs vs' = true := by
    cases hwf; rwa [← hctx_rs]
  rw [hnd, wp0_ret] at hwp
  cases hev : evalArgs0Ty vs (ty0ListToTy rs) vs' with
  | none => rw [hev] at hwp; exact False.elim hwp
  | some rvs =>
    rw [hev] at hwp
    have hargs_ok : ∀ a ∈ vs', ∀ idx, a = .var idx → idx.toNat < cur.venv.length := by
      have hva := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at hva; exact hva
    have hlive : ∀ a ∈ vs', ∀ idx, a = .var idx →
        LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
      taskMetaOk0_args_live hinv (fun a ha idx heq => by
        rw [hnd]; exact nodeArgsUses0_pos_lin_term (heq ▸ ha)) hargs_ok
    have hvals := argsSlotVal64_of_evalArgs0Ty hcargs hag hev hlive
    have hvs_len : vs'.length = rs.length := (checkArgs0_spec hcargs).1.symm
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    let stClean := stepRet0 vs' cur st0Clean
    have hrun_rev :
        (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
          ctrl [cur]).1.revDirs = stClean.revDirs := by
      have hd := regaRunAux0_step_once (fuel := (1 : UInt32)) (esc := preRes.escaped)
        (st := { st with revDirs := [] }) (ctrl := ctrl) (cur := cur) (rest := []) (by decide)
      dsimp only at hd
      have hst_eq : regaStep0 preRes.escaped cur st0Clean ctrl [] =
          LoopStep0.mk stClean ctrl [] := by
        dsimp only [regaStep0]; rw [hnd]; dsimp only [regaStepCtrl0]; rw [hnd]
      rw [hd, hst_eq]; dsimp only; rw [regaRunAux0_nil_eq]
    let dLoad := loadRegArgs0 (LoadCfg0.mk true false cur.venv st.vslot) [] vs' 0 []
    obtain ⟨hload_acc, hload_nz⟩ :=
      loadRegArgs0_acc (LoadCfg0.mk true false cur.venv st.vslot) [] vs' 0 st0Clean.revDirs
    have hstClean_vsl : st0Clean.vslot = st.vslot := by
      dsimp only [st0Clean, regaPrependLbl0]; split <;> rfl
    have hstClean_eq :
        stClean.revDirs = .ret :: (.spAdd false 0 :: (dLoad ++ st0Clean.revDirs)) := by
      dsimp only [stClean, stepRet0, pushDImm0]
      rw [hstClean_vsl, hload_acc]; rfl
    have hpatch_eq :
        patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
            ctrl [cur]).1.revDirs) [] =
        patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 st0Clean.revDirs) [] ++
          (emitFwd0 dLoad ++
            emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) []) ++
            emitFwd0 [.ret]) := by
      have hlast : patchEpilogues0 (x64FrameSizeU0 ns) [.ret] [] = [.ret] := by
        rw [patchEpilogues0_eq]; rfl
      rw [hrun_rev, hstClean_eq, emitFwd0_cons, patchEpilogues0_append,
        patchEpilogues0_spZero_cons, patchEpilogues0_prepend _ hload_nz]
      dsimp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append]
      rw [hlast]
      change patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 st0Clean.revDirs) [] ++
        emitFwd0 dLoad ++ emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) []) ++ [.ret] = _
      simp only [List.append_assoc]; rfl
    rw [hpatch_eq, toAmd64Program_append, toAmd64Program_append, toAmd64Program_append] at hcode
    refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns)
      (toAmd64Program symName (emitFwd0 dLoad) ++
        toAmd64Program symName (emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) [])) ++
        toAmd64Program symName (emitFwd0 [.ret])) s (fnPost0 h rs Q X s0 ra0 n nX Rf)
      hu hcode fun _ hprog_ret => ?_
    have hld := loadRegArgs0_spec (symName := symName) (h := h)
      (k := k + (if cur.lblId = 0 then 0 else 1))
      (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
      (LoadCfg0.mk true false cur.venv st.vslot) [] vs' 0
      (fun _ => rfl) (by simp [hvs_len, hrs_len])
      (fun h => by cases h) hvals (fnFrameInv0_mem_slots hfr)
    refine hld hprog_ret.append.1.append.1 fun s1 ⟨hm1, hregs1⟩ hfr1 => ?_
    have hrsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp :=
      hfr1.1 .rsp rsp_not_mem_scratchAndAbi
    have hcs1 : ∀ r ∈ x64Frame.calleeSaved, s1.regs.get64 r = s0.regs.get64 r := fun r hr =>
      (hfr1.1 r (calleeSaved_not_mem_scratchAndAbi r hr)).trans (hfr.2.2.1 r hr)
    have hret1 : x64ScalarTarget.RetsIn rvs s1 := by
      refine (retsIn_ty0_iff hrs_len rvs s1).mpr (tupAbiHolds0_of_regs true 0 rs rvs s1 ?_)
      intro j hj
      have h' := hregs1 j (hvs_len ▸ hj) (by rw [tupToCanon64s_length]; exact hj)
      simpa only [UInt32.toNat_zero, Nat.zero_add] using h'
    have hmem1_reg : s1.dmem =⋆
        x64ScalarFramePreds.Saved (s1.regs.get64 .rsp +
          BitVec.ofNat 64 (x64FrameSize ns.toNat)) ra0 ns.toNat ⋆
        region (s1.regs.get64 .rsp) (8 * ns.toNat) ⋆
        (Eq mCurMem ⋆ region (s0.regs.get64 .rsp - BitVec.ofNat 64 n)
          (n - x64FrameSize ns.toNat) ⋆ Rf) := by
      have hsp1_eq : s1.regs.get64 .rsp = s0.regs.get64 .rsp -
          BitVec.ofNat 64 (x64FrameSize ns.toNat) := hrsp1.trans hfr.2.1
      have hsp_rec : s1.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns.toNat) =
          s0.regs.get64 .rsp := by rw [hsp1_eq, BitVec.sub_add_cancel]
      rw [hsp_rec]
      have h1 : (array64 (s.regs.get64 .rsp) σ) = array64 (s1.regs.get64 .rsp) σ := by rw [hrsp1]
      have h8 : 8 * σ.length ≤ 2 ^ 64 := by
        rw [hfr.1]; have := x64FrameSize_lt_pow64 ns; have := x64FrameSize_ge ns.toNat; omega
      have hmem1' : (s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ (Eq mCurMem ⋆
          x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
          region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆
          Rf)) := by
        rw [hm1, ← h1]; exact sep_cast (fnFrameInv0_mem_entry hfr) (by ac_rfl)
      have hmem1_r := sep_mono (P := array64 (s1.regs.get64 .rsp) σ)
        (P' := region (s1.regs.get64 .rsp) (8 * σ.length)) (fun _ hf => array64_region h8 hf)
        hmem1'
      rw [hfr.1] at hmem1_r
      exact sep_cast hmem1_r (by ac_rfl)
    have hepi := emitSpAdj0_epilogue_spec (symName := symName) (h := h)
      (k := k + (if cur.lblId = 0 then 0 else 1) +
        (toAmd64Program symName (emitFwd0 dLoad)).length)
      (post := fnPost0 h rs Q X s0 ra0 n nX Rf) ns hmem1_reg
    refine hepi hprog_ret.append.1.append.2 fun s2 ⟨hrsp2, hm2⟩ hfr2 => ?_
    have hrsp2_eq : s2.regs.get64 .rsp = s0.regs.get64 .rsp := by
      rw [hrsp2, hrsp1, hfr.2.1, BitVec.sub_add_cancel]
    have hcs2 : ∀ r ∈ x64Frame.calleeSaved, s2.regs.get64 r = s0.regs.get64 r := fun r hr =>
      (hfr2.1 r (calleeSaved_not_in_rsp_scratch r hr)).trans (hcs1 r hr)
    have hret2 : x64ScalarTarget.RetsIn rvs s2 := by
      refine (retsIn_ty0_iff hrs_len rvs s2).mpr ?_
      refine tupAbiHolds0_frame (fun r hr => hfr2.1 r hr)
        (fun j _ => abiRegAt0_not_in_rsp_scratch true _) ((retsIn_ty0_iff hrs_len rvs s1).mp hret1)
    have hmem2_ret :
        s2.dmem =⋆ x64ScalarFramePreds.RetAddr (s2.regs.get64 .rsp) ra0 ⋆
          (Eq mCurMem ⋆ region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) n ⋆ Rf) := by
      rw [hrsp2_eq]
      have hsp1_eq : s1.regs.get64 .rsp = s0.regs.get64 .rsp -
          BitVec.ofNat 64 (x64FrameSize ns.toNat) := hrsp1.trans hfr.2.1
      rw [hsp1_eq] at hm2
      have h_entry : s2.dmem =⋆ Eq mCurMem ⋆
          x64ScalarTarget.Entry (s0.regs.get64 .rsp) ra0 n ⋆ Rf :=
        epilogue_reconstruct_entry (hle := hframe_le) (hn := hn_bd) (sep_cast hm2 (by ac_rfl))
      have he_eq : x64ScalarTarget.Entry (s0.regs.get64 .rsp) ra0 n =
          (region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) n ⋆
            x64ScalarFramePreds.RetAddr (s0.regs.get64 .rsp) ra0) := rfl
      rw [he_eq] at h_entry
      exact sep_cast h_entry (by ac_rfl)
    have hret_dir :
        (toAmd64Program symName (emitFwd0 [.ret])) = x64Frame.ret := rfl
    have hret_inf : x64Frame.ret.IsInfixAt (x64ScalarMach.prog h)
        (k + (if cur.lblId = 0 then 0 else 1) + (toAmd64Program symName (emitFwd0 dLoad)).length +
          (toAmd64Program symName (emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) []))).length) :=
      by simpa only [List.length_append, Nat.add_assoc, hret_dir] using hprog_ret.append.2
    refine x64ScalarTarget.frameSpec.ret_spec hret_inf (by intros; trivial) hmem2_ret
      fun s3 hkg _ hrsp3 hm3 => ?_
    refine Eventually.done _ ?_
    left
    refine ⟨rfl, rvs, mCurMem, hwp, ?_, ?_, ?_⟩
    · refine (retsIn_ty0_iff hrs_len rvs s3).mpr ?_
      refine tupAbiHolds0_frame hkg (fun j _ hm => by
        dsimp only [Isa.frame, x64ScalarTarget, x64Frame] at hm
        exact abiRegAt0_not_in_rsp_scratch true _ hm)
        ((retsIn_ty0_iff hrs_len rvs s2).mp hret2)
    · have hrsp3' : s3.regs.get64 .rsp = s2.regs.get64 .rsp + 8#64 := hrsp3
      refine ⟨fun r hr => ?_, by
        change s3.regs.get64 .rsp = s0.regs.get64 .rsp + 8#64
        rw [hrsp3', hrsp2_eq]⟩
      have hn : r ∉ x64ScalarTarget.frame.sp :: x64ScalarTarget.frame.scratch := fun hm => by
        dsimp only [Isa.frame, x64ScalarTarget, x64Frame] at hm
        exact calleeSaved_not_in_rsp_scratch r hr hm
      exact (hkg r hn).trans (hcs2 r hr)
    · have hm3' : s3.dmem = s2.dmem := hm3
      have h_exit : s3.dmem =⋆ Eq mCurMem ⋆ x64ScalarTarget.Exit (s0.regs.get64 .rsp) n ⋆ Rf := by
        rw [hm3']
        have h_entry : s2.dmem =⋆ Eq mCurMem ⋆
            x64ScalarTarget.Entry (s0.regs.get64 .rsp) ra0 n ⋆ Rf := by
          rw [hrsp2_eq] at hmem2_ret
          have he_eq : x64ScalarTarget.Entry (s0.regs.get64 .rsp) ra0 n =
              (region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) n ⋆
                x64ScalarFramePreds.RetAddr (s0.regs.get64 .rsp) ra0) := rfl
          rw [he_eq]
          exact sep_cast hmem2_ret (by ac_rfl)
        exact epilogue_reconstruct_exit (hn := hn_bd) h_entry
      exact h_exit

theorem stepTail0_run_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {fnSym : Sym0} {as : List Ty0} {args : List Arg0} {isExit : Bool}
    {k : Nat} {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)}
    (hnd : cur.node = if isExit then .exit fnSym as args else .tailCall fnSym as args)
    (hctx_rs : ctx.curRs = rs)
    (hframe_le : x64FrameSize ns.toNat ≤ n) (hn_bd : n + 8 ≤ 2 ^ 64)
    (hsp0 : x64ScalarTarget.frameSpec.spEntry (s0.regs.get64 .rsp))
    (hc_node : NodeContracts0 h symName Γ ctx ns n nX cur.node)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
        ctrl [cur]).1.revDirs) [])).IsInfixAt (x64ScalarMach.prog h) k)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hwp : wp0 Γ symName rs vs ls Q X cur.node mCurMem)
    (hfr : FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ)
    (hag : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ) :
    x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨_, _, hvlen, _, _, _, _, hwf, _, _, _, _, _, _, _, _, _⟩ := hcur_ok
  have ⟨has_le, hcargs⟩ : as.length ≤ 6 ∧ checkArgs0 mCur.vT as args = true := by
    cases isExit <;> simp only [Bool.false_eq_true, ↓reduceIte] at hnd <;> rw [hnd] at hwf <;>
      cases hwf <;> exact ⟨‹_›, ‹_›⟩
  have hev_prop : ∃ argv : Tup Val (ty0ListToTy as),
      evalArgs0Ty vs (ty0ListToTy as) args = some argv ∧
      (if isExit then X (symName fnSym) (ty0ListToTy as) argv mCurMem
       else Γ (symName fnSym) (ty0ListToTy as) (ty0ListToTy rs) argv mCurMem Q X) := by
    cases isExit <;> simp only [Bool.false_eq_true, ↓reduceIte] at hnd ⊢ <;> rw [hnd] at hwp
    · rw [wp0_tailCall] at hwp
      cases h1 : evalArgs0Ty vs (ty0ListToTy as) args <;> rw [h1] at hwp
      · exact False.elim hwp
      · exact ⟨_, rfl, hwp⟩
    · rw [wp0_exit] at hwp
      cases h1 : evalArgs0Ty vs (ty0ListToTy as) args <;> rw [h1] at hwp
      · exact False.elim hwp
      · exact ⟨_, rfl, hwp⟩
  obtain ⟨argv, hev, hsem⟩ := hev_prop
  have hargs_ok : ∀ a ∈ args, ∀ idx, a = .var idx → idx.toNat < cur.venv.length := by
    have hva : nodeArgsInVenv0 cur.venv.length cur.node := by
      cases isExit <;> simp only [Bool.false_eq_true, ↓reduceIte] at hnd <;>
        rw [hnd] at hwf ⊢ <;> (have h' := wfNode0_nodeArgsInVenv0 hwf; rw [← hvlen] at h'; exact h')
    cases isExit <;> simp only [Bool.false_eq_true, ↓reduceIte] at hnd <;> rw [hnd] at hva <;>
      exact hva
  have hlive : ∀ a ∈ args, ∀ idx, a = .var idx →
      LiveInTask0 preRes.escaped preSt st curPre cur (listGetU32 cur.venv idx).toNat :=
    taskMetaOk0_args_live hinv (fun a ha idx heq => by
      cases isExit <;> simp only [Bool.false_eq_true, ↓reduceIte] at hnd <;> rw [hnd] <;>
        exact nodeArgsUses0_pos_lin_term (heq ▸ ha)) hargs_ok
  have hvals := argsSlotVal64_of_evalArgs0Ty hcargs hag hev hlive
  have hc_specs := checkArgs0_spec hcargs
  have hargs_len : args.length = as.length := hc_specs.1.symm
  let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
  let stClean := stepTail0 fnSym as args cur st0Clean
  have hrun_rev :
      (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
        ctrl [cur]).1.revDirs = stClean.revDirs := by
    have hd := regaRunAux0_step_once (fuel := (1 : UInt32)) (esc := preRes.escaped)
      (st := { st with revDirs := [] }) (ctrl := ctrl) (cur := cur) (rest := []) (by decide)
    dsimp only at hd
    have hst_eq : regaStep0 preRes.escaped cur st0Clean ctrl [] =
        LoopStep0.mk stClean ctrl [] := by
      dsimp only [regaStep0, regaStepCtrl0]; rw [hnd]; cases isExit <;> rfl
    rw [hd, hst_eq]; dsimp only; rw [regaRunAux0_nil_eq]
  let dLoad := loadRegArgs0 (LoadCfg0.mk false true cur.venv st.vslot) as args 0 []
  obtain ⟨hload_acc, hload_nz⟩ :=
    loadRegArgs0_acc (LoadCfg0.mk false true cur.venv st.vslot) as args 0 st0Clean.revDirs
  have hstClean_vsl : st0Clean.vslot = st.vslot := by
    dsimp only [st0Clean, regaPrependLbl0]; split <;> rfl
  have hstClean_eq : stClean.revDirs =
      .jmp (.sym fnSym) :: (.spAdd false 0 :: (dLoad ++ st0Clean.revDirs)) := by
    dsimp only [stClean, stepTail0, pushDImm0]
    rw [hstClean_vsl, hload_acc]; rfl
  have hpatch_eq :
      patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped { st with revDirs := [] }
          ctrl [cur]).1.revDirs) [] =
      patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 st0Clean.revDirs) [] ++
        (emitFwd0 dLoad ++
          emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) []) ++
          emitFwd0 [.jmp (.sym fnSym)]) := by
    have hlast : patchEpilogues0 (x64FrameSizeU0 ns) [.jmp (.sym fnSym)] [] =
        [.jmp (.sym fnSym)] := by
      rw [patchEpilogues0_eq]; rfl
    rw [hrun_rev, hstClean_eq, emitFwd0_cons, patchEpilogues0_append,
      patchEpilogues0_spZero_cons, patchEpilogues0_prepend _ hload_nz]
    dsimp only [emitFwd0, List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [hlast]
    change patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 st0Clean.revDirs) [] ++
      emitFwd0 dLoad ++ emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) []) ++
      [.jmp (.sym fnSym)] = _
    simp only [List.append_assoc]; rfl
  rw [hpatch_eq, toAmd64Program_append, toAmd64Program_append, toAmd64Program_append] at hcode
  refine regaPrependLbl0_run cur st ctrl (x64FrameSizeU0 ns)
    (toAmd64Program symName (emitFwd0 dLoad) ++
      toAmd64Program symName (emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) [])) ++
      toAmd64Program symName (emitFwd0 [.jmp (.sym fnSym)])) s (fnPost0 h rs Q X s0 ra0 n nX Rf)
    hu hcode fun _ hprog_t => ?_
  have hld := loadRegArgs0_spec (symName := symName) (h := h)
    (k := k + (if cur.lblId = 0 then 0 else 1))
    (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
    (LoadCfg0.mk false true cur.venv st.vslot) as args 0
    (vals := tupToCanon64s as argv)
    (fun h => by cases h) (by simp [hargs_len, has_le])
    (fun _ => ⟨hargs_len.symm, fun j hj1 hj2 => tupToCanon64s_canon_ok as argv j hj1 hj2⟩)
    hvals (fnFrameInv0_mem_slots hfr)
  refine hld hprog_t.append.1.append.1 fun s1 ⟨hm1, hregs1⟩ hfr1 => ?_
  have hrsp1 : s1.regs.get64 .rsp = s.regs.get64 .rsp :=
    hfr1.1 .rsp rsp_not_mem_scratchAndAbi
  have hcs1 : ∀ r ∈ x64Frame.calleeSaved, s1.regs.get64 r = s0.regs.get64 r := fun r hr =>
    (hfr1.1 r (calleeSaved_not_mem_scratchAndAbi r hr)).trans (hfr.2.2.1 r hr)
  have hargs1 : x64ScalarTarget.ArgsIn argv s1 := by
    refine (argsIn_ty0_iff has_le argv s1).mpr (tupAbiHolds0_of_regs false 0 as argv s1 ?_)
    intro j hj
    have h' := hregs1 j (hargs_len ▸ hj) (by rw [tupToCanon64s_length]; exact hj)
    simpa only [UInt32.toNat_zero, Nat.zero_add] using h'
  have hmem1_reg : s1.dmem =⋆
      x64ScalarFramePreds.Saved (s1.regs.get64 .rsp +
        BitVec.ofNat 64 (x64FrameSize ns.toNat)) ra0 ns.toNat ⋆
      region (s1.regs.get64 .rsp) (8 * ns.toNat) ⋆
      (Eq mCurMem ⋆ region (s0.regs.get64 .rsp - BitVec.ofNat 64 n)
        (n - x64FrameSize ns.toNat) ⋆ Rf) := by
    have hsp1_eq : s1.regs.get64 .rsp = s0.regs.get64 .rsp -
        BitVec.ofNat 64 (x64FrameSize ns.toNat) := hrsp1.trans hfr.2.1
    have hsp_rec : s1.regs.get64 .rsp + BitVec.ofNat 64 (x64FrameSize ns.toNat) =
        s0.regs.get64 .rsp := by rw [hsp1_eq, BitVec.sub_add_cancel]
    rw [hsp_rec]
    have h1 : (array64 (s.regs.get64 .rsp) σ) = array64 (s1.regs.get64 .rsp) σ := by rw [hrsp1]
    have h8 : 8 * σ.length ≤ 2 ^ 64 := by
      rw [hfr.1]; have := x64FrameSize_lt_pow64 ns; have := x64FrameSize_ge ns.toNat; omega
    have hmem1' : (s1.dmem =⋆ array64 (s1.regs.get64 .rsp) σ ⋆ (Eq mCurMem ⋆
        x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
        region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf)) := by
      rw [hm1, ← h1]; exact sep_cast (fnFrameInv0_mem_entry hfr) (by ac_rfl)
    have hmem1_r := sep_mono (P := array64 (s1.regs.get64 .rsp) σ)
      (P' := region (s1.regs.get64 .rsp) (8 * σ.length)) (fun _ hf => array64_region h8 hf)
      hmem1'
    rw [hfr.1] at hmem1_r
    exact sep_cast hmem1_r (by ac_rfl)
  have hepi := emitSpAdj0_epilogue_spec (symName := symName) (h := h)
    (k := k + (if cur.lblId = 0 then 0 else 1) +
      (toAmd64Program symName (emitFwd0 dLoad)).length)
    (post := fnPost0 h rs Q X s0 ra0 n nX Rf) ns hmem1_reg
  refine hepi hprog_t.append.1.append.2 fun s2 ⟨hrsp2, hm2⟩ hfr2 => ?_
  have hrsp2_eq : s2.regs.get64 .rsp = s0.regs.get64 .rsp := by
    rw [hrsp2, hrsp1, hfr.2.1, BitVec.sub_add_cancel]
  have hcs2 : ∀ r ∈ x64Frame.calleeSaved, s2.regs.get64 r = s0.regs.get64 r := fun r hr =>
    (hfr2.1 r (calleeSaved_not_in_rsp_scratch r hr)).trans (hcs1 r hr)
  have hargs2 : x64ScalarTarget.ArgsIn argv s2 := by
    refine (argsIn_ty0_iff has_le argv s2).mpr ?_
    refine tupAbiHolds0_frame (fun r hr => hfr2.1 r hr)
      (fun j _ => abiRegAt0_not_in_rsp_scratch false _) ((argsIn_ty0_iff has_le argv s1).mp hargs1)
  have hmem2_entry :
      s2.dmem =⋆ Eq mCurMem ⋆ x64ScalarTarget.Entry (s0.regs.get64 .rsp) ra0 n ⋆ Rf := by
    have hsp1_eq : s1.regs.get64 .rsp = s0.regs.get64 .rsp -
        BitVec.ofNat 64 (x64FrameSize ns.toNat) := hrsp1.trans hfr.2.1
    rw [hsp1_eq] at hm2
    exact epilogue_reconstruct_entry (hle := hframe_le) (hn := hn_bd) (sep_cast hm2 (by ac_rfl))
  have hjmp_dir : toAmd64Program symName (emitFwd0 [.jmp (.sym fnSym)]) =
      x64Frame.exitJmp (symName fnSym) := rfl
  have hjmp_inf : (x64Frame.exitJmp (symName fnSym)).IsInfixAt (x64ScalarMach.prog h)
      (k + (if cur.lblId = 0 then 0 else 1) + (toAmd64Program symName (emitFwd0 dLoad)).length +
        (toAmd64Program symName (emitFwd0 (emitSpAdj0 false (x64FrameSizeU0 ns) []))).length) :=
    by simpa only [List.length_append, Nat.add_assoc, hjmp_dir] using hprog_t.append.2
  refine x64ScalarTarget.frameSpec.exitJmp_spec hjmp_inf fun s3 hfr3 hm3 => ?_
  have hrsp3 : s3.regs.get64 .rsp = s0.regs.get64 .rsp :=
    (hfr3.1 .rsp (by simp)).trans hrsp2_eq
  have hcs3 : ∀ r ∈ x64Frame.calleeSaved, s3.regs.get64 r = s0.regs.get64 r := fun r hr =>
    (hfr3.1 r (fun hm => calleeSaved_not_in_rsp_scratch r hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      rcases hm with rfl | rfl <;> simp))).trans (hcs2 r hr)
  have hargs3 : x64ScalarTarget.ArgsIn argv s3 := by
    refine (argsIn_ty0_iff has_le argv s3).mpr ?_
    refine tupAbiHolds0_frame (fun r hr => hfr3.1 r hr)
      (fun j _ hm => abiRegAt0_not_in_rsp_scratch false _
        (List.mem_cons_of_mem Reg64.rsp (by
          dsimp only [Isa.frame, x64ScalarTarget, x64Frame] at hm; exact hm)))
      ((argsIn_ty0_iff has_le argv s2).mp hargs2)
  have hmem3 : s3.dmem =⋆ Eq mCurMem ⋆ x64ScalarTarget.Entry (s3.regs.get64 .rsp) ra0 n ⋆ Rf := by
    have hm3' : s3.dmem = s2.dmem := hm3
    rw [hm3', hrsp3]; exact hmem2_entry
  cases isExit
  · simp only [Bool.false_eq_true, ↓reduceIte] at hnd hsem hc_node
    rw [hnd] at hc_node; dsimp only [NodeContracts0] at hc_node; rw [hctx_rs] at hc_node
    obtain ⟨bound, hbd_le, _, hfspec⟩ := hc_node
    have hlifted := Target.FnSpec.mono_stack x64ScalarTarget hfspec hbd_le hn_bd
    have hev_cal := hlifted argv mCurMem Q X hsem s3 ra0 Rf hargs3 (by intros; trivial)
      (show x64ScalarTarget.frameSpec.spEntry (s3.regs.get64 .rsp) from hrsp3 ▸ hsp0) hmem3
    refine eventually_weaken _ _ _ _ ?_ hev_cal
    rintro st (⟨hpc, rets, m', hQ, hrets, hrest, hm'⟩ |
      ⟨sym', cs, xs, m', hX, hdef, hpc, has, hsp', ra', n', F, hnx, hnbd, hra', hm'⟩)
    · left
      refine ⟨hpc, rets, m', hQ, hrets, ?_, ?_⟩
      · refine ⟨fun r hr => (hrest.1 r hr).trans (hcs3 r hr), ?_⟩
        change st.data.regs.get64 .rsp = s0.regs.get64 .rsp + 8#64
        have h2 : st.data.regs.get64 .rsp = s3.regs.get64 .rsp + 8#64 := hrest.2
        rw [h2, hrsp3]
      · have hm'' : (Eq m' ⋆ x64ScalarTarget.Exit (s3.regs.get64 .rsp) n ⋆ Rf) st.data.dmem := hm'
        rw [hrsp3] at hm''; exact hm''
    · right
      exact ⟨sym', cs, xs, m', hX, hdef, hpc, has, hsp', ra', n', F, hnx, hnbd, hra', hm'⟩
  · simp only [↓reduceIte] at hnd hsem hc_node
    rw [hnd] at hc_node; dsimp only [NodeContracts0] at hc_node
    refine Eventually.done _ ?_
    right
    refine ⟨symName fnSym, ty0ListToTy as, argv, mCurMem, hsem, hc_node.2, rfl, hargs3,
      (show x64ScalarTarget.frameSpec.spEntry (s3.regs.get64 .rsp) from hrsp3 ▸ hsp0),
      ra0, n, emp, hc_node.1, hn_bd, by intros; trivial, ?_⟩
    simpa only [sep_assoc, emp_sep] using hmem3

/-- Result type list for a straight-line instruction node (`linCnt0` binder types). -/
@[expose] def linRetTys0 : TFlat0 → List Ty0
  | .let1 op _ _ => [opRetTy0 op]
  | .let2Umulw64 _ _ _ => [.b64, .b64]
  | .load t _ _ => [t]
  | .store _ _ _ _ => []
  | .call _ _ bs _ _ => bs
  | _ => []

theorem linRetTys0_length_le {ctx : LegalCtx0} {vT : List Ty0} {lT : List (List Ty0)}
    {node : TFlat0} (hwf : WfNode0 ctx vT lT node) (hlin : isTerm0 node = false)
    (hnj : ∀ c t e, node ≠ .jnz c t e) (hng : ∀ bs k, node ≠ .group bs k) :
    (linRetTys0 node).length ≤ 7 ∧ (linRetTys0 node).length = (linCnt0 node).toNat := by
  cases node with
  | let1 _ _ _ | load _ _ _ => simp [linRetTys0, linCnt0]
  | let2Umulw64 _ _ _ => simp [linRetTys0, linCnt0]
  | store _ _ _ _ => simp [linRetTys0, linCnt0]
  | call _ _ bs _ _ =>
    have hbs7 : bs.length ≤ 7 := by cases hwf with | call _ hbs7 _ _ _ => exact hbs7
    have hle : bs.length < 2 ^ 32 := by omega
    rw [linRetTys0, linCnt0, tyLenU0_eq_of_lt hle]
    exact ⟨hbs7, rfl⟩
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

theorem legalNextVenv0_eq_pushTys0 {node : TFlat0} {vT : List Ty0}
    (hlin : isTerm0 node = false) (hnj : ∀ c t e, node ≠ .jnz c t e)
    (hng : ∀ bs k, node ≠ .group bs k) :
    legalNextVenv0 node vT = pushTys0 (linRetTys0 node) vT := by
  cases node with
  | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ => rfl
  | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
  | group _ _ => exact absurd rfl (hng _ _)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

private theorem nodeArgsUses0_eq_zero_of_not_in_venv {v nextVid : Nat} {venv : List UInt32}
    {node : TFlat0} (_hv : v < nextVid) (_hnv32 : nextVid ≤ 2 ^ 32)
    (_hvlt : ∀ w ∈ venv, w.toNat < nextVid) (hargs : nodeArgsInVenv0 venv.length node)
    (hlin : isTerm0 node = false) (hnj : ∀ c t e, node ≠ .jnz c t e)
    (hng : ∀ bs k, node ≠ .group bs k) (hnin : UInt32.ofNat v ∉ venv) :
    nodeArgsUses0 (UInt32.ofNat v) venv node = 0 := by
  have ha0 : ∀ a, (∀ idx, a = .var idx → idx.toNat < venv.length) →
      argUses0 (UInt32.ofNat v) venv a = 0 := fun a ha => by
    cases a with
    | immBool _ | immBits _ _ => rfl
    | var idx =>
      dsimp only [argUses0]
      have hne : listGetU32 venv idx ≠ UInt32.ofNat v := fun he => hnin <| by
        rw [← he, listGetU32_eq_listGetD, listGetD_eq_getElem7 _ _ _ (ha idx rfl)]
        exact List.getElem_mem _
      simp [hne]
  have has0 : ∀ xs, (∀ a ∈ xs, ∀ idx, a = .var idx → idx.toNat < venv.length) →
      argsUses0 (UInt32.ofNat v) venv xs = 0 := fun xs hxs => by
    induction xs with
    | nil => rfl
    | cons a rs ih =>
      dsimp only [argsUses0]
      rw [ha0 a (hxs a List.mem_cons_self), ih (fun b hb => hxs b (List.mem_cons_of_mem _ hb))]
  cases hnd : node with
  | let1 _ _ _ | call _ _ _ _ _ =>
    rw [hnd] at hargs; dsimp only [nodeArgsUses0]; exact has0 _ hargs
  | let2Umulw64 _ _ _ | store _ _ _ _ =>
    rw [hnd] at hargs; dsimp only [nodeArgsUses0]; rw [ha0 _ hargs.1, ha0 _ hargs.2]
  | load _ _ _ => rw [hnd] at hargs; dsimp only [nodeArgsUses0]; exact ha0 _ hargs
  | jnz c t e => exact absurd hnd (hnj c t e)
  | group bs k => exact absurd hnd (hng bs k)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
    rw [hnd] at hlin; simp [isTerm0] at hlin

private theorem stepLinear0_work_head_ok (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0)
    (ctrl : CtrlSt0) (rest : List RegaTask0) :
    let ls := stepLinear0 esc cur st ctrl rest
    ls.work.length = rest.length + 1 ∧
    ls.ctrl = ctrl ∧
    let bl := bindRetsN0 esc (linCnt0 cur.node) 0
      (relAndUpdateSt0 esc cur st (emitLinNode0 cur st))
    ls.st = bl.st ∧
    ls.work = RegaTask0.mk 0 (linK0 cur.node) bl.venv cur.lenv bl.free bl.nxt :: rest :=
  ⟨by simp [stepLinear0, stepLinBindPush0, linBindPush0], rfl, rfl, rfl⟩

private theorem regaStep0_lin_unfold (esc : Array Nat) (curPre : PreItem0) (preSt : PreSt0)
    (nextSc : UInt32) (pw₂ : List PreItem0) (st0 : RegaSt0) (ctrl : CtrlSt0) (cur : RegaTask0)
    (w₂ : List RegaTask0) (hpn : curPre.node = cur.node) (hlin : isTerm0 cur.node = false)
    (hnj : ∀ c t e, cur.node ≠ .jnz c t e) (hng : ∀ bs k, cur.node ≠ .group bs k) :
    let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
    let out := preStepPush0 curPre preSt1 nextSc pw₂
    let ls := regaStep0 esc cur st0 ctrl w₂
    let bl := bindRetsN0 esc (linCnt0 cur.node) 0
      (relAndUpdateSt0 esc cur st0 (emitLinNode0 cur st0))
    out.work = PreItem0.mk (linK0 curPre.node)
      (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope :: pw₂ ∧
    ls.st = bl.st ∧ ls.ctrl = ctrl ∧
    ls.work = RegaTask0.mk 0 (linK0 cur.node) bl.venv cur.lenv bl.free bl.nxt :: w₂ := by
  have hst : regaStep0 esc cur st0 ctrl w₂ = stepLinear0 esc cur st0 ctrl w₂ := by
    rcases cur with ⟨lbl, nd, venv, lenv, fr, nxt⟩
    cases nd with
    | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
    | group _ _ => exact absurd rfl (hng _ _)
    | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin
    | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ => rfl
  have hout : (preStepPush0 curPre (preNoteNode0 curPre.scope curPre.venv curPre.node preSt)
      nextSc pw₂).work =
      PreItem0.mk (linK0 curPre.node)
        (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv
          (preNoteNode0 curPre.scope curPre.venv curPre.node preSt)).1
        curPre.scope :: pw₂ := by
    have hlinp : isTerm0 curPre.node = false := hpn ▸ hlin
    rcases curPre with ⟨nd, venv, sc⟩
    cases hnd : nd with
    | jnz _ _ _ => subst hnd; exact absurd hpn.symm (hnj _ _ _)
    | group _ _ => subst hnd; exact absurd hpn.symm (hng _ _)
    | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => subst hnd; simp [isTerm0] at hlinp
    | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
      subst hnd; dsimp only [preStepPush0, isTerm0, preStepLin0, preLinFinish0]; rfl
  rw [hst]
  exact ⟨hout, rfl, rfl, rfl⟩

private theorem linCnt0_le_binderCount0 {ctx : LegalCtx0} {vT : List Ty0} {lT : List (List Ty0)}
    {node : TFlat0} (hwf : WfNode0 ctx vT lT node) (hlin : isTerm0 node = false)
    (hnj : ∀ c t e, node ≠ .jnz c t e) (hng : ∀ bs k, node ≠ .group bs k) :
    (linCnt0 node).toNat ≤ binderCount0 node := by
  cases node with
  | let1 _ _ _ | load _ _ _ =>
    dsimp only [linCnt0, binderCount0]; simp only [UInt32.toNat_one]; omega
  | let2Umulw64 _ _ _ =>
    dsimp only [linCnt0, binderCount0]; rw [show (2 : UInt32).toNat = 2 from rfl]; omega
  | store _ _ _ _ =>
    dsimp only [linCnt0, binderCount0]; rw [UInt32.toNat_zero]; exact Nat.zero_le _
  | call _ _ bs _ _ =>
    have hbs : bs.length ≤ 7 := by cases hwf with | call _ hbs7 _ _ _ => exact hbs7
    dsimp only [linCnt0, binderCount0]
    rw [tyLenU0_eq_of_lt (by omega : bs.length < 2 ^ 32)]
    omega
  | jnz c t e => exact absurd rfl (hnj c t e)
  | group bs k => exact absurd rfl (hng bs k)
  | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin

private theorem relAndUpdateSt0_clean (esc : Array Nat) (cur : RegaTask0)
    (stA stB : RegaSt0) (dA : List Dir0)
    (h1 : stA.nextVid = stB.nextVid) (h2 : stA.maxSlots = stB.maxSlots)
    (h3 : stA.vslot = stB.vslot) (h4 : stA.remUses = stB.remUses) :
    let blA := relAndUpdateSt0 esc cur stA dA
    { blA with st := { blA.st with revDirs := [] } } =
      relAndUpdateSt0 esc cur { stB with revDirs := [] } [] := by
  cases stA; cases stB; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

theorem stepLinear_program_split {symName : Sym0 → Sym} {h : Host} {k : Nat}
    (esc : Array Nat) (cur : RegaTask0) (st : RegaSt0) (ctrl : CtrlSt0) (ns : UInt32)
    (hlin : isTerm0 cur.node = false) (hnj : ∀ c t e, cur.node ≠ .jnz c t e)
    (hng : ∀ bs k, cur.node ≠ .group bs k) (hbd : nodeCount0 cur.node < 2 ^ 31)
    (hcode : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) esc
        { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
      (x64ScalarMach.prog h) k) :
    let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
    let lsC := stepLinear0 esc cur st0Clean ctrl []
    let tK := lsC.work[0]'(by simp [lsC, stepLinear0, stepLinBindPush0, linBindPush0])
    let blZero := bindRetsN0 esc (linCnt0 cur.node) 0
      (relAndUpdateSt0 esc cur { st0Clean with revDirs := [] } [])
    let rK := regaRunAux0 (UInt32.ofNat (nodeCount0 (linK0 cur.node))) esc
      { lsC.st with revDirs := [] } ctrl [tK]
    (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 st0Clean.revDirs) []) ++
      (toAmd64Program symName (emitFwd0 (emitLinNode0 cur { st0Clean with revDirs := [] })) ++
        (toAmd64Program symName (emitFwd0 blZero.st.revDirs) ++
          toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
            (emitFwd0 rK.1.revDirs) [])))).IsInfixAt (x64ScalarMach.prog h) k := by
  intro st0Clean lsC tK blZero rK
  have hnc_eq : nodeCount0 cur.node = nodeCount0 (linK0 cur.node) + 1 := by
    cases hnd : cur.node with
    | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ =>
      dsimp only [nodeCount0, linK0]; omega
    | jnz c t e => exact absurd hnd (hnj c t e)
    | group bs k => exact absurd hnd (hng bs k)
    | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt =>
      rw [hnd] at hlin; simp [isTerm0] at hlin
  have hpos : 0 < (UInt32.ofNat (nodeCount0 cur.node)).toNat := by
    rw [u32_ofNat_toNat_lt10 (by omega), hnc_eq]; omega
  have hsub : UInt32.ofNat (nodeCount0 cur.node) - 1 =
      UInt32.ofNat (nodeCount0 (linK0 cur.node)) := by
    apply u32_ext7
    rw [u32_sub1_toNat7 hpos, u32_ofNat_toNat_lt10 (by omega),
      u32_ofNat_toNat_lt10 (by omega), hnc_eq, Nat.add_sub_cancel]
  have hstep1 := congrArg (fun p => p.1.revDirs)
    (regaRunAux0_step_once (fuel := UInt32.ofNat (nodeCount0 cur.node))
      (esc := esc) (st := { st with revDirs := [] }) (ctrl := ctrl) (cur := cur) (rest := [])
      hpos)
  have hlin_st : regaStep0 esc cur st0Clean ctrl [] = lsC := by
    rcases cur with ⟨lbl, nd, venv, lenv, fr, nxt⟩
    cases nd with
    | jnz _ _ _ => exact absurd rfl (hnj _ _ _)
    | group _ _ => exact absurd rfl (hng _ _)
    | tailCall _ _ _ | jump _ _ | ret _ | exit _ _ _ | hlt => simp [isTerm0] at hlin
    | let1 _ _ _ | let2Umulw64 _ _ _ | load _ _ _ | store _ _ _ _ | call _ _ _ _ _ => rfl
  have hls_eq : lsC.work = [tK] ∧ lsC.ctrl = ctrl :=
    ⟨by dsimp only [lsC, stepLinear0, stepLinBindPush0, linBindPush0]; rfl, rfl⟩
  have hrev_rk := congrArg (fun p => p.1.revDirs) (regaRunAux0_revDirs_append
    (UInt32.ofNat (nodeCount0 (linK0 cur.node))) esc lsC.st ctrl [tK])
  dsimp only at hrev_rk
  rw [hlin_st, hsub, hls_eq.1, hls_eq.2, hrev_rk] at hstep1
  have hr_split :
      lsC.st.revDirs =
        blZero.st.revDirs ++ (emitLinNode0 cur { st0Clean with revDirs := [] } ++
          st0Clean.revDirs) := by
    obtain ⟨hn_acc, _⟩ := emitLinNode0_acc cur st0Clean
    let blA : BindListOut0 := relAndUpdateSt0 esc cur st0Clean (emitLinNode0 cur st0Clean)
    have hbr := bindRetsN0_revDirs esc (linCnt0 cur.node).toNat (linCnt0 cur.node) 0 blA rfl
    have hblA_z : { blA with st := { blA.st with revDirs := [] } } =
        relAndUpdateSt0 esc cur { st0Clean with revDirs := [] } [] :=
      relAndUpdateSt0_clean esc cur st0Clean st0Clean _ rfl rfl rfl rfl
    have hbr_rev : (bindRetsN0 esc (linCnt0 cur.node) 0 blA).st.revDirs =
        blZero.st.revDirs ++ blA.st.revDirs := by
      rw [hbr.2.2.2.1, hblA_z]
    change (bindRetsN0 esc (linCnt0 cur.node) 0 blA).st.revDirs = _
    rw [hbr_rev]
    change blZero.st.revDirs ++ emitLinNode0 cur st0Clean = _
    rw [hn_acc]
  have hrev_eq :
      (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) esc
        { st with revDirs := [] } ctrl [cur]).1.revDirs =
      rK.1.revDirs ++ (blZero.st.revDirs ++
        (emitLinNode0 cur { st0Clean with revDirs := [] } ++ st0Clean.revDirs)) := by
    rw [hstep1]; dsimp only [rK]; rw [hr_split]
  have hpat_node :
      patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (emitLinNode0 cur { st0Clean with revDirs := [] })) [] =
      emitFwd0 (emitLinNode0 cur { st0Clean with revDirs := [] }) :=
    patchEpilogues0_of_listNoSpZero0 _
      (listNoSpZero0_reverse (emitLinNode0_acc cur { st0Clean with revDirs := [] }).2)
  have hbr_nz : ListNoSpZero0 blZero.st.revDirs := by
    let blA := relAndUpdateSt0 esc cur { st0Clean with revDirs := [] } []
    have hbr := bindRetsN0_revDirs esc (linCnt0 cur.node).toNat (linCnt0 cur.node) 0 blA rfl
    exact hbr.2.2.2.2
  have hpat_bl : patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 blZero.st.revDirs) [] =
      emitFwd0 blZero.st.revDirs :=
    patchEpilogues0_of_listNoSpZero0 _ (listNoSpZero0_reverse hbr_nz)
  rw [hrev_eq, emitFwd0_append, emitFwd0_append, emitFwd0_append,
    patchEpilogues0_append, patchEpilogues0_append, patchEpilogues0_append,
    hpat_node, hpat_bl, toAmd64Program_append, toAmd64Program_append,
    toAmd64Program_append] at hcode
  simpa only [List.append_assoc] using hcode

private theorem slotsAgree0_venv_congr {esc : Array Nat} {preSt : PreSt0} {st : RegaSt0}
    {p : PreItem0} {t : RegaTask0} {vT : List Ty0} {vs : List ((ty : Ty) × Val ty)}
    {σ : List (BitVec 64)} {venv0 : List UInt32}
    (h : t.venv = venv0)
    (hag : SlotsAgree0 esc preSt st p { t with venv := venv0 } vT vs σ) :
    SlotsAgree0 esc preSt st p t vT vs σ := by
  rcases t with ⟨lbl, nd, venv, lenv, fr, nxt⟩; dsimp only at h; subst h; exact hag

theorem stepLinear_bind_ok {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
    {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
    {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
    {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
    {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
    {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
    {k : Nat} {fuel : UInt32} {mNew : Mem 64} {s1 : MachineData}
    {σ : List (BitVec 64)} {rvs : Tup Val (ty0ListToTy (linRetTys0 cur.node))}
    (hlin : isTerm0 cur.node = false) (hnj : ∀ c t e, cur.node ≠ .jnz c t e)
    (hng : ∀ bs k, cur.node ≠ .group bs k)
    (hfuel : workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat)
    (hns_eq : (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns)
    (hinv : RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
      (cur :: w₂) (mCur :: m₂))
    (hlen_pw : pw₂.length = w₂.length) (hlen_mw : m₂.length = w₂.length)
    (hk_inf :
      let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
      let lsC := stepLinear0 preRes.escaped cur st0Clean ctrl []
      let tK := lsC.work[0]'(by simp [lsC, stepLinear0, stepLinBindPush0, linBindPush0])
      let blZero := bindRetsN0 preRes.escaped (linCnt0 cur.node) 0
        (relAndUpdateSt0 preRes.escaped cur { st0Clean with revDirs := [] } [])
      (toAmd64Program symName (emitFwd0 blZero.st.revDirs) ++
        toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 (linK0 cur.node))) preRes.escaped
            { lsC.st with revDirs := [] } ctrl [tK]).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k)
    (hwp' : wp0 Γ symName rs (pushTup rvs vs) ls Q X (linK0 cur.node) mNew)
    (hfr1 : FnFrameInv0 ns s0 ra0 n Rf mNew s1 σ)
    (htup1 : tupAbiHolds0 s1 true 0 (linRetTys0 cur.node) rvs)
    (hag1 : SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ)
    (hgl : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped st cur mCur vs fnIdx mCur.gl ls)
    (hih : ∀ k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m' fuel' s' σ',
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' (curPre' :: pw') seenJnz' st' ctrl'
        (cur' :: w') (mCur' :: m') →
      pw'.length = w'.length → m'.length = w'.length →
      cur'.node = linK0 cur.node →
      nodeCount0 cur'.node = nodeCount0 (linK0 cur.node) →
      workNodeCount0 ((cur' :: w').map RegaTask0.node) ≤ fuel'.toNat →
      (regaRunAux0 fuel' preRes.escaped st' ctrl' (cur' :: w')).1.maxSlots = ns →
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur'.node)) preRes.escaped
          { st' with revDirs := [] } ctrl' [cur']).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k_nxt →
      wp0 Γ symName rs (pushTup rvs vs) ls Q X cur'.node mNew →
      FnFrameInv0 ns s0 ra0 n Rf mNew s' σ' →
      SlotsAgree0 preRes.escaped preSt' st' curPre' cur' mCur'.vT (pushTup rvs vs) σ' →
      GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st' cur' mCur' (pushTup rvs vs) fnIdx mCur'.gl ls →
      x64ScalarMach.Run h k_nxt s' (fnPost0 h rs Q X s0 ra0 n nX Rf)) :
    x64ScalarMach.Run h k s1 (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  have hcur_ok := hinv.items_ok 0 (by simp) (by simp) (by simp)
  dsimp only [List.getElem_cons_zero] at hcur_ok
  obtain ⟨hpn, hpv, hvlen, hvlt, _, _, _, hwf, hfit, _, _, hpool, hnxt_nv, hinfo_ok,
    _, _, hlive⟩ := hcur_ok
  obtain ⟨hret_7, hret_cnt⟩ := linRetTys0_length_le hwf hlin hnj hng
  let st0 := regaPrependLbl0 cur st ctrl
  let lsStep := regaStep0 preRes.escaped cur st0 ctrl w₂
  let st0Clean := regaPrependLbl0 cur { st with revDirs := [] } ctrl
  let lsC := stepLinear0 preRes.escaped cur st0Clean ctrl []
  let bl0 := relAndUpdateSt0 preRes.escaped cur { st0Clean with revDirs := [] } []
  let blZero := bindRetsN0 preRes.escaped (linCnt0 cur.node) 0 bl0
  let preSt1 := preNoteNode0 curPre.scope curPre.venv curPre.node preSt
  let out := preStepPush0 curPre preSt1 nextSc pw₂
  let mK : TaskMeta0 := TaskMeta0.mk (legalNextVenv0 cur.node mCur.vT) mCur.lT mCur.gl none
  have hlin_inv : RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st out.work
      seenJnz lsStep.st lsStep.ctrl lsStep.work (mK :: m₂) :=
    regaStep0_lin hinv hlin hnj hng
  obtain ⟨hout_work, hls_st, hls_ctrl, hls_work⟩ :=
    regaStep0_lin_unfold preRes.escaped curPre preSt nextSc pw₂ st0 ctrl cur w₂ hpn hlin hnj hng
  let blFull := bindRetsN0 preRes.escaped (linCnt0 cur.node) 0
    (relAndUpdateSt0 preRes.escaped cur st0 (emitLinNode0 cur st0))
  let blC := bindRetsN0 preRes.escaped (linCnt0 cur.node) 0
    (relAndUpdateSt0 preRes.escaped cur st0Clean (emitLinNode0 cur st0Clean))
  have hst0_eqs : st0.nextVid = st.nextVid ∧ st0.maxSlots = st.maxSlots ∧
      st0.vslot = st.vslot ∧ st0.remUses = st.remUses := by
    dsimp only [st0, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hst0C_eqs : st0Clean.nextVid = st.nextVid ∧ st0Clean.maxSlots = st.maxSlots ∧
      st0Clean.vslot = st.vslot ∧ st0Clean.remUses = st.remUses := by
    dsimp only [st0Clean, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hst0Z_eqs : { st0Clean with revDirs := [] }.nextVid = st.nextVid ∧
      { st0Clean with revDirs := [] }.maxSlots = st.maxSlots ∧
      { st0Clean with revDirs := [] }.vslot = st.vslot ∧
      { st0Clean with revDirs := [] }.remUses = st.remUses := by
    dsimp only [st0Clean, regaPrependLbl0]; split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  have hbl0_rel :
      { relAndUpdateSt0 preRes.escaped cur st0 (emitLinNode0 cur st0) with
        st := { (relAndUpdateSt0 preRes.escaped cur st0 (emitLinNode0 cur st0)).st with
          revDirs := [] } } = bl0 :=
    relAndUpdateSt0_clean preRes.escaped cur st0 { st0Clean with revDirs := [] } _
      (hst0_eqs.1.trans hst0Z_eqs.1.symm) (hst0_eqs.2.1.trans hst0Z_eqs.2.1.symm)
      (hst0_eqs.2.2.1.trans hst0Z_eqs.2.2.1.symm) (hst0_eqs.2.2.2.trans hst0Z_eqs.2.2.2.symm)
  have hbl0C_rel :
      { relAndUpdateSt0 preRes.escaped cur st0Clean (emitLinNode0 cur st0Clean) with
        st := { (relAndUpdateSt0 preRes.escaped cur st0Clean (emitLinNode0 cur st0Clean)).st with
          revDirs := [] } } = bl0 :=
    relAndUpdateSt0_clean preRes.escaped cur st0Clean { st0Clean with revDirs := [] } _
      (hst0C_eqs.1.trans hst0Z_eqs.1.symm) (hst0C_eqs.2.1.trans hst0Z_eqs.2.1.symm)
      (hst0C_eqs.2.2.1.trans hst0Z_eqs.2.2.1.symm) (hst0C_eqs.2.2.2.trans hst0Z_eqs.2.2.2.symm)
  have hbr_full := bindRetsN0_revDirs preRes.escaped (linCnt0 cur.node).toNat (linCnt0 cur.node) 0
    (relAndUpdateSt0 preRes.escaped cur st0 (emitLinNode0 cur st0)) rfl
  have hbr_C := bindRetsN0_revDirs preRes.escaped (linCnt0 cur.node).toNat (linCnt0 cur.node) 0
    (relAndUpdateSt0 preRes.escaped cur st0Clean (emitLinNode0 cur st0Clean)) rfl
  rw [hbl0_rel] at hbr_full
  rw [hbl0C_rel] at hbr_C
  have hlsC_clean : { lsC.st with revDirs := [] } = { lsStep.st with revDirs := [] } := by
    have hlsC_st : lsC.st = blC.st := rfl
    rw [hlsC_st, hls_st, hbr_full.2.2.2.1, hbr_C.2.2.2.1]
  have hlsC_head :
      lsC.work[0]'(by simp [lsC, stepLinear0, stepLinBindPush0, linBindPush0]) =
        RegaTask0.mk 0 (linK0 cur.node) blFull.venv cur.lenv blFull.free blFull.nxt := by
    have h1 : (lsC.work[0]'(by simp [lsC, stepLinear0, stepLinBindPush0, linBindPush0])) =
        RegaTask0.mk 0 (linK0 cur.node) blC.venv cur.lenv blC.free blC.nxt := rfl
    rw [h1, hbr_full.1, hbr_full.2.1, hbr_full.2.2.1, hbr_C.1, hbr_C.2.1, hbr_C.2.2.1]
  have hsub := preRunAux0_sub_active hinv.pre_inv hinv.pre_run
  obtain ⟨⟨_, _, _, _, _, _⟩, hpr_noesc⟩ := hsub
  let rr := relNodeArgs0 preRes.escaped st.vslot cur.venv cur.node
    (RelRes0.mk st.remUses cur.freeSlots)
  have hrel := relNodeArgs0_spec preRes.escaped st.vslot cur.venv cur.node
    (RelRes0.mk st.remUses cur.freeSlots) preRes.nextVid.toNat cur.nextSlot
    (by have := hinv.preRes_nv; omega) (ActiveDefScope0 preSt (curPre :: pw₂)) hlin hnj hng
    hinv.st_rem_sz (fun v hv => Nat.lt_of_lt_of_le (hvlt v hv) (by
      have := hinv.preRes_uses_lt_bd; omega))
    (by rw [hvlen]; exact wfNode0_nodeArgsInVenv0 hwf)
    (fun v hv hesc hpos => by
      have hnv_cur : UInt32.ofNat v ∈ cur.venv := Classical.byContradiction fun hnin => by
        have hzer := nodeArgsUses0_eq_zero_of_not_in_venv hv (by have := hinv.preRes_nv; omega)
          (fun w hw => Nat.lt_of_lt_of_le (hvlt w hw) (by have := hinv.preRes_uses_lt_bd; omega))
          (by rw [hvlen]; exact wfNode0_nodeArgsInVenv0 hwf) hlin hnj hng hnin
        omega
      have hv_st : v < preSt.nextVid.toNat := by
        rw [← hinv.st_nv]
        have hvn : (UInt32.ofNat v).toNat = v :=
          u32_ofNat_toNat_lt10 (Nat.lt_trans hv (by have := hinv.preRes_nv; omega))
        have h1 := hvlt _ hnv_cur
        rw [hvn] at h1
        exact h1
      refine ⟨hv_st, curPre, List.mem_cons_self, ?_⟩
      by_cases he : preSt.defScope.getD v 0 = curPre.scope.toNat
      · exact he.symm
      · exfalso
        have h0 := hpr_noesc v hv_st hesc curPre List.mem_cons_self
        simp only [Ne.symm he, ↓reduceIte, hpn, hpv, ← hinv.st_nv] at h0
        have hnz := nodeArgsUses0_zero_of_astZero h0
        omega)
    hinv.preRes_es_bit
    (fun v hv => Nat.lt_of_le_of_lt (hinv.st_rem_le v hv) (hinv.preRes_us_bd v hv))
    (fun v hv hesc => by
      by_cases hpos : 0 < nodeArgsUses0 (UInt32.ofNat v) cur.venv cur.node
      · have hnv_cur : UInt32.ofNat v ∈ cur.venv := Classical.byContradiction fun hnin => by
          have hzer := nodeArgsUses0_eq_zero_of_not_in_venv hv (by have := hinv.preRes_nv; omega)
            (fun w hw => Nat.lt_of_lt_of_le (hvlt w hw) (by
              have := hinv.preRes_uses_lt_bd; omega))
            (by rw [hvlen]; exact wfNode0_nodeArgsInVenv0 hwf) hlin hnj hng hnin
          omega
        have hv_st : v < st.nextVid.toNat := by
          have hvn : (UInt32.ofNat v).toNat = v :=
            u32_ofNat_toNat_lt10 (Nat.lt_trans hv (by have := hinv.preRes_nv; omega))
          have h1 := hvlt _ hnv_cur
          rw [hvn] at h1
          exact h1
        have hsc : curPre.scope.toNat = preSt.defScope.getD v 0 := by
          by_cases he : curPre.scope.toNat = preSt.defScope.getD v 0
          · exact he
          · exfalso
            have h0 := hpr_noesc v (hinv.st_nv ▸ hv_st) hesc curPre List.mem_cons_self
            simp only [he, ↓reduceIte, hpn, hpv, ← hinv.st_nv] at h0
            have hnz := nodeArgsUses0_zero_of_astZero h0
            omega
        rw [hinv.st_rem_active v hv_st hesc ⟨hinv.st_nv ▸ hv_st, curPre, List.mem_cons_self, hsc⟩]
        dsimp only [sameScopeSpineSum0]
        rw [hsc.symm]; simp only [↓reduceIte, hpv, hpn, ← hinv.st_nv]
        rw [spineUses0_lin (UInt32.ofNat v) cur.venv st.nextVid hlin hnj hng hfit]
        omega
      · omega)
    (activeDefScope0_live_slots_ok hinv) hpool.1 hpool.2.1
  change rr.remUses.size = preRes.nextVid.toNat ∧ _ at hrel
  have hbl0_free : bl0.free = rr.free := by
    dsimp only [bl0, relAndUpdateSt0, rr]
    rw [hst0Z_eqs.2.2.1, hst0Z_eqs.2.2.2]
  have hbl0_rem : bl0.st.remUses = rr.remUses := by
    dsimp only [bl0, relAndUpdateSt0, rr]
    rw [hst0Z_eqs.2.2.1, hst0Z_eqs.2.2.2]
  have hbl0_nxt : bl0.nxt = cur.nextSlot := rfl
  have hbl0_nv : bl0.st.nextVid = st.nextVid := hst0Z_eqs.1
  have hbl0_vsl : bl0.st.vslot = st.vslot := hst0Z_eqs.2.2.1
  have hbl0_ms : bl0.st.maxSlots = st.maxSlots := hst0Z_eqs.2.1
  have hpool0 :
      SlotPoolInv0 bl0.free bl0.nxt bl0.st.maxSlots (preRes.nextVid.toNat + fnMaxJump) :=
    ⟨hbl0_free ▸ hrel.2.1, fun s hs => hbl0_nxt ▸ hrel.2.2.1 s (hbl0_free ▸ hs),
     hbl0_ms ▸ hbl0_nxt ▸ hpool.2.2.1, hbl0_ms ▸ hpool.2.2.2.1, hpool.2.2.2.2⟩
  have hret_bd_step : bl0.st.nextVid.toNat + (linRetTys0 cur.node).length ≤
      preRes.nextVid.toNat := by
    have hbc := linCnt0_le_binderCount0 hwf hlin hnj hng
    have htot := hinv.preRes_uses_lt_bd
    rw [List.map_cons] at htot; dsimp only [workBinderCount0] at htot
    rw [hbl0_nv]; omega
  have hret_nv31 : bl0.st.nextVid.toNat + (linRetTys0 cur.node).length < 2 ^ 31 := by
    have := hinv.preRes_nv; omega
  have hret_nxt_bd : bl0.nxt.toNat + (linRetTys0 cur.node).length ≤
      preRes.nextVid.toNat + fnMaxJump := by
    have hbc := linCnt0_le_binderCount0 hwf hlin hnj hng
    have htot := hinv.preRes_uses_lt_bd
    rw [List.map_cons] at htot; dsimp only [workBinderCount0] at htot
    have := hnxt_nv
    have := hret_cnt
    rw [hbl0_nxt]
    omega
  have hfuel_pos : 0 < fuel.toNat := by
    rw [List.map_cons] at hfuel; dsimp only [workNodeCount0] at hfuel
    have := nodeCount0_pos cur.node; omega
  have hfuel_sub : (fuel - 1).toNat = fuel.toNat - 1 := u32_sub1_toNat7 hfuel_pos
  have hcnt_child : workNodeCount0 (lsStep.work.map RegaTask0.node) + 1 =
      workNodeCount0 ((cur :: w₂).map RegaTask0.node) :=
    regaWorkNodeCount0_children preRes.escaped cur st0 ctrl w₂
  have hfuel_next : workNodeCount0 (lsStep.work.map RegaTask0.node) ≤ (fuel - 1).toNat := by
    omega
  have hns_next :
      (regaRunAux0 (fuel - 1) preRes.escaped lsStep.st lsStep.ctrl lsStep.work).1.maxSlots =
        ns := by
    have h1 := regaRunAux0_step_once (fuel := fuel) (esc := preRes.escaped)
      (st := st) (ctrl := ctrl) (cur := cur) (rest := w₂) hfuel_pos
    dsimp only at h1
    rw [← h1]; exact hns_eq
  have hstep_ms : lsStep.st.maxSlots.toNat ≤ ns.toNat := by
    have hp0_b := regaRunAux0_step_prefix 0 (fuel - 1) ctx fnIdx fnMaxJump preRes out.nextScope
      out.st [] out.work seenJnz lsStep.st lsStep.ctrl [] lsStep.work [] (mK :: m₂)
      rfl (Nat.zero_le _) rfl rfl (by simpa only [List.nil_append] using hlin_inv)
    dsimp only at hp0_b
    have hr1_eq : (regaRunAux0 (UInt32.ofNat 0) preRes.escaped { lsStep.st with revDirs := [] }
        lsStep.ctrl []).1.maxSlots = lsStep.st.maxSlots := by
      rw [regaRunAux0_nil]
    rw [hr1_eq] at hp0_b
    have hle_full := hp0_b.2.2.1
    simp only [List.nil_append] at hle_full
    rw [hns_next] at hle_full
    exact hle_full
  have hms_blZero : blZero.st.maxSlots.toNat ≤ σ.length := by
    have hms_eq : lsStep.st.maxSlots = blZero.st.maxSlots := by
      rw [hls_st, hbr_full.2.2.2.1]
    rw [hfr1.1, ← hms_eq]; exact hstep_ms
  have hst_bd_cnt : st.nextVid.toNat + (linCnt0 cur.node).toNat ≤ preRes.nextVid.toNat := by
    rw [← hbl0_nv, ← hret_cnt]; exact hret_bd_step
  have hbr_run := bindRetsN0_run_spec (symName := symName) (h := h) (esc := preRes.escaped)
    (G := Eq mNew ⋆ x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
      region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ Rf)
    (post := fnPost0 h rs Q X s0 ra0 n nX Rf)
    (linRetTys0 cur.node) k (linCnt0 cur.node) 0 bl0 rvs σ s1 (preRes.nextVid.toNat + fnMaxJump)
    hret_cnt.symm (by simpa using hret_7) (by simpa using htup1)
    (by rw [hbl0_vsl, hbl0_nv]; exact hinv.st_vslot_sz)
    hret_nv31 hpool0 hret_nxt_bd hms_blZero
    (fun j hj => by
      rw [hbl0_nv, hbl0_rem]
      have hult : st.nextVid.toNat + j < preRes.nextVid.toNat := by rw [← hbl0_nv]; omega
      have hes : preRes.escaped.getD (st.nextVid.toNat + j) 0 < 2 ^ 32 := by
        rcases hinv.preRes_es_bit (st.nextVid.toNat + j) hult with h0 | h1 <;> omega
      have hru : rr.remUses.getD (st.nextVid.toNat + j) 0 < 2 ^ 32 := by
        have hrs := hrel.2.2.2.1 (st.nextVid.toNat + j) hult
        have hbd := Nat.lt_of_le_of_lt (hinv.st_rem_le (st.nextVid.toNat + j) hult)
          (hinv.preRes_us_bd (st.nextVid.toNat + j) hult)
        change rr.remUses.getD (st.nextVid.toNat + j) 0 = _ at hrs
        dsimp only [rr] at hrs
        rw [hrs]; split <;> omega
      exact ⟨hes, hru⟩)
    (fnFrameInv0_mem_slots hfr1)
  dsimp only at hbr_run
  have hbl0_clean : { bl0 with st := { bl0.st with revDirs := [] } } = bl0 := rfl
  rw [hbl0_clean] at hbr_run
  let tK := RegaTask0.mk 0 (linK0 cur.node) blFull.venv cur.lenv blFull.free blFull.nxt
  let curPre1 := PreItem0.mk (linK0 curPre.node)
    (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).1 curPre.scope
  have hk_inf1 : (toAmd64Program symName (emitFwd0 blZero.st.revDirs)).IsInfixAt
      (x64ScalarMach.prog h) k := hk_inf.append.1
  have hk_inf2 :
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 tK.node)) preRes.escaped
          { lsStep.st with revDirs := [] } lsStep.ctrl [tK]).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h)
        (k + (toAmd64Program symName (emitFwd0 blZero.st.revDirs)).length) := by
    dsimp only at hk_inf
    let tK' := lsC.work[0]'(by simp [lsC, stepLinear0, stepLinBindPush0, linBindPush0])
    have ht_eq : tK = tK' := hlsC_head.symm
    have hst_eq : { lsStep.st with revDirs := [] } = { lsC.st with revDirs := [] } :=
      hlsC_clean.symm
    rw [ht_eq, hst_eq, hls_ctrl]
    exact hk_inf.append.2
  refine hbr_run hk_inf1 fun s2 ⟨σ2, hσ2_len, hpres2, hpush2, hmem2⟩ hfr2 => ?_
  have hfr2' : FnFrameInv0 ns s0 ra0 n Rf mNew s2 σ2 := by
    obtain ⟨hlen1, hrsp1, hcs1, _⟩ := hfr1
    have hrsp2 : s2.regs.get64 .rsp = s1.regs.get64 .rsp := hfr2.1 .rsp (by simp)
    refine ⟨hσ2_len.trans hlen1, hrsp2.trans hrsp1,
      fun r hr => (hfr2.1 r (fun hm => calleeSaved_not_in_rsp_scratch r hr (by
        simp only [List.mem_singleton] at hm; subst hm; simp))).trans (hcs1 r hr), ?_⟩
    exact fnFrameInv0_mem_of_slots hmem2
  have hbr_bl0 := bindRetsN0_spec preRes.escaped (linCnt0 cur.node).toNat (linCnt0 cur.node) 0
    bl0 (preRes.nextVid.toNat + fnMaxJump) rfl (by rw [hbl0_vsl, hbl0_nv]; exact hinv.st_vslot_sz)
    (by rw [hbl0_nv]; have := hinv.preRes_nv; omega) hpool0
    (by rw [hbl0_nxt]; have := hinv.preRes_uses_lt_bd; have := hinv.maxJump_bd; omega)
    (fun j hj => by
      rw [hbl0_nv, hbl0_rem]
      have hult : st.nextVid.toNat + j < preRes.nextVid.toNat := by omega
      have hes : preRes.escaped.getD (st.nextVid.toNat + j) 0 < 2 ^ 32 := by
        rcases hinv.preRes_es_bit (st.nextVid.toNat + j) hult with h0 | h1 <;> omega
      have hru : rr.remUses.getD (st.nextVid.toNat + j) 0 < 2 ^ 32 := by
        have hrs := hrel.2.2.2.1 (st.nextVid.toNat + j) hult
        have hbd := Nat.lt_of_le_of_lt (hinv.st_rem_le (st.nextVid.toNat + j) hult)
          (hinv.preRes_us_bd (st.nextVid.toNat + j) hult)
        change rr.remUses.getD (st.nextVid.toNat + j) 0 = _ at hrs
        dsimp only [rr] at hrs
        rw [hrs]; split <;> omega
      exact ⟨hes, hru⟩)
  dsimp only at hbr_bl0
  have hst_ls_eq : lsStep.st.remUses = blZero.st.remUses ∧
      lsStep.st.vslot = blZero.st.vslot ∧
      lsStep.st.nextVid = blZero.st.nextVid := by
    rw [hls_st, hbr_full.2.2.2.1]; exact ⟨rfl, rfl, rfl⟩
  have hlin_p : isTerm0 curPre.node = false := hpn ▸ hlin
  have hnj_p : ∀ c t e, curPre.node ≠ .jnz c t e := fun c t e h => hnj c t e (hpn ▸ h)
  have hng_p : ∀ bs k, curPre.node ≠ .group bs k := fun bs k h => hng bs k (hpn ▸ h)
  have hp_inv := hinv.pre_inv.items_ok curPre List.mem_cons_self
  obtain ⟨vT', lT', hvlen', hvlt', hwf', hfit', hsbg', hnb'⟩ := hp_inv
  have hst1 := preNoteNode0_spec curPre.scope curPre.venv curPre.node preSt
    hinv.pre_inv.defScope_sz hinv.pre_inv.uses_sz hinv.pre_inv.escaped_sz hvlt'
    (hvlen' ▸ wfNode0_nodeArgsInVenv0 hwf')
    (fun v hv => by
      have hb := hinv.pre_inv.uses_bound v hv
      rw [List.map_cons] at hb; dsimp only [workArgCount0] at hb
      omega)
    (fun v hv => Nat.lt_trans (hinv.pre_inv.defScope_lt v hv) (UInt32.toNat_lt nextSc))
    hinv.pre_inv.escaped_bit
  dsimp only at hst1
  have hnv_b : preSt1.nextVid.toNat + (linCnt0 curPre.node).toNat < 2 ^ 32 := by
    dsimp only [preSt1]; rw [hst1.1]
    have hb := hinv.pre_inv.nextVid_bound
    have hbc_l := linCnt0_le_binderCount0 hwf' hlin_p hnj_p hng_p
    rw [List.map_cons] at hb; dsimp only [workBinderCount0] at hb
    omega
  have hbind_pre := preBindLoop0_spec (linCnt0 cur.node).toNat (linCnt0 curPre.node)
    curPre.scope curPre.venv preSt1 (by rw [hpn]) (by rw [← hpn]; exact hnv_b)
    (hst1.1 ▸ hst1.2.1.symm ▸ hinv.pre_inv.defScope_sz)
    (hst1.1 ▸ hst1.2.2.1) (hst1.1 ▸ hst1.2.2.2.1)
  dsimp only at hbind_pre
  have hout_st_eq : out.st =
      (preBindLoop0 (linCnt0 curPre.node) curPre.scope curPre.venv preSt1).2 := by
    have hlinp : isTerm0 curPre.node = false := hpn ▸ hlin
    dsimp only [out, preStepPush0]; simp only [hlinp, Bool.false_eq_true, ↓reduceIte]; rfl
  have hbr_venv : blZero.venv = pushFreshVids0 (linCnt0 cur.node).toNat bl0.st.nextVid bl0.venv :=
    hbr_bl0.1
  have hbr_nxt : bl0.nxt.toNat ≤ blZero.nxt.toNat := hbr_bl0.2.2.2.2.2.1
  have hbr_st_rem : blZero.st.remUses = bl0.st.remUses := hbr_bl0.2.2.2.1
  have hbr_pres : ∀ v < bl0.st.nextVid.toNat,
      arrGetU0 blZero.st.vslot (UInt32.ofNat v) = arrGetU0 bl0.st.vslot (UInt32.ofNat v) :=
    hbr_bl0.2.2.2.2.2.2.2.2.1
  have hlive_old : ∀ v < st.nextVid.toNat,
      LiveInTask0 preRes.escaped out.st lsStep.st curPre1 tK v →
      LiveInTask0 preRes.escaped preSt st curPre cur v := by
    intro v hv hlv
    rcases hlv with ⟨hes, hwmem⟩ | ⟨hes, hsc, hpos⟩
    · refine Or.inl ⟨hes, ?_⟩
      dsimp only [tK] at hwmem
      rw [hbr_full.1, hbr_venv, hbl0_nv] at hwmem
      rcases (mem_pushFreshVids0 (linCnt0 cur.node).toNat st.nextVid cur.venv
          (UInt32.ofNat v)).mp hwmem with h0 | ⟨j, hj, he⟩
      · exact h0
      · have hn := congrArg UInt32.toNat he
        rw [u32_ofNat_toNat_lt10 (Nat.lt_trans hv (UInt32.toNat_lt _)),
          u32_add_ofNat_lt7 (by have := hinv.preRes_nv; omega)] at hn
        omega
    · rw [hout_st_eq, hbind_pre.2.2.2.2.2.1 v] at hsc
      simp only [show v < preSt1.nextVid.toNat from hst1.1 ▸ hinv.st_nv ▸ hv, ↓reduceIte] at hsc
      dsimp only [preSt1] at hsc; rw [hst1.2.1] at hsc
      have hv_res : v < preRes.nextVid.toNat :=
        Nat.lt_of_lt_of_le hv (by have := hinv.preRes_uses_lt_bd; omega)
      have hru := hrel.2.2.2.1 v hv_res
      change rr.remUses.getD v 0 = _ at hru
      rw [hst_ls_eq.1, hbr_st_rem, hbl0_rem] at hpos
      simp only [hes, ↓reduceIte] at hru
      rw [hru] at hpos
      exact Or.inr ⟨hes, hsc, by omega⟩
  have hfree_no_old : ∀ v < st.nextVid.toNat,
      LiveInTask0 preRes.escaped out.st lsStep.st curPre1 tK v →
      arrGetU0 st.vslot (UInt32.ofNat v) ∉ rr.free := by
    intro v hv hlv_lin hm
    have hlv := hlive_old v hv hlv_lin
    rcases (hrel.2.2.2.2.1 _).mp hm with hc | ⟨u, hu, hDu, hescu, hposu, hzu, heq⟩
    · exact (hlive v hv hlv).2.1 hc
    · have hu_lt : u < st.nextVid.toNat := hinv.st_nv ▸ hDu.1
      change rr.remUses.getD u 0 = 0 at hzu
      have hne : u ≠ v := by
        rintro rfl
        rcases hlv_lin with ⟨hes1, _⟩ | ⟨_, _, hpos'⟩
        · rw [hescu] at hes1; cases hes1
        · rw [hst_ls_eq.1, hbr_st_rem, hbl0_rem, hzu] at hpos'
          exact Nat.lt_irrefl 0 hpos'
      have hsc_u : curPre.scope.toNat = preSt.defScope.getD u 0 := by
        have hru := hrel.2.2.2.1 u hu
        simp only [hescu, ↓reduceIte] at hru
        by_cases he : curPre.scope.toNat = preSt.defScope.getD u 0
        · exact he
        · exfalso
          have h0 := hpr_noesc u (hinv.st_nv ▸ hu_lt) hescu curPre List.mem_cons_self
          simp only [he, ↓reduceIte, hpn, hpv, ← hinv.st_nv] at h0
          have hnz := nodeArgsUses0_zero_of_astZero h0
          rw [hru, hnz] at hzu
          dsimp only at hposu hzu
          rw [Nat.sub_zero] at hzu
          omega
      exact (hlive v hv hlv).2.2 u hu_lt hne (Or.inr ⟨hescu, hsc_u, hposu⟩) heq.symm
  have hold_agree : ∀ (idx : Nat) (_hi : idx < cur.venv.length),
      LiveInTask0 preRes.escaped out.st lsStep.st curPre1 tK (cur.venv[idx]'_hi).toNat →
      ∃ (hsl : (arrGetU0 lsStep.st.vslot (cur.venv[idx]'_hi)).toNat < σ2.length)
        (hvs : idx < vs.length) (ht : idx < mCur.vT.length),
        HoldsCanon640 mCur.vT[idx] vs[idx]
          σ2[(arrGetU0 lsStep.st.vslot (cur.venv[idx]'_hi)).toNat] := by
    intro idx hi hlv
    have hvid_lt : (cur.venv[idx]'hi).toNat < st.nextVid.toNat := hvlt _ (List.getElem_mem hi)
    have hlv_old := hlive_old _ hvid_lt hlv
    obtain ⟨hsl, hvs, ht, hcanon⟩ := hag1.2.2 idx hi hlv_old
    have hsl_lt : (arrGetU0 st.vslot (cur.venv[idx]'hi)).toNat < cur.nextSlot.toNat := by
      have := (hlive _ hvid_lt hlv_old).1
      simpa only [UInt32.ofNat_toNat] using this
    have hsl_nf : arrGetU0 st.vslot (cur.venv[idx]'hi) ∉ rr.free := by
      have := hfree_no_old _ hvid_lt hlv
      simpa only [UInt32.ofNat_toNat] using this
    have hvsl_pres :
        arrGetU0 lsStep.st.vslot (cur.venv[idx]'hi) = arrGetU0 st.vslot (cur.venv[idx]'hi) := by
      rw [hst_ls_eq.2.1]
      have := hbr_pres _ (hbl0_nv ▸ hvid_lt)
      simpa only [UInt32.ofNat_toNat, hbl0_vsl] using this
    have hq_eq := hpres2 (arrGetU0 st.vslot (cur.venv[idx]'hi)) (hbl0_nxt ▸ hsl_lt)
      (hbl0_free ▸ hsl_nf) hsl
    rw [hvsl_pres]
    refine ⟨hσ2_len ▸ hsl, hvs, ht, ?_⟩
    rw [hq_eq]; exact hcanon
  have hpa2 : PushAgree0 preRes.escaped lsStep.st.remUses lsStep.st.vslot
      st.nextVid (linRetTys0 cur.node) rvs σ2 := by
    rw [hst_ls_eq.1, hst_ls_eq.2.1, ← hbl0_nv]
    exact hpush2
  obtain ⟨hvlen2, henv2, hslot2⟩ := pushFresh_slotsAgree0_aux preRes.escaped out.st lsStep.st
    curPre1 tK σ2 (linRetTys0 cur.node) rvs st.nextVid cur.venv mCur.vT vs
    (by rw [← hbl0_nv]; exact hret_nv31) hag1.1 hag1.2.1 hvlt hold_agree hpa2
  have hag2 : SlotsAgree0 preRes.escaped out.st lsStep.st curPre1 tK mK.vT
      (pushTup rvs vs) σ2 := by
    have hvt_eq : mK.vT = pushTys0 (linRetTys0 cur.node) mCur.vT :=
      legalNextVenv0_eq_pushTys0 hlin hnj hng
    have hvenv_eq :
        tK.venv = pushFreshVids0 (linRetTys0 cur.node).length st.nextVid cur.venv := by
      dsimp only [tK]
      rw [hbr_full.1, hbr_venv, hbl0_nv, hret_cnt]; rfl
    rw [hvt_eq]
    exact slotsAgree0_venv_congr hvenv_eq ⟨hvlen2, henv2, fun idx hi hlv => by
      dsimp only at hlv ⊢
      exact hslot2 idx hi (by simpa only [LiveInTask0, hvenv_eq] using hlv)⟩
  have hgl2 : GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
      preRes.escaped lsStep.st tK mK (pushTup rvs vs) fnIdx mCur.gl ls := by
    refine glEntrySem0_pushTys0 (nv := st.nextVid) hgl ?_ ?_
      (legalNextVenv0_eq_pushTys0 hlin hnj hng) ?_
    · dsimp only [tK]; rw [hbr_full.2.2.1]; exact hbl0_nxt ▸ hbr_nxt
    · dsimp only [tK]; rw [hbr_full.1, hbr_venv, hbl0_nv, hret_cnt]; rfl
    · intro info hi_mem
      obtain ⟨_, _, _, _, _, hnv_o, _, _, _, _, hov_lt, _⟩ := hinfo_ok info hi_mem
      refine ⟨st.nextVid.toNat, fun w hw => Nat.lt_of_lt_of_le (hov_lt w hw)
        (Nat.le_trans (Nat.le_add_right _ _) hnv_o), fun v hv => ?_⟩
      rw [hst_ls_eq.2.1]
      exact (hbr_pres v (hbl0_nv ▸ hv)).trans (by rw [hbl0_vsl])
  have hpw_len' : pw₂.length = w₂.length := hlen_pw
  have hmw_len' : m₂.length = w₂.length := hlen_mw
  have hlin_inv' : RegaStepInv0 ctx fnIdx fnMaxJump preRes out.nextScope out.st
      (curPre1 :: pw₂) seenJnz lsStep.st lsStep.ctrl (tK :: w₂) (mK :: m₂) := by
    rw [← hout_work, ← hls_work]; exact hlin_inv
  have hfuel_next' : workNodeCount0 ((tK :: w₂).map RegaTask0.node) ≤ (fuel - 1).toNat := by
    rw [← hls_work]; exact hfuel_next
  have hns_next' :
      (regaRunAux0 (fuel - 1) preRes.escaped lsStep.st lsStep.ctrl (tK :: w₂)).1.maxSlots = ns := by
    rw [← hls_work]; exact hns_next
  exact hih (k + (toAmd64Program symName (emitFwd0 blZero.st.revDirs)).length)
    out.nextScope out.st curPre1 pw₂ seenJnz lsStep.st lsStep.ctrl tK w₂ mK m₂
    (fuel - 1) s2 σ2 hlin_inv' hpw_len' hmw_len' rfl rfl hfuel_next' hns_next' hk_inf2
    hwp' hfr2' hag2 hgl2

end LeanQbe.T.Bootstrap0
