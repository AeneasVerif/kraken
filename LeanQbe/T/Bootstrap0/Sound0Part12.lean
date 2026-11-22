module

public import LeanQbe.T.Bootstrap0.Sound0Part11
import LeanQbe.T.FlatLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.FrameLemmas

/-!
# Bootstrap Stage B (`Sound0Part12`): `regaTask0_run_ok` & `compileFn0_fnSpec`

Completes per-function machine-level semantic soundness for `Compiler0.compileFn0`:
1. Memory reconstruction `region_exists_array64` / `region_sep_exists_array64` turning freshly
   allocated stack slot regions into typed `array64` word arrays.
2. Strong-inductive task-runner soundness `regaTask0_run_ok` dispatching across every
   `TFlat0` AST constructor (`Sound0Part10` + `Sound0Part11` runners).
3. Entry-point function soundness `compileFn0_defined` and `compileFn0_fnSpec` targeting
   `x64ScalarTarget.FnSpec` over `wp0`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Bootstrap0

open LeanQbe.T
open LeanQbe.T.Amd64
open Std Std.ExtHashMap

/-! ## 1. Stack-Region Byte-to-Word Reconstruction (`region_exists_array64`) -/

private theorem toBytes_ofInt64_eq (x : Int) :
    Int.toBytes 8 (BitVec.ofInt 64 x).toInt = Int.toBytes 8 x := by
  rw [← Int.toBytes_emod 8, ← Int.toBytes_emod 8 x]
  congr 1
  simp only [Int.take, BitVec.toInt_eq_msb_cond]
  have hpos : (0 : Int) < 2 ^ 64 := Int.pow_pos (by decide)
  have hx : ((BitVec.ofInt 64 x).toNat : Int) = x % (2 ^ 64 : Int) := by
    rw [BitVec.toNat_ofInt]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.ne_of_gt hpos))
  rw [hx]
  cases (BitVec.ofInt 64 x).msb
  · simp
  · simp only [↓reduceIte]
    rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) from rfl, Int.sub_emod_right, Int.emod_emod]

private theorem bytes_to_words64 :
    ∀ (m : Nat) (bs : List UInt8),
      bs.length = 8 * m → ∃ xs : List (BitVec 64), xs.length = m ∧ bytes64 xs = bs
  | 0, bs, hlen => by
    have hnil : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hnil
    exact ⟨[], rfl, rfl⟩
  | m + 1, bs, hlen => by
    have h8 : 8 ≤ bs.length := by omega
    let bs1 := bs.take 8
    let bs2 := bs.drop 8
    have hlen1 : bs1.length = 8 := List.length_take_of_le h8
    have hlen2 : bs2.length = 8 * m := by
      dsimp only [bs2]
      rw [List.length_drop, hlen]
      omega
    obtain ⟨xs, hxs, hbx⟩ := bytes_to_words64 m bs2 hlen2
    let w : BitVec 64 := BitVec.ofInt 64 (Int.ofBytes bs1)
    refine ⟨w :: xs, by simp [hxs], ?_⟩
    change Int.toBytes 8 w.toInt ++ bytes64 xs = bs
    rw [hbx, show Int.toBytes 8 w.toInt = bs1 from by
      dsimp only [w]
      rw [toBytes_ofInt64_eq]
      have htb := Int.toBytes_ofBytes_all bs1
      rwa [hlen1] at htb]
    exact List.take_append_drop 8 bs

theorem region_exists_array64 (a : BitVec 64) (m : Nat) (hm : 8 * m ≤ 2 ^ 64)
    {f : Mem 64} (hf : region a (8 * m) f) :
    ∃ xs : List (BitVec 64), xs.length = m ∧ array64 a xs f := by
  obtain ⟨bs, hbs_len, rfl⟩ := hf
  obtain ⟨xs, hxs, hbx⟩ := bytes_to_words64 m bs hbs_len
  refine ⟨xs, hxs, ?_⟩
  rw [← hbx]
  exact array64_bytes a xs (by rw [hxs]; exact hm)

theorem region_sep_exists_array64 {a : BitVec 64} {m : Nat} (hm : 8 * m ≤ 2 ^ 64)
    {R : Mem 64 → Prop} {dmem : Mem 64} (h : (region a (8 * m) ⋆ R) dmem) :
    ∃ xs : List (BitVec 64), xs.length = m ∧ (array64 a xs ⋆ R) dmem := by
  have h1 : ((fun f => ∃ xs : List (BitVec 64), xs.length = m ∧ array64 a xs f) ⋆ R) dmem :=
    sep_mono (fun _ hf => region_exists_array64 a m hm hf) h
  rw [sep_ex_l] at h1
  obtain ⟨xs, h2⟩ := h1
  rw [sep_pure_l] at h2
  exact ⟨xs, h2⟩

/-! ## 2. Inductive Task-Runner Soundness (`regaTask0_run_ok`) -/

theorem regaTask0_run_ok :
    ∀ (N : Nat) {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
      {fnIdx : UInt32} {fnMaxJump : Nat} {preRes : PreSt0} {nextSc : UInt32} {preSt : PreSt0}
      {curPre : PreItem0} {pw₂ : List PreItem0} {seenJnz : Bool} {st : RegaSt0} {ctrl : CtrlSt0}
      {cur : RegaTask0} {w₂ : List RegaTask0} {mCur : TaskMeta0} {m₂ : List TaskMeta0}
      {vs : List ((t : Ty) × Val t)} {ls : List ((ts : List Ty) × Cont ts)}
      {rs : List Ty0} {Q : Post (ty0ListToTy rs)} {X : XPost}
      {s0 : MachineData} {ra0 : Int64} {n nX : Nat} {Rf : Mem 64 → Prop} {ns : UInt32}
      {k : Nat} {fuel : UInt32} {mCurMem : Mem 64} {s : MachineData} {σ : List (BitVec 64)},
      nodeCount0 cur.node = N →
      rs.length ≤ 7 → ctx.curRs = rs →
      x64FrameSize ns.toNat ≤ n → n + 8 ≤ 2 ^ 64 →
      x64ScalarTarget.frameSpec.spEntry (s0.regs.get64 .rsp) →
      x64ScalarTarget.LabelsUnique h →
      RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc preSt (curPre :: pw₂) seenJnz st ctrl
        (cur :: w₂) (mCur :: m₂) →
      pw₂.length = w₂.length → m₂.length = w₂.length →
      workNodeCount0 ((cur :: w₂).map RegaTask0.node) ≤ fuel.toNat →
      (regaRunAux0 fuel preRes.escaped st ctrl (cur :: w₂)).1.maxSlots = ns →
      (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
        (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur.node)) preRes.escaped
          { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
        (x64ScalarMach.prog h) k →
      wp0 Γ symName rs vs ls Q X cur.node mCurMem →
      FnFrameInv0 ns s0 ra0 n Rf mCurMem s σ →
      SlotsAgree0 preRes.escaped preSt st curPre cur mCur.vT vs σ →
      GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
        preRes.escaped st cur mCur vs fnIdx mCur.gl ls →
      NodeContracts0 h symName Γ ctx ns n nX cur.node →
      x64ScalarMach.Run h k s (fnPost0 h rs Q X s0 ra0 n nX Rf) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro h symName Γ ctx fnIdx fnMaxJump preRes nextSc preSt curPre pw₂ seenJnz st ctrl
      cur w₂ mCur m₂ vs ls rs Q X s0 ra0 n nX Rf ns k fuel mCurMem s σ
      hN hrs_len hctx_rs hframe_le hn_bd hsp0 hu hinv hlen_pw hlen_mw
      hfuel hns_eq hcode hwp hfr hag hgl hc_node
    have hih : ∀ k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m'
        fuel' s' σ' vs' ls' mMem',
        RegaStepInv0 ctx fnIdx fnMaxJump preRes nextSc' preSt' (curPre' :: pw') seenJnz'
          st' ctrl' (cur' :: w') (mCur' :: m') →
        pw'.length = w'.length → m'.length = w'.length →
        nodeCount0 cur'.node < nodeCount0 cur.node →
        workNodeCount0 ((cur' :: w').map RegaTask0.node) ≤ fuel'.toNat →
        (regaRunAux0 fuel' preRes.escaped st' ctrl' (cur' :: w')).1.maxSlots = ns →
        (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 cur'.node)) preRes.escaped
            { st' with revDirs := [] } ctrl' [cur']).1.revDirs) [])).IsInfixAt
          (x64ScalarMach.prog h) k_nxt →
        wp0 Γ symName rs vs' ls' Q X cur'.node mMem' →
        FnFrameInv0 ns s0 ra0 n Rf mMem' s' σ' →
        SlotsAgree0 preRes.escaped preSt' st' curPre' cur' mCur'.vT vs' σ' →
        GlEntriesSem0 h symName (fnPost0 h rs Q X s0 ra0 n nX Rf) ns s0 ra0 n Rf
          preRes.escaped st' cur' mCur' vs' fnIdx mCur'.gl ls' →
        NodeContracts0 h symName Γ ctx ns n nX cur'.node →
        x64ScalarMach.Run h k_nxt s' (fnPost0 h rs Q X s0 ra0 n nX Rf) :=
      fun k_nxt nextSc' preSt' curPre' pw' seenJnz' st' ctrl' cur' w' mCur' m'
          fuel' s' σ' vs' ls' mMem' hinv' hpw' hmw' hlt hfl' hns' hk' hwp' hfr' hag' hgl' hc' =>
        ih (nodeCount0 cur'.node) (hN ▸ hlt) rfl hrs_len hctx_rs hframe_le hn_bd hsp0 hu
          hinv' hpw' hmw' hfl' hns' hk' hwp' hfr' hag' hgl' hc'
    cases hnd : cur.node with
    | let1 op args cont =>
      exact let1_run_ok hnd hfuel hns_eq hinv hlen_pw hlen_mw hcode hu hwp hfr hag hgl hc_node hih
    | let2Umulw64 a b cont =>
      exact umulw_run_ok hnd hfuel hns_eq hinv hlen_pw hlen_mw hcode hu hwp hfr hag hgl hc_node hih
    | load t addr cont =>
      exact load_run_ok hnd hfuel hns_eq hinv hlen_pw hlen_mw hcode hu hwp hfr hag hgl hc_node hih
    | store t val addr cont =>
      exact store_run_ok hnd hfuel hns_eq hinv hlen_pw hlen_mw hcode hu hwp hfr hag hgl hc_node hih
    | call fnSym as bs args cont =>
      exact call_run_ok hnd hn_bd hsp0 hc_node hfuel hns_eq hinv hlen_pw hlen_mw hcode hu hwp
        hfr hag hgl hih
    | jnz c t e =>
      exact jnz_run_ok hnd hfuel hns_eq hinv hlen_pw hlen_mw hcode hu hwp hfr hag hgl hc_node hih
    | group bodies cont =>
      exact group_run_ok hnd hfuel hns_eq hinv hlen_pw hlen_mw hcode hu hwp hfr hag hgl hc_node hih
    | jump j args =>
      have hnc1 : UInt32.ofNat (nodeCount0 cur.node) = (1 : UInt32) := by
        rw [hnd]; dsimp only [nodeCount0]
        exact u32_ext7 (by rw [u32_toNat_ofNat7, UInt32.toNat_one])
      have hcode1 : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped
            { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
          (x64ScalarMach.prog h) k := hnc1 ▸ hcode
      exact emitJump0_run_ok hnd hfuel hns_eq hinv hcode1 hu hwp hfr hag hgl
    | ret vs' =>
      have hnc1 : UInt32.ofNat (nodeCount0 cur.node) = (1 : UInt32) := by
        rw [hnd]; dsimp only [nodeCount0]
        exact u32_ext7 (by rw [u32_toNat_ofNat7, UInt32.toNat_one])
      have hcode1 : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped
            { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
          (x64ScalarMach.prog h) k := hnc1 ▸ hcode
      exact stepRet0_run_ok hnd hrs_len hctx_rs hframe_le hn_bd hinv hcode1 hu hwp hfr hag
    | tailCall fnSym as args =>
      have hnc1 : UInt32.ofNat (nodeCount0 cur.node) = (1 : UInt32) := by
        rw [hnd]; dsimp only [nodeCount0]
        exact u32_ext7 (by rw [u32_toNat_ofNat7, UInt32.toNat_one])
      have hcode1 : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped
            { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
          (x64ScalarMach.prog h) k := hnc1 ▸ hcode
      exact stepTail0_run_ok (isExit := false) hnd hctx_rs hframe_le hn_bd hsp0 hc_node
        hinv hcode1 hu hwp hfr hag
    | exit fnSym as args =>
      have hnc1 : UInt32.ofNat (nodeCount0 cur.node) = (1 : UInt32) := by
        rw [hnd]; dsimp only [nodeCount0]
        exact u32_ext7 (by rw [u32_toNat_ofNat7, UInt32.toNat_one])
      have hcode1 : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
          (emitFwd0 (regaRunAux0 (1 : UInt32) preRes.escaped
            { st with revDirs := [] } ctrl [cur]).1.revDirs) [])).IsInfixAt
          (x64ScalarMach.prog h) k := hnc1 ▸ hcode
      exact stepTail0_run_ok (isExit := true) hnd hctx_rs hframe_le hn_bd hsp0 hc_node
        hinv hcode1 hu hwp hfr hag
    | hlt =>
      rw [hnd, wp0_hlt] at hwp
      exact False.elim hwp

/-! ## 3. Entry Soundness (`compileFn0_defined` & `compileFn0_fnSpec`) -/

private theorem u32_add_ofNat_succ12 (a : UInt32) (k : Nat) :
    a + UInt32.ofNat (k + 1) = (a + 1) + UInt32.ofNat k := by
  apply u32_ext7
  rw [UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_add, UInt32.toNat_one,
    u32_toNat_ofNat7, u32_toNat_ofNat7, Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_mod_mod,
    Nat.add_assoc, Nat.add_comm k 1]

private theorem u32_add_ofNat_zero12 (a : UInt32) : a + UInt32.ofNat 0 = a := by
  apply u32_ext7
  rw [UInt32.toNat_add, u32_toNat_ofNat7, Nat.zero_mod, Nat.add_zero,
    Nat.mod_eq_of_lt (UInt32.toNat_lt a)]

private theorem pushAgree0_of_forall (esc remUses vslot : Array Nat) (σ : List (BitVec 64)) :
    ∀ (ts : List Ty0) (xs : Tup Val (ty0ListToTy ts)) (nv : UInt32),
      (∀ (j : Nat) (hj : j < ts.length),
        ∃ hsl : (arrGetU0 vslot (nv + UInt32.ofNat j)).toNat < σ.length,
          σ[(arrGetU0 vslot (nv + UInt32.ofNat j)).toNat]'hsl =
            (tupToCanon64s ts xs)[j]'(by rw [tupToCanon64s_length]; exact hj)) →
      PushAgree0 esc remUses vslot nv ts xs σ
  | [], (), _, _ => trivial
  | _ :: rest, (_, restX), nv, h => by
    have h0 := h 0 (Nat.zero_lt_succ rest.length)
    rw [u32_add_ofNat_zero12] at h0
    dsimp only [tupToCanon64s, List.getElem_cons_zero] at h0
    refine ⟨fun _ => h0, pushAgree0_of_forall esc remUses vslot σ rest restX (nv + 1)
      fun j hj => ?_⟩
    have hj' := h (j + 1) (Nat.succ_lt_succ hj)
    dsimp only [tupToCanon64s, List.getElem_cons_succ] at hj'
    rwa [← u32_add_ofNat_succ12 nv j]

private theorem compileFnFinish0_code_eq_aux (fn : TFlatFn0) (esc : Array Nat)
    (bl : BindListOut0) (ctrl0 : CtrlSt0) (hbl_nz : ListNoSpZero0 bl.st.revDirs)
    (rOut : RegaSt0) (rCleanRev : List Dir0)
    (hrOut : regaWorkLoop0 0x7fffffff esc bl.st ctrl0
      [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt] = rOut)
    (hrev : rOut.revDirs = rCleanRev ++ bl.st.revDirs) :
    (compileFnFinish0 fn esc bl ctrl0).1 =
      .label (.sym fn.name) ::
        ((emitSpAdj0 true (x64FrameSizeU0 rOut.maxSlots) []).reverse ++
          (emitFwd0 bl.st.revDirs ++
            patchEpilogues0 (x64FrameSizeU0 rOut.maxSlots) (emitFwd0 rCleanRev) [])) ∧
    (compileFnFinish0 fn esc bl ctrl0).2 = rOut.maxSlots := by
  dsimp only [compileFnFinish0]
  rw [hrOut]
  refine ⟨?_, rfl⟩
  rw [compileFnFinish0_rev_eq fn rOut, emitFwd0_revDirAux0, hrev, emitFwd0_append,
    patchEpilogues0_append,
    show patchEpilogues0 (x64FrameSizeU0 rOut.maxSlots) (emitFwd0 bl.st.revDirs) [] =
        emitFwd0 bl.st.revDirs from
      patchEpilogues0_of_listNoSpZero0 (x64FrameSizeU0 rOut.maxSlots)
        (listNoSpZero0_reverse hbl_nz)]

private theorem compileFnFinish0_code_eq (fn : TFlatFn0) (esc : Array Nat) (bl : BindListOut0)
    (ctrl0 : CtrlSt0) (hbl_nz : ListNoSpZero0 bl.st.revDirs) :
    (compileFnFinish0 fn esc bl ctrl0).1 =
      .label (.sym fn.name) ::
        ((emitSpAdj0 true (x64FrameSizeU0 (regaRunAux0 0x7fffffff esc bl.st ctrl0
          [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt]).1.maxSlots) []).reverse ++
          (emitFwd0 bl.st.revDirs ++
            patchEpilogues0 (x64FrameSizeU0 (regaRunAux0 0x7fffffff esc bl.st ctrl0
              [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt]).1.maxSlots)
              (emitFwd0 (regaRunAux0 0x7fffffff esc { bl.st with revDirs := [] } ctrl0
                [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt]).1.revDirs) [])) ∧
    (compileFnFinish0 fn esc bl ctrl0).2 =
      (regaRunAux0 0x7fffffff esc bl.st ctrl0
        [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt]).1.maxSlots := by
  have hrev := congrArg (fun p => p.1.revDirs) (regaRunAux0_revDirs_append 0x7fffffff esc bl.st
    ctrl0 [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt])
  dsimp only at hrev
  exact compileFnFinish0_code_eq_aux fn esc bl ctrl0 hbl_nz _ _
    (regaRunAux0_fst_eq_regaWorkLoop0 0x7fffffff esc bl.st ctrl0
      [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt]).symm hrev

theorem compileFn0_defined {h : Host} {symName : Sym0 → Sym} (fnIdx : UInt32) (fn : TFlatFn0)
    {k₀ : Nat} (_hg : fn.okGuardsFull = true)
    (hinf : (toAmd64Program symName (compileFn0 fnIdx fn).1).IsInfixAt
      (x64ScalarMach.prog h) k₀) :
    x64ScalarTarget.Defined h (symName fn.name) := by
  let preRes := compileFnPre0 fn
  let cap := Nat.add 32 (tyLenU0 fn.as 0).toNat
  let lblArr0 : Array (List UInt32) := (Array.emptyWithCapacity cap).push []
  let rega0 := RegaSt0.mk 0 0 (Array.emptyWithCapacity cap) preRes.uses []
  let ctrl0 := CtrlSt0.mk fnIdx 1 lblArr0
  let bl := bindEntryArgs0 fn.as 0 [] rega0
  have hbl_nz := (bindEntryArgs0_acc fn.as 0 [] rega0).2.2.2.2.2.1
  have hbl_eq : ({ rega0 with revDirs := [] } : RegaSt0) = rega0 := rfl
  rw [hbl_eq] at hbl_nz
  obtain ⟨hd_eq, _⟩ := compileFnFinish0_code_eq fn preRes.escaped bl ctrl0 hbl_nz
  change (toAmd64Program symName (compileFnFinish0 fn preRes.escaped bl ctrl0).1).IsInfixAt
    (x64ScalarMach.prog h) k₀ at hinf
  rw [hd_eq, toAmd64Program, List.flatMap_cons, dir0ToAmd64, List.singleton_append] at hinf
  exact ⟨k₀, infix_getElem?_zero hinf rfl⟩

private theorem compileFn0_fnSpec_aux {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {ctx : LegalCtx0} (fnIdx : UInt32) (fn : TFlatFn0) (preRes : PreSt0)
    (rega0 : RegaSt0) (ctrl0 : CtrlSt0) (bl : BindListOut0)
    (dirs : List Dir0) (ns : UInt32) (rFull rClean rNode : RegaSt0 × CtrlSt0)
    {n nX k₀ : Nat}
    (hrega_nz : rega0.revDirs = [])
    (hrega_nv : rega0.nextVid = 0)
    (hrega_ms : rega0.maxSlots = 0)
    (hrega_vsz : rega0.vslot.size = 0)
    (hbl_eq : bl = bindEntryArgs0 fn.as 0 [] rega0)
    (hrFull : rFull = regaRunAux0 0x7fffffff preRes.escaped bl.st ctrl0
      [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt])
    (hrClean : rClean = regaRunAux0 0x7fffffff preRes.escaped { bl.st with revDirs := [] } ctrl0
      [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt])
    (hrNode : rNode = regaRunAux0 (UInt32.ofNat (nodeCount0 fn.body)) preRes.escaped
      { bl.st with revDirs := [] } ctrl0
      [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt])
    (hd_eq : dirs =
      .label (.sym fn.name) ::
        ((emitSpAdj0 true (x64FrameSizeU0 ns) []).reverse ++
          (emitFwd0 bl.st.revDirs ++
            patchEpilogues0 (x64FrameSizeU0 ns) (emitFwd0 rClean.1.revDirs) [])))
    (hns_eq : ns = rFull.1.maxSlots)
    (hnv_pre : preRes.nextVid.toNat = fn.as.length + binderCount0 fn.body)
    (hinv0 : RegaStepInv0 ctx fnIdx (maxJumpArity0 fn.body) preRes 1 (preInit0 fn.as).2
      [PreItem0.mk fn.body (preInit0 fn.as).1 0] false bl.st ctrl0
      [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt]
      [TaskMeta0.mk (pushTys0 fn.as []) [] [] none])
    (has_len : fn.as.length ≤ 6) (hrs_len : fn.rs.length ≤ 7) (hctx_rs : ctx.curRs = fn.rs)
    (_hwf : WfNode0 ctx (pushTys0 fn.as []) [] fn.body) (hg : fn.okGuardsFull = true)
    (hframe_le : x64FrameSize ns.toNat ≤ n) (hn_bd : n + 8 ≤ 2 ^ 64)
    (hinf : (toAmd64Program symName dirs).IsInfixAt (x64ScalarMach.prog h) k₀)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hc_node : NodeContracts0 h symName Γ ctx ns n nX fn.body) :
    x64ScalarTarget.FnSpec h (symName fn.name)
      (fun (args : Tup Val (ty0ListToTy fn.as)) m Q X =>
        wp0 Γ symName fn.rs (pushTup args []) [] Q X fn.body m) n nX := by
  intro args m Q X hwp s0 ra0 R hargs _hra hsp0 hmem0
  let initTask := RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt
  let initMeta := TaskMeta0.mk (pushTys0 fn.as []) [] [] none
  let initPre := PreItem0.mk fn.body (preInit0 fn.as).1 0
  let fSz := x64FrameSizeU0 ns
  have hbd := TFlatFn0.okGuardsFull_boundsFitU32 hg
  simp only [TFlatFn0.boundsFitU32, Bool.and_eq_true, decide_eq_true_eq] at hbd
  have hfuel0 : workNodeCount0 ([initTask].map RegaTask0.node) ≤ (0x7fffffff : UInt32).toNat := by
    rw [List.map_singleton]; dsimp only [initTask, workNodeCount0]
    change nodeCount0 fn.body ≤ 2147483647
    omega
  have hpfx_full := regaRunAux0_step_prefix (nodeCount0 fn.body) 0x7fffffff ctx fnIdx
    (maxJumpArity0 fn.body) preRes 1 (preInit0 fn.as).2 [initPre] [] false bl.st ctrl0
    [initTask] [] [initMeta] []
    (by rw [List.map_singleton]; dsimp only [initTask, workNodeCount0]; exact Nat.add_zero _)
    hfuel0 rfl rfl (by simpa only [List.append_nil] using hinv0)
  dsimp only at hpfx_full
  rw [List.append_nil] at hpfx_full
  have hnc_eq : (UInt32.ofNat (nodeCount0 fn.body) : UInt32) =
      UInt32.ofNat (workNodeCount0 ([initTask].map RegaTask0.node)) := by
    rw [List.map_singleton]; dsimp only [initTask, workNodeCount0]; rw [Nat.add_zero]
  have hrFull_eq : rFull =
      ({ rNode.1 with revDirs := rNode.1.revDirs ++ bl.st.revDirs }, rNode.2) := by
    have h1 := hpfx_full.1
    rw [regaRunAux0_nil_eq] at h1
    change regaRunAux0 0x7fffffff preRes.escaped bl.st ctrl0 [initTask] = _ at h1
    rw [← hrFull] at h1
    have hrn_eq : regaRunAux0 (UInt32.ofNat (nodeCount0 fn.body)) preRes.escaped
        { bl.st with revDirs := [] } ctrl0 [initTask] = rNode := hrNode.symm
    dsimp only at hrn_eq
    rwa [hrn_eq] at h1
  have hrClean_eq : rClean.1.revDirs = rNode.1.revDirs := by
    have hr := congrArg (fun p => p.1.revDirs)
      (regaRunAux0_revDirs_append 0x7fffffff preRes.escaped bl.st ctrl0 [initTask])
    dsimp only at hr
    change (regaRunAux0 0x7fffffff preRes.escaped bl.st ctrl0 [initTask]).1.revDirs =
      (regaRunAux0 0x7fffffff preRes.escaped { bl.st with revDirs := [] } ctrl0
        [initTask]).1.revDirs ++ bl.st.revDirs at hr
    rw [← hrFull, ← hrClean, hrFull_eq] at hr
    exact (List.append_inj_left' hr rfl).symm
  let pPrologue := toAmd64Program symName (emitFwd0 (emitSpAdj0 true fSz []))
  let pEntry := toAmd64Program symName (emitFwd0 bl.st.revDirs)
  let pBody := toAmd64Program symName (patchEpilogues0 fSz (emitFwd0 rNode.1.revDirs) [])
  have hd_eq' : dirs =
      .label (.sym fn.name) ::
        (emitFwd0 (emitSpAdj0 true fSz []) ++
          (emitFwd0 bl.st.revDirs ++ patchEpilogues0 fSz (emitFwd0 rNode.1.revDirs) [])) := by
    rw [hd_eq, hrClean_eq]
    rfl
  have hprog_eq : toAmd64Program symName dirs =
      x64Frame.label (symName fn.name) :: (pPrologue ++ pEntry ++ pBody) := by
    rw [hd_eq', toAmd64Program, List.flatMap_cons, dir0ToAmd64, List.singleton_append]
    change _ :: toAmd64Program symName _ = _
    rw [toAmd64Program_append, toAmd64Program_append, List.append_assoc]
    rfl
  rw [hprog_eq] at hinf
  have hadr : x64ScalarMach.labelAddr h (symName fn.name) = x64ScalarMach.addrOf h k₀ :=
    infix_labelAddr_eq hu hinf rfl
  have hstate : x64ScalarMach.mkState s0 (x64ScalarMach.labelAddr h (symName fn.name)) =
      ⟨s0, x64ScalarMach.addrOf h k₀⟩ := by
    rw [hadr]
  rw [hstate]
  change x64ScalarMach.Run h k₀ s0 (fnPost0 h fn.rs Q X s0 ra0 n nX R)
  have hinf_body : (pPrologue ++ (pEntry ++ pBody)).IsInfixAt (x64ScalarMach.prog h) (k₀ + 1) := by
    simpa only [List.append_assoc] using (List.IsInfixAt.cons hinf).2
  refine x64ScalarTarget.frameSpec.label_spec (infix_getElem?_zero hinf rfl) ?_
  have hfr_ns : x64FrameSize ns.toNat ≤ n := hframe_le
  have hsplit_entry :
      region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) n =
        (region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆
          region (s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat))
            (x64FrameSize ns.toNat)) := by
    have hadd : (s0.regs.get64 .rsp - BitVec.ofNat 64 n) +
        BitVec.ofNat 64 (n - x64FrameSize ns.toNat) =
        s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat) := by
      have h1 := sub_add_ofNat_le (s0.regs.get64 .rsp) (n := n)
        (k := n - x64FrameSize ns.toNat) (Nat.sub_le _ _)
      rwa [Nat.sub_sub_self hfr_ns] at h1
    have hs := region_split (a := s0.regs.get64 .rsp - BitVec.ofNat 64 n)
      (n1 := n - x64FrameSize ns.toNat) (n2 := x64FrameSize ns.toNat) (by omega)
    rw [hadd, show n - x64FrameSize ns.toNat + x64FrameSize ns.toNat = n from by omega] at hs
    exact hs
  have hmem0' :
      s0.dmem =⋆ x64ScalarFramePreds.RetAddr (s0.regs.get64 .rsp) ra0 ⋆
        region (s0.regs.get64 .rsp - BitVec.ofNat 64 (x64FrameSize ns.toNat))
          (x64FrameSize ns.toNat) ⋆
        (Eq m ⋆ region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆
          R) := by
    change s0.dmem =⋆ Eq m ⋆
      (region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) n ⋆
        x64ScalarFramePreds.RetAddr (s0.regs.get64 .rsp) ra0) ⋆ R at hmem0
    rw [hsplit_entry] at hmem0
    exact sep_cast hmem0 (by ac_rfl)
  have hpro := emitSpAdj0_prologue_spec (symName := symName) (h := h) (k := k₀ + 1) ns
    (s := s0) (ra := ra0)
    (G := Eq m ⋆ region (s0.regs.get64 .rsp - BitVec.ofNat 64 n)
      (n - x64FrameSize ns.toNat) ⋆ R)
    (post := fnPost0 h fn.rs Q X s0 ra0 n nX R) hmem0'
  refine hpro hinf_body.append.1 fun s1 ⟨hrsp1, hmem1⟩ hfr1 => ?_
  have hcs1 : ∀ r ∈ x64Frame.calleeSaved, s1.regs.get64 r = s0.regs.get64 r := fun r hr =>
    hfr1.1 r (calleeSaved_not_in_rsp_scratch r hr)
  have hargs1 : x64ScalarTarget.ArgsIn args s1 := by
    have ht0 := (argsIn_ty0_iff has_len args s0).mp hargs
    have ht1 : tupAbiHolds0 s1 false 0 fn.as args :=
      tupAbiHolds0_frame (fun r hr => hfr1.1 r hr)
        (fun j _ => abiRegAt0_not_in_rsp_scratch false (UInt32.ofNat (0 + j))) ht0
    exact (argsIn_ty0_iff has_len args s1).mpr ht1
  have hmem1_reg :
      (region (s1.regs.get64 .rsp) (8 * ns.toNat) ⋆
        (Eq m ⋆ x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
          region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ R))
        s1.dmem := by
    rw [hrsp1]
    exact sep_cast hmem1 (by ac_rfl)
  have h8ns : 8 * ns.toNat ≤ 2 ^ 64 := by
    have hge := x64FrameSize_ge ns.toNat
    omega
  obtain ⟨σ1, hσ1_len, hmem1_arr⟩ := region_sep_exists_array64 h8ns hmem1_reg
  have hmaxBd_fn : fn.as.length ≤ preRes.nextVid.toNat + maxJumpArity0 fn.body := by omega
  have hmaxBd_31 : preRes.nextVid.toNat + maxJumpArity0 fn.body < 2 ^ 31 := by omega
  have hbl_spec := bindEntryArgs0_spec fn.as 0 [] rega0
    (preRes.nextVid.toNat + maxJumpArity0 fn.body)
    (by rw [hrega_vsz, hrega_nv, UInt32.toNat_zero]) hrega_nv
    (by simp only [UInt32.toNat_zero, Nat.zero_add]; exact hmaxBd_fn)
    hmaxBd_31 (by rw [hrega_ms])
  dsimp only at hbl_spec
  rw [← hbl_eq, hrega_nv, UInt32.toNat_zero, Nat.zero_add] at hbl_spec
  have hbl_ms_le : bl.st.maxSlots.toNat ≤ ns.toNat := by
    have hpfx0 := regaRunAux0_step_prefix 0 0x7fffffff ctx fnIdx (maxJumpArity0 fn.body)
      preRes 1 (preInit0 fn.as).2 [] [initPre] false bl.st ctrl0 [] [initTask] [] [initMeta]
      rfl (Nat.zero_le _) rfl rfl (by simpa only [List.nil_append] using hinv0)
    dsimp only at hpfx0
    have hr0_eq : (regaRunAux0 (UInt32.ofNat 0) preRes.escaped { bl.st with revDirs := [] }
        ctrl0 []).1.maxSlots = bl.st.maxSlots := by
      rw [regaRunAux0_nil]
    rw [hr0_eq, List.nil_append] at hpfx0
    have hle_rf := hpfx0.2.2.1
    change bl.st.maxSlots.toNat ≤
      (regaRunAux0 0x7fffffff preRes.escaped bl.st ctrl0 [initTask]).1.maxSlots.toNat at hle_rf
    rwa [← hrFull, ← hns_eq] at hle_rf
  have has_σ1 : fn.as.length ≤ σ1.length := by
    rw [hσ1_len]
    have hpool := hbl_spec.2.2.2.2.2.2.1
    have hnxt_eq : bl.nxt.toNat = fn.as.length := hbl_spec.2.2.1
    exact Nat.le_trans (hnxt_eq ▸ hpool.2.2.1) hbl_ms_le
  have hbe := bindEntryArgs0_run_spec (symName := symName) (h := h)
    (G := Eq m ⋆ x64ScalarFramePreds.Saved (s0.regs.get64 .rsp) ra0 ns.toNat ⋆
      region (s0.regs.get64 .rsp - BitVec.ofNat 64 n) (n - x64FrameSize ns.toNat) ⋆ R)
    (post := fnPost0 h fn.rs Q X s0 ra0 n nX R) fn.as (k₀ + 1 + pPrologue.length) rega0
    args σ1 s1 (preRes.nextVid.toNat + maxJumpArity0 fn.body)
    has_len (by rw [hrega_vsz, hrega_nv, UInt32.toNat_zero]) hrega_nv hmaxBd_fn hmaxBd_31
    hrega_ms has_σ1 hargs1 hmem1_arr
  dsimp only at hbe
  have hrega_clean : ({ rega0 with revDirs := [] } : RegaSt0) = rega0 := by
    cases rega0; simp only at hrega_nz; subst hrega_nz; rfl
  have hbl0_eq : bindEntryArgs0 fn.as 0 [] { rega0 with revDirs := [] } = bl := by
    rw [hrega_clean, ← hbl_eq]
  have hinf_entry :
      (toAmd64Program symName
        (emitFwd0 (bindEntryArgs0 fn.as 0 [] { rega0 with revDirs := [] }).st.revDirs)).IsInfixAt
        (x64ScalarMach.prog h) (k₀ + 1 + pPrologue.length) := by
    rw [hbl0_eq]
    exact hinf_body.append.2.append.1
  refine hbe hinf_entry fun s2 ⟨σ2, hσ2_len, hslots2, hmem2⟩ hfr2 => ?_
  have hrsp2 : s2.regs.get64 .rsp = s1.regs.get64 .rsp :=
    hfr2.1 .rsp rsp_not_mem_scratchAndAbi
  have hfr2_inv : FnFrameInv0 ns s0 ra0 n R m s2 σ2 := by
    refine ⟨hσ2_len.trans hσ1_len, hrsp2.trans hrsp1,
      fun r hr => (hfr2.1 r (calleeSaved_not_mem_scratchAndAbi r hr)).trans (hcs1 r hr), ?_⟩
    rw [hrsp2] at hmem2 ⊢
    exact sep_cast hmem2 (by dsimp only [x64ScalarFramePreds, x64FramePreds]; ac_rfl)
  have hpa2 : PushAgree0 preRes.escaped bl.st.remUses bl.st.vslot 0 fn.as args σ2 := by
    refine pushAgree0_of_forall preRes.escaped bl.st.remUses bl.st.vslot σ2 fn.as args 0
      fun j hj => ?_
    have hz_j : (0 + UInt32.ofNat j : UInt32) = UInt32.ofNat j := UInt32.zero_add _
    rw [hz_j]
    have hsl_j := hbl_spec.2.2.2.2.2.2.2.2 j hj
    simp only [Nat.zero_add] at hsl_j
    have hlt_σ2 : (arrGetU0 bl.st.vslot (UInt32.ofNat j)).toNat < σ2.length := by
      rw [hsl_j, u32_toNat_ofNat7, Nat.mod_eq_of_lt (by omega), hσ2_len]
      exact Nat.lt_of_lt_of_le hj has_σ1
    have hget_nat : ∀ (xs : List (BitVec 64)) (a b : Nat) (he : a = b)
        (ha : a < xs.length) (hb : b < xs.length), xs[a]'ha = xs[b]'hb := fun _ _ _ he _ _ => by
      subst he; rfl
    have hsl_idx : (arrGetU0 bl.st.vslot (UInt32.ofNat j)).toNat =
        (arrGetU0 (bindEntryArgs0 fn.as 0 [] { rega0 with revDirs := [] }).st.vslot
          (UInt32.ofNat j)).toNat := by
      rw [hbl0_eq]
    exact ⟨hlt_σ2, (hget_nat σ2 _ _ hsl_idx hlt_σ2 _).trans (hslots2 j hj)⟩
  have haux2 := pushFresh_slotsAgree0_aux preRes.escaped (preInit0 fn.as).2 bl.st
    initPre initTask σ2 fn.as args 0 [] [] []
    (by simp only [UInt32.toNat_zero, Nat.zero_add]; omega)
    rfl trivial (fun _ hm => nomatch hm) (fun _ h => absurd h (Nat.not_lt_zero _)) hpa2
  have hag2 : SlotsAgree0 preRes.escaped (preInit0 fn.as).2 bl.st initPre initTask
      (pushTys0 fn.as []) (pushTup args []) σ2 := by
    have hget : ∀ (l1 l2 : List UInt32) (he : l1 = l2) (i : Nat)
        (h1 : i < l1.length) (h2 : i < l2.length), l1[i]'h1 = l2[i]'h2 := by
      intro _ _ he _ _ _; cases he; rfl
    refine ⟨?_, haux2.2.1, fun idx hi hlv => ?_⟩
    · dsimp only [initTask]
      change bl.venv.length = (pushTup args []).length
      rw [hbl_spec.1]
      exact haux2.1
    · have hv_eq : initTask.venv = pushFreshVids0 fn.as.length 0 [] := hbl_spec.1
      have hi' : idx < (pushFreshVids0 fn.as.length 0 []).length := hv_eq ▸ hi
      have hge := hget initTask.venv (pushFreshVids0 fn.as.length 0 []) hv_eq idx hi hi'
      rw [hge] at hlv ⊢
      exact haux2.2.2 idx hi' (by
        simpa only [LiveInTask0, hv_eq] using hlv)
  have hinf_node : pBody.IsInfixAt (x64ScalarMach.prog h)
      (k₀ + 1 + pPrologue.length + pEntry.length) := by
    simpa only [Nat.add_assoc] using hinf_body.append.2.append.2
  have hns_run :
      (regaRunAux0 0x7fffffff preRes.escaped bl.st ctrl0 [initTask]).1.maxSlots = ns := by
    change (regaRunAux0 0x7fffffff preRes.escaped bl.st ctrl0
      [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt]).1.maxSlots = ns
    rw [← hrFull, hns_eq]
  have hinf_run : (toAmd64Program symName (patchEpilogues0 (x64FrameSizeU0 ns)
      (emitFwd0 (regaRunAux0 (UInt32.ofNat (nodeCount0 initTask.node)) preRes.escaped
        { bl.st with revDirs := [] } ctrl0 [initTask]).1.revDirs) [])).IsInfixAt
      (x64ScalarMach.prog h)
      (k₀ + 1 + pPrologue.length +
        (toAmd64Program symName
          (emitFwd0 (bindEntryArgs0 fn.as 0 [] { rega0 with revDirs := [] }).st.revDirs)).length)
      := by
    dsimp only [initTask]
    rw [← hrNode, hbl0_eq]
    exact hinf_node
  dsimp only at hinf_run
  exact regaTask0_run_ok (nodeCount0 fn.body) rfl hrs_len hctx_rs hframe_le hn_bd hsp0 hu
    hinv0 rfl rfl hfuel0 hns_run hinf_run hwp hfr2_inv hag2 trivial hc_node

private theorem compileFnFinish0_fnSpec {h : Host} {symName : Sym0 → Sym} {Γ : Env}
    {ctx : LegalCtx0} (fnIdx : UInt32) (fn : TFlatFn0) (preRes : PreSt0)
    (rega0 : RegaSt0) (ctrl0 : CtrlSt0) (bl : BindListOut0) {n nX k₀ : Nat}
    (hrega_nz : rega0.revDirs = []) (hrega_nv : rega0.nextVid = 0)
    (hrega_ms : rega0.maxSlots = 0) (hrega_vsz : rega0.vslot.size = 0)
    (hbl_eq : bl = bindEntryArgs0 fn.as 0 [] rega0)
    (hnv_pre : preRes.nextVid.toNat = fn.as.length + binderCount0 fn.body)
    (hinv0 : RegaStepInv0 ctx fnIdx (maxJumpArity0 fn.body) preRes 1 (preInit0 fn.as).2
      [PreItem0.mk fn.body (preInit0 fn.as).1 0] false bl.st ctrl0
      [RegaTask0.mk 0 fn.body bl.venv [] bl.free bl.nxt]
      [TaskMeta0.mk (pushTys0 fn.as []) [] [] none])
    (has_len : fn.as.length ≤ 6) (hrs_len : fn.rs.length ≤ 7) (hctx_rs : ctx.curRs = fn.rs)
    (hwf : WfNode0 ctx (pushTys0 fn.as []) [] fn.body) (hg : fn.okGuardsFull = true)
    (hframe_le : x64FrameSize (compileFnFinish0 fn preRes.escaped bl ctrl0).2.toNat ≤ n)
    (hn_bd : n + 8 ≤ 2 ^ 64)
    (hinf : (toAmd64Program symName (compileFnFinish0 fn preRes.escaped bl ctrl0).1).IsInfixAt
      (x64ScalarMach.prog h) k₀)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hc_node : NodeContracts0 h symName Γ ctx
      (compileFnFinish0 fn preRes.escaped bl ctrl0).2 n nX fn.body) :
    x64ScalarTarget.FnSpec h (symName fn.name)
      (fun (args : Tup Val (ty0ListToTy fn.as)) m Q X =>
        wp0 Γ symName fn.rs (pushTup args []) [] Q X fn.body m) n nX := by
  have hrega_clean : ({ rega0 with revDirs := [] } : RegaSt0) = rega0 := by
    cases rega0; simp only at hrega_nz; subst hrega_nz; rfl
  have hbl_nz : ListNoSpZero0 bl.st.revDirs := by
    have hacc := (bindEntryArgs0_acc fn.as 0 [] rega0).2.2.2.2.2.1
    rw [hrega_clean, ← hbl_eq] at hacc
    exact hacc
  obtain ⟨hd_eq, hns_eq⟩ := compileFnFinish0_code_eq fn preRes.escaped bl ctrl0 hbl_nz
  exact compileFn0_fnSpec_aux fnIdx fn preRes rega0 ctrl0 bl
    (compileFnFinish0 fn preRes.escaped bl ctrl0).1
    (compileFnFinish0 fn preRes.escaped bl ctrl0).2 _ _ _
    hrega_nz hrega_nv hrega_ms hrega_vsz hbl_eq rfl rfl rfl
    (by rw [hns_eq]; exact hd_eq) hns_eq hnv_pre hinv0
    has_len hrs_len hctx_rs hwf hg hframe_le hn_bd hinf hu hc_node

theorem compileFn0_fnSpec {h : Host} {symName : Sym0 → Sym} {Γ : Env} {ctx : LegalCtx0}
    (fnIdx : UInt32) (fn : TFlatFn0) {n nX k₀ : Nat}
    (has_len : fn.as.length ≤ 6) (hrs_len : fn.rs.length ≤ 7) (hctx_rs : ctx.curRs = fn.rs)
    (hwf : WfNode0 ctx (pushTys0 fn.as []) [] fn.body) (hg : fn.okGuardsFull = true)
    (hframe_le : x64FrameSize (compileFn0 fnIdx fn).2.toNat ≤ n) (hn_bd : n + 8 ≤ 2 ^ 64)
    (hinf : (toAmd64Program symName (compileFn0 fnIdx fn).1).IsInfixAt
      (x64ScalarMach.prog h) k₀)
    (hu : x64ScalarTarget.LabelsUnique h)
    (hc_node : NodeContracts0 h symName Γ ctx (compileFn0 fnIdx fn).2 n nX fn.body) :
    x64ScalarTarget.FnSpec h (symName fn.name)
      (fun (args : Tup Val (ty0ListToTy fn.as)) m Q X =>
        wp0 Γ symName fn.rs (pushTup args []) [] Q X fn.body m) n nX := by
  have hpre := compileFnPre0_inv hwf hg
  dsimp only at hpre
  have hinv0 := regaStepInv0_init fnIdx fn hwf hg
  dsimp only [compileFn0] at hframe_le hinf hc_node
  dsimp only at hinv0
  exact compileFnFinish0_fnSpec fnIdx fn (compileFnPre0 fn)
    (RegaSt0.mk 0 0 (Array.emptyWithCapacity (Nat.add 32 (tyLenU0 fn.as 0).toNat))
      (compileFnPre0 fn).uses [])
    (CtrlSt0.mk fnIdx 1
      ((Array.emptyWithCapacity (Nat.add 32 (tyLenU0 fn.as 0).toNat)).push []))
    (bindEntryArgs0 fn.as 0 []
      (RegaSt0.mk 0 0 (Array.emptyWithCapacity (Nat.add 32 (tyLenU0 fn.as 0).toNat))
        (compileFnPre0 fn).uses []))
    rfl rfl rfl (by simp) rfl hpre.2.1 hinv0
    has_len hrs_len hctx_rs hwf hg hframe_le hn_bd hinf hu hc_node

end LeanQbe.T.Bootstrap0
