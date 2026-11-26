module

public import LeanQbe.T.Vll.FromWord
import LeanQbe.T.Vll.FromWordLemmas0
import LeanQbe.T.Unified.CfgContifyLemmas
import LeanQbe.T.BedrockWord.Ops
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.TargetLemmas

/-!
# Memory, Private Frame, CodeMap Well-Formedness & Budget Lemmas (`Vll.FromWordLemmas1`)

Arch-free intermediate proof layer for `LeanQbe.T.Vll.FromWord`:
* §1. L0 memory loads/stores (`lowerMemLoad_bodyWp`, `lowerMemStore_bodyWp`), `PrivSlotsRel`,
      `emitPrivFrameInit_bodyWp`, `emitPrivFlush_bodyWp`, `emitDynAliasGuard_bodyWp`, and
      promoted/guarded private-frame memory ops (`lowerMemLoad_priv_direct_bodyWp`,
      `lowerMemStore_priv_direct_bodyWp`, `lowerMemLoad_priv_slot_bodyWp`,
      `lowerMemStore_priv_slot_bodyWp`).
* §2. `buildVllSymAddr`, `finalizeVllCodeMap_wf`, `VllCodeMap.Wf` preservation for `fromWord` and
      `fromWordContify`, `symAddr` entry agreement, and `witnessBudgets` stack bounds.

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

/-! ## §0. Generic Helpers, `WordRegsRel`, and `loadLevelInto_bodyWp` -/

theorem locOf_slot_ne_lt_sb {A : Arch} (b : WordRegBind A) {sb lvl k : Nat} (hk : k < sb) :
    locOf b sb lvl ≠ .slot k := by
  intro he; have := locOf_slot_ge_sb b sb lvl k he; omega

theorem wordRegsRel_upd_ge6' {A : Arch} {b : WordRegBind A} (hwf : b.Wf) {rw : Regs}
    {s s' : MachSt A} (hr : WordRegsRel b rw s) {sb d : Nat} (h6 : 6 ≤ d) {rd : A.Reg}
    (hl : locOf b sb d = .gpr rd) (hne : ∀ q, q ≠ rd → s'.gpr q = s.gpr q) :
    WordRegsRel b rw s' := by
  have hneq : ∀ {w : A.Reg}, w ∈ b.wordRegs → w ≠ rd :=
    fun hw => wordRegs_ne_locOf_ge6 hwf h6 hl hw
  exact ⟨(hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.2.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.2.2.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.2.2.2.1,
    (hne _ (hneq (by simp [WordRegBind.wordRegs]))).trans hr.2.2.2.2.2⟩

theorem loadLevelInto_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d lvl : Nat} {dst : A.Reg} {t : Ty} {v : Val t}
    {bvs : List ((u : Ty) × Val u)} {s : MachSt A} {slots : List (BitVec 64)}
    {G : Mem 64 → Prop} {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)}
    {H : Xcap.Halt (MachSt A)}
    (hdst : dst ∈ b.workRegs) (hlt : lvl < d)
    (hget : listGet? bvs (d - 1 - lvl) = some ⟨t, v⟩)
    (he : EnvRel b sb d bvs s)
    (_hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (hk : ∀ s',
      (∀ q, q ≠ dst → s'.gpr q = s.gpr q) →
      ValHolds64 t v (s'.gpr dst) →
      s'.mem = s.mem →
      EnvRel b sb d bvs s' →
      Kpost s') :
    bodyWp A symAddr (loadLevelInto b sb dst lvl) Kpost Ψ H s := by
  have hev := he.2 (d - 1 - lvl) (by omega)
  rw [hget] at hev
  have hsub : d - 1 - (d - 1 - lvl) = lvl := by omega
  rw [hsub] at hev
  dsimp only [loadLevelInto]
  cases hl : locOf b sb lvl with
  | gpr r =>
    dsimp only [LocHolds] at hev; rw [hl] at hev
    by_cases hrd : r = dst
    · subst hrd; simp only [beq_self_eq_true, ↓reduceIte, bodyWp]
      exact hk s (fun _ _ => rfl) hev rfl he
    · have hne : (r == dst) = false := beq_false_of_ne hrd
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      refine instrWp_mov (hk _ (fun q hq => MachSt.gpr_setGprW_ne s .w64 _ hq) ?_ rfl
        ((envRel_setGprW_work hwf sb d bvs s .w64 hdst _).mpr he))
      simpa only [MachSt.gpr_setGprW_same, hawf.writeSub_w64, BitVec.setWidth_eq] using hev
  | slot k =>
    dsimp only [LocHolds] at hev; rw [hl] at hev
    obtain ⟨g, hld, hval⟩ := hev
    refine instrWp_slotLd hld (hk _ (fun q hq => MachSt.gpr_setGpr_ne s g hq) ?_ rfl
      ((envRel_setGpr_work hwf sb d bvs s hdst g).mpr he))
    simpa only [MachSt.gpr_setGpr_same] using hval

/-! ## §1. Plain Memory Ops, Private Frame Init/Flush, Alias Guard, and Promoted Memory Ops -/

private theorem loadVal_of_tyToWidth {A : Arch} {m : Mem 64} {t : Ty} {w : Width} {a : BitVec 64}
    {v : Val t} {old : BitVec 64} (hw : tyToWidth? t = some w) (hld : loadVal m t a = some v) :
    ∃ bv : BitVec w.bits, loadVal m w.toTy a = some bv ∧
      ValHolds64 t v (LoadExt.zx.apply A w old bv) := by
  rcases tyToWidth?_spec hw with ⟨rfl, rfl⟩ | rfl
  · refine ⟨BitVec.ofNat 8 v.toNat, loadVal_bits8_of_bool hld, ?_⟩
    dsimp only [ValHolds64, LoadExt.apply]
    simp [BitVec.setWidth_setWidth_of_le (BitVec.ofNat 8 v.toNat) (by decide : 8 ≤ 64)]
  · refine ⟨v, hld, Width.bits_le_64 w, ?_⟩
    dsimp only [LoadExt.apply]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [hi, Nat.lt_of_lt_of_le hi (Width.bits_le_64 w)]

theorem lowerMemLoad_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax : Nat} {t : Ty} {a : Arg K i64}
    {bvs : List ((u : Ty) × Val u)} {aa : Arg Val i64} {rw : Regs}
    {slots : List (BitVec 64)} {mL0 : Mem 64} {G : Mem 64 → Prop} {s : MachSt A}
    {is : List (Instr A)} {v : Val t}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem)
    (ha : denoteArg bvs a = some aa) (hld : loadVal mL0 t aa.val = some v)
    (hlo : lowerMemLoad b sb d t a = .ok is)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      EnvRel b sb (d + 1) (⟨t, v⟩ :: bvs) s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mL0 ⋆ G)) s'.mem → Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  dsimp only [lowerMemLoad, Except.bind] at hlo
  cases hw : tyToWidth? t with
  | none => simp [hw] at hlo
  | some w =>
    simp only [hw] at hlo
    cases h1 : loadArgToGpr b sb d b.w1 a <;> rw [h1] at hlo; · cases hlo
    cases hlo; rename_i p; rcases p with ⟨ca, ra⟩
    have hwk := w_mem_workRegs b; have hwsp := work_not_sp hwf
    refine bodyWp_append ca _ _ (loadArgToGpr_bodyWp hwf hwk.2.1 he ha hm h1 ?_)
    intro s1 hs1_ne hva hm1 he1
    have hsp1 : s1.gpr A.abi.sp = s.gpr A.abi.sp := hs1_ne A.abi.sp hwsp.2.2.1.symm
    have hr1 := wordRegsRel_updWork hwf hr b.w1 hwk.2.1 hs1_ne
    have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s1.mem := by
      simpa [hsp1, hm1] using hm
    have hva' : s1.gpr ra = aa.val := by
      dsimp only [ValHolds64] at hva; simpa [BitVec.setWidth_eq] using hva.2
    have hm1_eq : (Eq mL0 ⋆ (array64 (s1.gpr A.abi.sp) slots ⋆ G)) s1.mem :=
      sep_cast hm1' (by ac_rfl)
    have hcore : ∀ rd (hrd : rd = b.w0 ∨ locOf b sb d = .gpr rd),
        bodyWp A symAddr [.load w .zx rd (.baseDisp ra 0)] (fun s' =>
          ValHolds64 t v (s'.gpr rd) ∧ s'.gpr A.abi.sp = s1.gpr A.abi.sp ∧
          EnvRel b sb d bvs s' ∧ WordRegsRel b rw s' ∧
          ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
            (∀ j < sb, slots'[j]? = slots[j]?) ∧
            (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mL0 ⋆ G)) s'.mem) Ψ H s1 := by
      intro rd hrd
      obtain ⟨bv, hld_w, hval_bv⟩ := loadVal_of_tyToWidth (A := A) (old := s1.gpr rd) hw hld
      have hld_mem : loadVal s1.mem w.toTy (AddrArg.baseDisp ra 0 |>.eval s1.gpr) = some bv := by
        simpa [AddrArg.eval, hva'] using loadVal_frame hm1_eq hld_w
      refine instrWp_load hld_mem ?_
      have hsp_rd : A.abi.sp ≠ rd := by
        rcases hrd with rfl | hlrd
        · exact hwsp.2.1.symm
        · exact (locOf_gpr_ne_sp hwf sb d hlrd).symm
      have hspr : (s1.setGpr rd (LoadExt.zx.apply A w (s1.gpr rd) bv)).gpr A.abi.sp =
          s1.gpr A.abi.sp := MachSt.gpr_setGpr_ne _ _ hsp_rd
      refine ⟨by simpa [MachSt.gpr_setGpr_same] using hval_bv, hspr, ?_, ?_,
        slots, rfl, fun _ _ => rfl, by simpa [hspr] using hm1'⟩
      · rcases hrd with rfl | hlrd
        · exact (envRel_setGpr_work hwf sb d bvs s1 hwk.1 _).mpr he1
        · exact envRel_setGpr_new hwf hlrd _ he1
      · rcases hrd with rfl | hlrd
        · exact wordRegsRel_updWork hwf hr1 b.w0 hwk.1
            (fun q hq => MachSt.gpr_setGpr_ne _ _ hq)
        · exact wordRegsRel_upd_ge6' hwf hr1 h6 hlrd
            (fun q hq => MachSt.gpr_setGpr_ne _ _ hq)
    refine emitToLoc_bodyWp hwf hd hbound (fun rd h => hcore rd (Or.inr h))
      (fun _ _ => hcore b.w0 (Or.inl rfl)) ?_
    intro s' slots' hlen hsb he' hr' hsp' hm'
    exact hk s' slots' hlen hsb he' hr' (hsp'.trans hsp1) hm'

private theorem store_of_tyToWidth {m M : Mem 64} {F : Mem 64 → Prop}
    {t : Ty} {w : Width} {a : BitVec 64} {v : Val t} {g : BitVec 64}
    (hw : tyToWidth? t = some w) (hv : ValHolds64 t v g) (hm : (Eq m ⋆ F) M)
    (hst : storeOk m t a) :
    storeOk M w.toTy a ∧
      (Eq (storeMem m t a v) ⋆ F) (storeMem M w.toTy a (g.setWidth w.bits)) := by
  rcases tyToWidth?_spec hw with ⟨rfl, rfl⟩ | rfl
  · dsimp only [ValHolds64, Width.bits] at hv
    have hst8 : storeOk M (.bits 8) a := storeOk_frame hm ((storeOk_bool_iff_bits8 m a).mp hst)
    have hmem := storeMem_frame hm ((storeOk_bool_iff_bits8 m a).mp hst) (BitVec.ofNat 8 v.toNat)
    rw [storeMem_bits8_eq_bool] at hmem
    exact ⟨hst8, by simpa [hv] using hmem⟩
  · dsimp only [ValHolds64] at hv
    exact ⟨storeOk_frame hm hst, by simpa [hv.2] using storeMem_frame hm hst v⟩

theorem lowerMemStore_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax : Nat} {t : Ty} {v : Arg K t} {a : Arg K i64}
    {bvs : List ((u : Ty) × Val u)} {va : Arg Val t} {aa : Arg Val i64} {rw : Regs}
    {slots : List (BitVec 64)} {mL0 : Mem 64} {G : Mem 64 → Prop} {s : MachSt A}
    {is : List (Instr A)}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d ≤ dMax) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem)
    (hvD : denoteArg bvs v = some va) (haD : denoteArg bvs a = some aa)
    (hst : storeOk mL0 t aa.val)
    (hlo : lowerMemStore b sb d v a = .ok is)
    (hk : ∀ s',
      EnvRel b sb d bvs s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots ⋆ (Eq (storeMem mL0 t aa.val va.val) ⋆ G)) s'.mem →
      Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  dsimp only [lowerMemStore, Except.bind] at hlo
  cases hw : tyToWidth? t with
  | none => simp [hw] at hlo
  | some w =>
    simp only [hw] at hlo
    cases h1 : loadArgToGpr b sb d b.w1 v <;> rw [h1] at hlo; · cases hlo
    cases h2 : loadArgToGpr b sb d b.w2 a <;> rw [h2] at hlo; · cases hlo
    cases hlo; rename_i p1 p2; rcases p1 with ⟨cv, rv⟩; rcases p2 with ⟨ca, ra⟩
    have hwk := w_mem_workRegs b; have hwsp := work_not_sp hwf
    have hsl : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots.length :=
      envRel_slots_bound b hd hbound
    have hv_ne_w2 : rv ≠ b.w2 := by
      intro heq; subst heq; cases v with
      | imm c =>
        dsimp only [loadArgToGpr] at h1; cases him : immToBitVec64 t c <;> simp [him] at h1
        exact (wordRegBind_work_ne hwf).2.2.2.2.2 h1.2
      | var idx =>
        dsimp only [loadArgToGpr] at h1; split at h1
        · cases hlx : locOf b sb (d - 1 - idx) with
          | gpr _ => simp [hlx] at h1; exact (locOf_gpr_ne_work hwf sb _ hlx).2.2.2 h1.2
          | slot _ => simp [hlx] at h1; exact (wordRegBind_work_ne hwf).2.2.2.2.2 h1.2
        · cases h1
    rw [List.append_assoc]
    refine bodyWp_append cv _ _ (loadArgToGpr_bodyWp hwf hwk.2.1 he hvD hm h1 ?_)
    intro s1 hs1_ne hvv hm1 he1
    have hsp1 : s1.gpr A.abi.sp = s.gpr A.abi.sp := hs1_ne A.abi.sp hwsp.2.2.1.symm
    have hr1 := wordRegsRel_updWork hwf hr b.w1 hwk.2.1 hs1_ne
    have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s1.mem := by
      simpa [hsp1, hm1] using hm
    refine bodyWp_append ca _ _ (loadArgToGpr_bodyWp hwf hwk.2.2 he1 haD hm1' h2 ?_)
    intro s2 hs2_ne hva hm2 he2
    have hsp2 : s2.gpr A.abi.sp = s.gpr A.abi.sp := (hs2_ne A.abi.sp hwsp.2.2.2.symm).trans hsp1
    have hr2 := wordRegsRel_updWork hwf hr1 b.w2 hwk.2.2 hs2_ne
    have hvv2 : ValHolds64 t va.val (s2.gpr rv) := by
      simpa [hs2_ne rv hv_ne_w2] using hvv
    have hva2 : s2.gpr ra = aa.val := by
      dsimp only [ValHolds64] at hva; simpa [BitVec.setWidth_eq] using hva.2
    have hm2' : (array64 (s2.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s2.mem := by
      simpa [hsp2, hm2, hm1] using hm
    have hm2_eq : (Eq mL0 ⋆ (array64 (s2.gpr A.abi.sp) slots ⋆ G)) s2.mem :=
      sep_cast hm2' (by ac_rfl)
    obtain ⟨hstM, hmemM⟩ := store_of_tyToWidth hw hvv2 hm2_eq hst
    have hst_addr : storeOk s2.mem w.toTy (AddrArg.baseDisp ra 0 |>.eval s2.gpr) := by
      simpa [AddrArg.eval, hva2] using hstM
    have hmem_post : (array64 (s2.gpr A.abi.sp) slots ⋆
        (Eq (storeMem mL0 t aa.val va.val) ⋆ G))
        (storeMem s2.mem w.toTy (AddrArg.baseDisp ra 0 |>.eval s2.gpr)
          ((s2.gpr rv).setWidth w.bits)) := by
      have hzero : (0 : Int64).toBitVec = 0#64 := rfl
      simp only [AddrArg.eval, hzero, hva2, BitVec.add_zero]
      exact sep_cast hmemM (by ac_rfl)
    have hm2_triv : (array64 (s2.gpr A.abi.sp) slots ⋆ fun _ => True) s2.mem := by
      rw [sep_comm]; exact sep_mono (fun _ _ => trivial) (by rw [sep_comm]; exact hm2')
    have hmpost_triv : (array64 (s2.gpr A.abi.sp) slots ⋆ fun _ => True)
        (storeMem s2.mem w.toTy (AddrArg.baseDisp ra 0 |>.eval s2.gpr)
          ((s2.gpr rv).setWidth w.bits)) := by
      rw [sep_comm]; exact sep_mono (fun _ _ => trivial) (by rw [sep_comm]; exact hmem_post)
    refine instrWp_store hst_addr ?_
    refine hk _ (envRel_setMem_of_array (R' := fun _ => True) hsl hm2_triv hmpost_triv he2)
      ((wordRegsRel_setMem _ _ _ _).mpr hr2) hsp2
      (by simpa [MachSt.mem_setMem, MachSt.gpr_setMem] using hmem_post)

/-- Combined private-frame invariant pairing Stage-1 `FrameRel` with hardware slot `nPriv`
storing L0 entry `sp₀`. When `nPriv = 0`, simplifies to `mConc = mPub`. -/
def PrivSlotsRel (nPriv : Nat) (sp0 : BitVec 64) (slots : List (BitVec 64))
    (mConc mPub : Mem 64) : Prop :=
  if nPriv = 0 then mConc = mPub
  else
    slots.length ≥ nPriv + 1 ∧ nPriv ≤ 64 ∧ slots[nPriv]? = some sp0 ∧
    FrameRel nPriv sp0 (slots.take nPriv) mConc mPub

theorem privSlotsRel_zero {sp0 : BitVec 64} {slots : List (BitVec 64)} {mConc mPub : Mem 64}
    (h : PrivSlotsRel 0 sp0 slots mConc mPub) : mConc = mPub := by
  simpa [PrivSlotsRel] using h

theorem privSlotsRel_slot_sp0 {nPriv : Nat} {sp0 : BitVec 64} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} (hpos : 0 < nPriv) (h : PrivSlotsRel nPriv sp0 slots mConc mPub) :
    nPriv ≤ 64 ∧ nPriv + 1 ≤ slots.length ∧ slots[nPriv]? = some sp0 := by
  dsimp only [PrivSlotsRel] at h; rw [ite_eq_right (Nat.ne_of_gt hpos)] at h
  exact ⟨h.2.1, h.1, h.2.2.1⟩

private theorem privSlotsRel_nonZero_fields {nPriv : Nat} {sp0 : BitVec 64}
    {slots : List (BitVec 64)} {mConc mPub : Mem 64} (hpos : 0 < nPriv)
    (h : PrivSlotsRel nPriv sp0 slots mConc mPub) :
    slots.length ≥ nPriv + 1 ∧ nPriv ≤ 64 ∧ slots[nPriv]? = some sp0 ∧
      FrameRel nPriv sp0 (slots.take nPriv) mConc mPub := by
  dsimp only [PrivSlotsRel] at h; rw [ite_eq_right (Nat.ne_of_gt hpos)] at h; exact h

private theorem writeSlots_eq_foldl (sp0 : BitVec 64) :
    ∀ (k : Nat) (vs : List (BitVec 64)) (m : Mem 64),
      writeSlots m sp0 k vs =
        (vs.foldl (fun p v => (p.1 + 1, storeMem p.2 i64 (slotAddr sp0 p.1) v)) (k, m)).2
  | _, [], _ => rfl
  | k, _ :: vs, _ => writeSlots_eq_foldl sp0 (k + 1) vs _

theorem privSlotsRel_foldl_iff {nPriv : Nat} {sp0 : BitVec 64} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} :
    PrivSlotsRel nPriv sp0 slots mConc mPub ↔
      if nPriv = 0 then mConc = mPub
      else
        slots.length ≥ nPriv + 1 ∧ nPriv ≤ 64 ∧ slots[nPriv]? = some sp0 ∧
        (slots.take nPriv).length = nPriv ∧
        (∀ k < nPriv, storeOk mPub i64 (slotAddr sp0 k)) ∧
        mConc = ((slots.take nPriv).foldl
          (fun (p : Nat × Mem 64) v => (p.1 + 1, storeMem p.2 i64 (slotAddr sp0 p.1) v))
          (0, mPub)).2 := by
  by_cases hn : nPriv = 0
  · subst hn; simp [PrivSlotsRel]
  · simp only [PrivSlotsRel, FrameRel, hn, ↓reduceIte, writeSlots_eq_foldl]
    exact ⟨fun ⟨h1, h2, h3, h4, _, h6, h7⟩ => ⟨h1, h2, h3, h4, h6, h7⟩,
      fun ⟨h1, h2, h3, h4, h6, h7⟩ => ⟨h1, h2, h3, h4, h2, h6, h7⟩⟩

private theorem writeSlots_eq_self_of_loadVal (sp0 : BitVec 64) :
    ∀ (base : Nat) (vs : List (BitVec 64)) (m : Mem 64),
      base + vs.length ≤ 64 →
      (∀ (j : Nat) (hj : j < vs.length),
        loadVal m i64 (slotAddr sp0 (base + j)) = some (vs[j]'hj)) →
      writeSlots m sp0 base vs = m
  | _, [], _, _, _ => rfl
  | base, v :: vs, m, hbd, hld => by
    dsimp only [writeSlots]
    have hv0 : loadVal m i64 (slotAddr sp0 base) = some v := by
      simpa using hld 0 (Nat.zero_lt_succ _)
    rw [storeMem_of_loadVal_i64 m (slotAddr sp0 base) v hv0]
    exact writeSlots_eq_self_of_loadVal sp0 (base + 1) vs m (by simp at hbd; omega)
      (fun j hj => by
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using hld (j + 1) (Nat.succ_lt_succ hj))

private theorem emitPrivFrameInitAux_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A}
    (hwf : b.Wf) {symAddr : Sym → BitVec 64} {nPriv : Nat} {sp0 : BitVec 64}
    {mL0 : Mem 64} {G : Mem 64 → Prop} {Kpost : MachSt A → Prop}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (k : Nat) (hk_le : k ≤ nPriv) (slots : List (BitVec 64)) (s : MachSt A)
    (h64 : nPriv ≤ 64) (hlen : nPriv + 1 ≤ slots.length) (hsp : s.gpr b.sp = sp0)
    (hldAll : ∀ j < nPriv, ∃ v, loadVal mL0 i64 (slotAddr sp0 j) = some v)
    (hdone : ∀ j < k, ∃ v, loadVal mL0 i64 (slotAddr sp0 j) = some v ∧ slots[j]? = some v)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ q, q ≠ b.w0 → s'.gpr q = s.gpr q) →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (∀ j, nPriv ≤ j → slots'[j]? = slots[j]?) →
      (∀ j < nPriv, ∃ v, loadVal mL0 i64 (slotAddr sp0 j) = some v ∧ slots'[j]? = some v) →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mL0 ⋆ G)) s'.mem →
      Kpost s') :
    bodyWp A symAddr (emitPrivFrameInitAux b nPriv k) Kpost Ψ H s := by
  unfold emitPrivFrameInitAux
  split
  · rename_i hk_lt
    obtain ⟨v, hv⟩ := hldAll k hk_lt
    have hw_not := wordRegs_not_sp_ra hwf
    have hw0_sp : b.w0 ≠ A.abi.sp := (work_not_sp hwf).2.1
    have hsp_w0 : b.sp ≠ b.w0 := (hw_not.2 b.sp (by simp [WordRegBind.wordRegs])).2.1
    let off := BitVec.ofNat 64 (8 * (k + 1))
    let s1 := (s.setGprW .w64 b.w0 (CoreAlu.eval .sub .w64 ((s.gpr b.sp).setWidth 64)
        (Src.evalW .w64 s.gpr (.imm off)))).setFlags
        (A.aluFlags .sub .w64 false ((s.gpr b.sp).setWidth 64)
          (Src.evalW .w64 s.gpr (.imm off)) s.flags)
    have hs1_w0 : s1.gpr b.w0 = slotAddr sp0 k := by
      simp [s1, hawf.writeSub_w64, CoreAlu.eval, Src.evalW, Src.eval, BitVec.setWidth_eq,
        hsp, slotAddr, off]
    have hs1_sp : s1.gpr A.abi.sp = s.gpr A.abi.sp := by
      simp [s1, MachSt.gpr_setGprW_ne _ _ _ hw0_sp.symm]
    have hm1 : (array64 (s1.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s1.mem := by
      simpa only [s1, hs1_sp, MachSt.mem_setFlags, MachSt.mem_setGprW] using hm
    have hld_s1 : loadVal s1.mem Width.w64.toTy (AddrArg.baseDisp b.w0 0 |>.eval s1.gpr) =
        some v := by
      have hm1_eq : (Eq mL0 ⋆ (array64 (s1.gpr A.abi.sp) slots ⋆ G)) s1.mem :=
        sep_cast hm1 (by ac_rfl)
      have haddr : (AddrArg.baseDisp b.w0 0 |>.eval s1.gpr) = slotAddr sp0 k := by
        simp [AddrArg.eval, hs1_w0]
      rw [haddr]; exact loadVal_frame hm1_eq hv
    let s2 := s1.setGpr b.w0 (LoadExt.zx.apply A .w64 (s1.gpr b.w0) v)
    have hs2_sp : s2.gpr A.abi.sp = s.gpr A.abi.sp :=
      (MachSt.gpr_setGpr_ne _ _ hw0_sp.symm).trans hs1_sp
    have hs2_w0 : s2.gpr b.w0 = v := by simp [s2, LoadExt.apply, BitVec.setWidth_eq]
    have hm2 : (array64 (s2.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s2.mem := by
      simpa only [s2, hs2_sp, hs1_sp, MachSt.mem_setGpr] using hm1
    have hklt : k < slots.length := by omega
    have hst := store_array64 (s2.gpr b.w0) hklt hm2
    refine instrWp_alu (instrWp_load (v := v) hld_s1 (instrWp_slotSt hst.1 ?_))
    have hne2 : ∀ q, q ≠ b.w0 → s2.gpr q = s.gpr q := fun q hq => by
      simp [s2, s1, MachSt.gpr_setGpr_ne _ _ hq, MachSt.gpr_setGprW_ne _ _ _ hq]
    refine emitPrivFrameInitAux_bodyWp hawf hwf (k + 1) (by omega) (slots.set k (s2.gpr b.w0)) _
      h64 (by simpa [List.length_set] using hlen) ((hne2 b.sp hsp_w0).trans hsp) hldAll ?_
      (by simpa only [MachSt.mem_setMem, MachSt.gpr_setMem] using hst.2) ?_
    · intro j hj
      by_cases hjk : j = k
      · subst hjk; exact ⟨v, hv, by rw [List.getElem?_set_self (by omega), hs2_w0]⟩
      · obtain ⟨vj, hvj, hgetj⟩ := hdone j (by omega)
        exact ⟨vj, hvj, by rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hgetj⟩
    · intro s' slots' hlen' hq' hsp' hj_ge hdone' hm'
      refine hk s' slots' (by simpa [List.length_set] using hlen')
        (fun q hq => (hq' q hq).trans (hne2 q hq)) (hsp'.trans hs2_sp) (fun j hj => ?_) hdone' hm'
      rw [hj_ge j hj, List.getElem?_set_ne (by omega)]
  · dsimp only [bodyWp]
    refine hk s slots rfl (fun _ _ => rfl) rfl (fun _ _ => rfl) ?_ hm
    intro j hj; exact hdone j (by omega)
termination_by nPriv - k

theorem emitPrivFrameInit_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {nPriv : Nat} {sp0 : BitVec 64} {rw : Regs}
    {slots : List (BitVec 64)} {mL0 : Mem 64} {G : Mem 64 → Prop} {s : MachSt A}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (hsp : rw.sp = sp0) (hr : WordRegsRel b rw s)
    (hpriv : nPriv > 0 → nPriv ≤ 64 ∧ ∀ k < nPriv, storeOk mL0 i64 (slotAddr sp0 k))
    (hlen : nPriv > 0 → nPriv + 1 ≤ slots.length)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mL0 ⋆ G)) s.mem)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length →
      PrivSlotsRel nPriv sp0 slots' mL0 mL0 →
      WordRegsRel b rw s' → s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (∀ q, q ≠ b.w0 → s'.gpr q = s.gpr q) →
      (∀ j, nPriv + 1 ≤ j → slots'[j]? = slots[j]?) →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mL0 ⋆ G)) s'.mem →
      Kpost s') :
    bodyWp A symAddr (emitPrivFrameInit b nPriv) Kpost Ψ H s := by
  by_cases hn : nPriv = 0
  · subst hn; simp only [emitPrivFrameInit, beq_self_eq_true, ↓reduceIte, bodyWp]
    exact hk s slots rfl (by simp [PrivSlotsRel]) hr rfl (fun _ _ => rfl) (fun _ _ => rfl) hm
  · have hpos : nPriv > 0 := Nat.pos_of_ne_zero hn
    obtain ⟨h64, hok⟩ := hpriv hpos
    have hlen1 : nPriv + 1 ≤ slots.length := hlen hpos
    have hnb : (nPriv == 0) = false := beq_false_of_ne hn
    simp only [emitPrivFrameInit, hnb, Bool.false_eq_true, ↓reduceIte]
    have hstN := store_array64 (s.gpr b.sp) (i := nPriv) (by omega) hm
    refine instrWp_slotSt hstN.1 ?_
    have hsp_eq : s.gpr b.sp = sp0 := hr.1.trans hsp
    have hldAll : ∀ j < nPriv, ∃ v, loadVal mL0 i64 (slotAddr sp0 j) = some v := fun j hj =>
      loadVal_i64_of_storeOk (hok j hj)
    refine emitPrivFrameInitAux_bodyWp hawf hwf 0 (Nat.zero_le _) (slots.set nPriv (s.gpr b.sp))
      _ h64 (by simpa [List.length_set] using hlen1) hsp_eq hldAll
      (fun _ hj => absurd hj (Nat.not_lt_zero _)) (by simpa [MachSt.mem_setMem] using hstN.2) ?_
    intro s' slots' hlen' hq' hsp' hj_ge hdone' hm'
    have hlen'' : slots'.length = slots.length := by simpa [List.length_set] using hlen'
    have hsl_n : slots'[nPriv]? = some sp0 := by
      rw [hj_ge nPriv (Nat.le_refl _), List.getElem?_set_self (by omega), hsp_eq]
    have hfr : FrameRel nPriv sp0 (slots'.take nPriv) mL0 mL0 := by
      dsimp only [FrameRel]; rw [ite_eq_right hn]
      refine ⟨by rw [List.length_take]; omega, h64, hok, ?_⟩
      symm
      refine writeSlots_eq_self_of_loadVal sp0 0 (slots'.take nPriv) mL0
        (by rw [List.length_take]; omega) fun j hj => ?_
      rw [List.length_take] at hj
      have hj' : j < nPriv := by omega
      obtain ⟨vj, hvj, hgetj⟩ := hdone' j hj'
      have helem : (slots'.take nPriv)[j] = vj := by
        rw [← Option.some_inj, ← List.getElem?_eq_getElem, List.getElem?_take_of_lt hj', hgetj]
      simpa [helem] using hvj
    refine hk s' slots' hlen'' ?_ ?_ hsp' hq' (fun j hj => ?_) hm'
    · dsimp only [PrivSlotsRel]; rw [ite_eq_right hn]; exact ⟨by omega, h64, hsl_n, hfr⟩
    · exact wordRegsRel_updWork hwf hr b.w0 (w_mem_workRegs b).1 hq'
    · rw [hj_ge j (by omega), List.getElem?_set_ne (by omega)]

private theorem slotAddr_sub8 (sp0 : BitVec 64) (k : Nat) :
    (sp0 - BitVec.ofNat 64 (8 * k)) - 8#64 = slotAddr sp0 k := by
  dsimp only [slotAddr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

private theorem emitPrivFlushAux_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {nPriv : Nat} {sp0 : BitVec 64} {G : Mem 64 → Prop}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (k : Nat) (hk_le : k ≤ nPriv) (slots : List (BitVec 64)) (mCur : Mem 64) (s : MachSt A)
    (h64 : nPriv ≤ 64) (hlen : nPriv ≤ slots.length)
    (hw1 : s.gpr b.w1 = sp0 - BitVec.ofNat 64 (8 * k))
    (hok : ∀ j, k ≤ j → j < nPriv → storeOk mCur i64 (slotAddr sp0 j))
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mCur ⋆ G)) s.mem)
    (hk : ∀ s',
      (∀ q, q ≠ b.w1 → q ≠ b.w2 → s'.gpr q = s.gpr q) →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots ⋆
        (Eq (writeSlots mCur sp0 k ((slots.take nPriv).drop k)) ⋆ G)) s'.mem →
      Kpost s') :
    bodyWp A symAddr (emitPrivFlushAux b nPriv k) Kpost Ψ H s := by
  unfold emitPrivFlushAux
  split
  · rename_i hk_lt
    have hk_s : k < slots.length := Nat.lt_of_lt_of_le hk_lt hlen
    have hldk := loadVal_array64 hk_s hm
    have hne := wordRegBind_work_ne hwf; have hwsp := work_not_sp hwf
    let s1 := s.setGpr b.w2 slots[k]
    let s2 := (s1.setGprW .w64 b.w1 (CoreAlu.eval .sub .w64 ((s1.gpr b.w1).setWidth 64)
        (Src.evalW .w64 s1.gpr (.imm 8#64)))).setFlags
        (A.aluFlags .sub .w64 false ((s1.gpr b.w1).setWidth 64)
          (Src.evalW .w64 s1.gpr (.imm 8#64)) s1.flags)
    have hs2_w2 : s2.gpr b.w2 = slots[k] := by
      simp [s2, s1, MachSt.gpr_setGprW_ne _ _ _ hne.2.2.2.2.2.symm]
    have hs2_w1 : s2.gpr b.w1 = slotAddr sp0 k := by
      have hw1' : s1.gpr b.w1 = sp0 - BitVec.ofNat 64 (8 * k) := by
        simpa [s1, MachSt.gpr_setGpr_ne _ _ hne.2.2.2.2.2] using hw1
      simp [s2, hawf.writeSub_w64, CoreAlu.eval, Src.evalW, Src.eval, BitVec.setWidth_eq,
        hw1', slotAddr_sub8]
    have hs2_sp : s2.gpr A.abi.sp = s.gpr A.abi.sp := by
      simp [s2, s1, MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.1.symm,
        MachSt.gpr_setGpr_ne _ _ hwsp.2.2.2.symm]
    have hm2 : (array64 (s2.gpr A.abi.sp) slots ⋆ (Eq mCur ⋆ G)) s2.mem := by
      simpa only [s2, s1, hs2_sp, MachSt.mem_setFlags, MachSt.mem_setGprW, MachSt.mem_setGpr]
        using hm
    have hm2_eq : (Eq mCur ⋆ (array64 (s2.gpr A.abi.sp) slots ⋆ G)) s2.mem :=
      sep_cast hm2 (by ac_rfl)
    have hev : (AddrArg.baseDisp b.w1 0 |>.eval s2.gpr) = slotAddr sp0 k := by
      simp [AddrArg.eval, hs2_w1]
    have hst_m := hok k (Nat.le_refl k) hk_lt
    have hst_s2 : storeOk s2.mem Width.w64.toTy (AddrArg.baseDisp b.w1 0 |>.eval s2.gpr) := by
      rw [hev]; exact storeOk_frame hm2_eq hst_m
    let m' := storeMem mCur i64 (slotAddr sp0 k) slots[k]
    have hm3 : (array64 (s2.gpr A.abi.sp) slots ⋆ (Eq m' ⋆ G))
        (storeMem s2.mem Width.w64.toTy (AddrArg.baseDisp b.w1 0 |>.eval s2.gpr)
          ((s2.gpr b.w2).setWidth Width.w64.bits)) := by
      have hf := storeMem_frame hm2_eq hst_m slots[k]
      rw [hev]; simp only [Width.bits, BitVec.setWidth_eq, hs2_w2]
      exact sep_cast hf (by ac_rfl)
    refine instrWp_slotLd hldk (instrWp_alu (instrWp_store hst_s2 ?_))
    have hdrop : (slots.take nPriv).drop k = slots[k] :: ((slots.take nPriv).drop (k + 1)) := by
      rw [List.drop_eq_getElem_cons (by rw [List.length_take]; omega)]
      simp [List.getElem_take]
    have hne2 : ∀ q, q ≠ b.w1 → q ≠ b.w2 → s2.gpr q = s.gpr q := fun q hq1 hq2 => by
      simp [s2, s1, MachSt.gpr_setGprW_ne _ _ _ hq1, MachSt.gpr_setGpr_ne _ _ hq2]
    refine emitPrivFlushAux_bodyWp hawf hwf (k + 1) (by omega) slots m' _ h64 hlen ?_
      (fun j hj1 hj2 => storeOk_storeMem mCur i64 i64 (slotAddr sp0 k) (slotAddr sp0 j)
        slots[k] (hok j (by omega) hj2))
      (by simpa only [MachSt.mem_setMem, MachSt.gpr_setMem] using hm3) ?_
    · rw [MachSt.gpr_setMem, hs2_w1]; rfl
    · intro s' hq' hsp' hm'
      refine hk s' (fun q hq1 hq2 => (hq' q hq1 hq2).trans (hne2 q hq1 hq2)) (hsp'.trans hs2_sp)
        ?_
      simpa [hdrop, writeSlots, m'] using hm'
  · dsimp only [bodyWp]
    have hdrop : (slots.take nPriv).drop k = [] := by
      rw [List.drop_eq_nil_iff, List.length_take]; omega
    refine hk s (fun _ _ _ => rfl) rfl ?_
    rw [hdrop]; simpa [writeSlots] using hm
termination_by nPriv - k

theorem emitPrivFlush_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {nPriv : Nat} {sp0 : BitVec 64} {rw : Regs}
    {slots : List (BitVec 64)} {mConc mPub : Mem 64} {G : Mem 64 → Prop} {s : MachSt A}
    {sb d : Nat} {bvs : List ((u : Ty) × Val u)}
    {Kpost : MachSt A → Prop} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    (hsb : nPriv > 0 → nPriv + 1 ≤ sb)
    (hslots : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots.length)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hpriv : PrivSlotsRel nPriv sp0 slots mConc mPub)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem)
    (hk : ∀ s',
      s'.gpr b.w0 = s.gpr b.w0 →
      WordRegsRel b rw s' → EnvRel b sb d bvs s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots ⋆ (Eq mConc ⋆ G)) s'.mem →
      Kpost s') :
    bodyWp A symAddr (emitPrivFlush b nPriv) Kpost Ψ H s := by
  by_cases hn : nPriv = 0
  · subst hn; simp only [emitPrivFlush, beq_self_eq_true, ↓reduceIte, bodyWp]
    refine hk s rfl hr he rfl ?_
    rw [privSlotsRel_zero hpriv]; exact hm
  · have hnb : (nPriv == 0) = false := beq_false_of_ne hn
    simp only [emitPrivFlush, hnb, Bool.false_eq_true, ↓reduceIte]
    have hp := privSlotsRel_nonZero_fields (Nat.pos_of_ne_zero hn) hpriv
    rcases hp with ⟨hlen, h64, hsp0, hfr⟩
    dsimp only [FrameRel] at hfr; rw [ite_eq_right hn] at hfr
    rcases hfr with ⟨_, _, hok, rfl⟩
    have hsp0' : slots[nPriv] = sp0 := by
      rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega)]; exact hsp0
    have hldN := @loadVal_array64 (s.gpr A.abi.sp) slots nPriv (Eq mPub ⋆ G) s.mem (by omega) hm
    rw [hsp0'] at hldN
    have hwk := w_mem_workRegs b; have hne := wordRegBind_work_ne hwf; have hwsp := work_not_sp hwf
    refine instrWp_slotLd hldN ?_
    have hsp1 : (s.setGpr b.w1 sp0).gpr A.abi.sp = s.gpr A.abi.sp :=
      MachSt.gpr_setGpr_ne _ _ hwsp.2.2.1.symm
    refine emitPrivFlushAux_bodyWp hawf hwf 0 (Nat.zero_le _) slots mPub _ h64 (by omega)
      (by simp [MachSt.gpr_setGpr_same]) (fun j _ hj => hok j hj)
      (by simpa [hsp1] using hm) ?_
    intro s' hq' hsp' hm'
    have hq_all : ∀ q, q ≠ b.w1 → q ≠ b.w2 → s'.gpr q = s.gpr q := fun q h1 h2 => by
      simpa [MachSt.gpr_setGpr_ne _ _ h1] using hq' q h1 h2
    have hm'_eq : (array64 (s'.gpr A.abi.sp) slots ⋆
        (Eq (writeSlots mPub sp0 0 (slots.take nPriv)) ⋆ G)) s'.mem := by
      simpa using hm'
    refine hk s' (hq_all b.w0 hne.2.2.2.1 hne.2.2.2.2.1) ?_ ?_ (hsp'.trans hsp1) hm'_eq
    · have hr1 := wordRegsRel_updWork hwf hr b.w1 hwk.2.1 (s' := s.setGpr b.w1 sp0)
        (fun q hq => MachSt.gpr_setGpr_ne _ _ hq)
      have hnot := wordRegs_not_sp_ra hwf
      have hne1 : ∀ q ∈ b.wordRegs, q ≠ b.w1 ∧ q ≠ b.w2 := fun q hq =>
        ⟨(hnot.2 q hq).2.2.1, (hnot.2 q hq).2.2.2⟩
      exact ⟨(hq' b.sp (hne1 _ (by simp [WordRegBind.wordRegs])).1
        (hne1 _ (by simp [WordRegBind.wordRegs])).2).trans hr1.1,
        (hq' b.rp (hne1 _ (by simp [WordRegBind.wordRegs])).1
        (hne1 _ (by simp [WordRegBind.wordRegs])).2).trans hr1.2.1,
        (hq' b.rv (hne1 _ (by simp [WordRegBind.wordRegs])).1
        (hne1 _ (by simp [WordRegBind.wordRegs])).2).trans hr1.2.2.1,
        (hq' b.r1 (hne1 _ (by simp [WordRegBind.wordRegs])).1
        (hne1 _ (by simp [WordRegBind.wordRegs])).2).trans hr1.2.2.2.1,
        (hq' b.r2 (hne1 _ (by simp [WordRegBind.wordRegs])).1
        (hne1 _ (by simp [WordRegBind.wordRegs])).2).trans hr1.2.2.2.2.1,
        (hq' b.r3 (hne1 _ (by simp [WordRegBind.wordRegs])).1
        (hne1 _ (by simp [WordRegBind.wordRegs])).2).trans hr1.2.2.2.2.2⟩
    · refine envRel_map_loc (fun i hi item _ h => ?_) he
      cases hl : locOf b sb (d - 1 - i) with
      | gpr r =>
        have hne_r := locOf_gpr_ne_work hwf sb _ hl
        simpa [LocHolds, hl, hq_all r hne_r.2.2.1 hne_r.2.2.2] using h
      | slot k =>
        simp only [LocHolds, hl] at h ⊢
        obtain ⟨g, hld0, hval0⟩ := h
        have hlt := hslots (d - 1 - i) (by omega) k hl
        have h1 := loadVal_array64 hlt hm
        have h2 := loadVal_array64 hlt hm'
        rw [h1] at hld0; cases hld0
        exact ⟨slots[k], by simpa [hsp'.trans hsp1] using h2, hval0⟩

theorem emitDynAliasGuard_bodyWp {A : Arch} (hawf : A.Wf) {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d nPriv bytes : Nat} {a : Arg K i64}
    {bvs : List ((u : Ty) × Val u)} {aa : Arg Val i64} {rw : Regs} {sp0 : BitVec 64}
    {slots : List (BitVec 64)} {G : Mem 64 → Prop} {s : MachSt A} {cg : List (Instr A)}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hn0 : 0 < nPriv) (h64 : nPriv ≤ 64) (hbytes : bytes ≤ 16)
    (hlen : nPriv + 1 ≤ slots.length) (hsp0 : slots[nPriv]? = some sp0)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ G) s.mem)
    (ha : denoteArg bvs a = some aa)
    (hlo : emitDynAliasGuard b sb d nPriv bytes a = .ok cg)
    (hk : ∀ (ok : Bool) s',
      ValHolds64 .bool ok (s'.gpr b.w0) →
      (ok = true → ∀ k i j, k < nPriv → i < 8 → j < bytes →
        aa.val + BitVec.ofNat 64 j ≠ slotAddr sp0 k + BitVec.ofNat 64 i) →
      EnvRel b sb d bvs s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp → s'.mem = s.mem → Kpost s') :
    bodyWp A symAddr cg Kpost Ψ H s := by
  dsimp only [emitDynAliasGuard] at hlo
  cases hge : b.condOfCmp? .uge <;> rw [hge] at hlo; · cases hlo
  cases hle : b.condOfCmp? .ule <;> rw [hle] at hlo; · cases hlo
  rename_i ccUge ccUle
  dsimp only [Except.bind] at hlo
  cases hca : loadArgInto b sb d b.w0 a <;> rw [hca] at hlo; · cases hlo
  cases hlo; rename_i ca
  have hwk := w_mem_workRegs b; have hne := wordRegBind_work_ne hwf; have hwsp := work_not_sp hwf
  refine bodyWp_append ca _ _ (loadArgInto_bodyWp hawf hwf hwk.1 he ha hm hca ?_)
  intro s1 hs1_ne hva hm1 he1
  have hsp1 : s1.gpr A.abi.sp = s.gpr A.abi.sp := hs1_ne A.abi.sp hwsp.2.1.symm
  have hr1 := wordRegsRel_updWork hwf hr b.w0 hwk.1 hs1_ne
  have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ G) s1.mem := by simpa [hsp1, hm1] using hm
  have hsp0' : slots[nPriv] = sp0 := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem (by omega)]; exact hsp0
  have hldN : loadVal s1.mem i64 (s1.gpr A.abi.sp + BitVec.ofNat 64 (8 * nPriv)) = some sp0 := by
    simpa [hsp0'] using loadVal_array64 (i := nPriv) (by omega) hm1'
  refine instrWp_slotLd hldN (instrWp_alu (instrWp_alu (instrWp_cmp (instrWp_setcc
    (instrWp_cmp (instrWp_setcc (instrWp_alu ?_)))))))
  let frameBytes := BitVec.ofNat 64 (8 * nPriv)
  let hiBound := BitVec.ofNat 64 (2 ^ 64 - bytes)
  let dist := aa.val - (sp0 - frameBytes)
  let c1 := BitVec.ule frameBytes dist
  let c2 := BitVec.ule dist hiBound
  have ha1 : s1.gpr b.w0 = aa.val := by
    dsimp only [ValHolds64] at hva; simpa [BitVec.setWidth_eq] using hva.2
  let s2 := s1.setGpr b.w1 sp0
  let s3 := (s2.setGprW .w64 b.w1 (CoreAlu.eval .sub .w64 ((s2.gpr b.w1).setWidth 64)
      (Src.evalW .w64 s2.gpr (.imm frameBytes)))).setFlags
      (A.aluFlags .sub .w64 false ((s2.gpr b.w1).setWidth 64)
        (Src.evalW .w64 s2.gpr (.imm frameBytes)) s2.flags)
  let s4 := (s3.setGprW .w64 b.w0 (CoreAlu.eval .sub .w64 ((s3.gpr b.w0).setWidth 64)
      (Src.evalW .w64 s3.gpr (.reg b.w1)))).setFlags
      (A.aluFlags .sub .w64 false ((s3.gpr b.w0).setWidth 64)
        (Src.evalW .w64 s3.gpr (.reg b.w1)) s3.flags)
  have hs3_w1 : s3.gpr b.w1 = sp0 - frameBytes := by
    simp [s3, s2, hawf.writeSub_w64, CoreAlu.eval, Src.evalW, Src.eval, BitVec.setWidth_eq]
  have hs4_w0 : s4.gpr b.w0 = dist := by
    have h20 : s3.gpr b.w0 = aa.val := by
      simp [s3, s2, MachSt.gpr_setGprW_ne _ _ _ hne.2.2.2.1,
        MachSt.gpr_setGpr_ne _ _ hne.2.2.2.1, ha1]
    simp [s4, hawf.writeSub_w64, CoreAlu.eval, Src.evalW, Src.eval, BitVec.setWidth_eq,
      h20, hs3_w1, dist]
  let f5 := A.cmpFlags .w64 ((s4.gpr b.w0).setWidth 64) (Src.evalW .w64 s4.gpr (.imm frameBytes))
      s4.flags
  let s5 := s4.setFlags f5
  have hc1_eval : A.evalCond f5 ccUge = c1 := by
    have hsnd := hwf.cond_sound .uge ccUge .w64 ((s4.gpr b.w0).setWidth 64)
      (Src.evalW .w64 s4.gpr (.imm frameBytes)) s4.flags hge
    simpa [f5, CmpOp.evalBits, Src.evalW, Src.eval, BitVec.setWidth_eq, hs4_w0, c1] using hsnd
  let s6 := s5.setGprW .w8 b.w1 (BitVec.ofNat 8 (A.evalCond s5.flags ccUge).toNat)
  let f7 := A.cmpFlags .w64 ((s6.gpr b.w0).setWidth 64) (Src.evalW .w64 s6.gpr (.imm hiBound))
      s6.flags
  let s7 := s6.setFlags f7
  have hc2_eval : A.evalCond f7 ccUle = c2 := by
    have hs6_w0 : s6.gpr b.w0 = dist := by
      simp [s6, s5, MachSt.gpr_setGprW_ne _ _ _ hne.2.2.2.1, hs4_w0]
    have hsnd := hwf.cond_sound .ule ccUle .w64 ((s6.gpr b.w0).setWidth 64)
      (Src.evalW .w64 s6.gpr (.imm hiBound)) s6.flags hle
    simpa [f7, CmpOp.evalBits, Src.evalW, Src.eval, BitVec.setWidth_eq, hs6_w0, c2] using hsnd
  let s8 := s7.setGprW .w8 b.w2 (BitVec.ofNat 8 (A.evalCond s7.flags ccUle).toNat)
  let s9 := (s8.setGprW .w8 b.w0 (CoreAlu.eval .and .w8 ((s8.gpr b.w1).setWidth 8)
      (Src.evalW .w8 s8.gpr (.reg b.w2)))).setFlags
      (A.aluFlags .and .w8 false ((s8.gpr b.w1).setWidth 8)
        (Src.evalW .w8 s8.gpr (.reg b.w2)) s8.flags)
  have hval9 : ValHolds64 .bool (c1 && c2) (s9.gpr b.w0) := by
    have hs8_w1 : (s8.gpr b.w1).setWidth 8 = BitVec.ofNat 8 c1.toNat := by
      simp [s8, s7, s6, s5, MachSt.gpr_setGprW_ne _ _ _ hne.2.2.2.2.2,
        MachSt.gpr_setGprW_same, hawf.writeSub_setWidth .w8, hc1_eval]
    have hs8_w2 : (s8.gpr b.w2).setWidth 8 = BitVec.ofNat 8 c2.toNat := by
      simp [s8, s7, MachSt.gpr_setGprW_same, hawf.writeSub_setWidth .w8, hc2_eval]
    dsimp only [ValHolds64, Width.bits]
    simp only [s9, MachSt.gpr_setFlags, MachSt.gpr_setGprW_same, hawf.writeSub_setWidth .w8,
      CoreAlu.eval, Src.evalW, Src.eval, Width.bits, hs8_w1, hs8_w2]
    cases c1 <;> cases c2 <;> decide
  have hdisj : c1 && c2 = true → ∀ k i j, k < nPriv → i < 8 → j < bytes →
      aa.val + BitVec.ofNat 64 j ≠ slotAddr sp0 k + BitVec.ofNat 64 i := by
    intro hok k i j hk' hi hj
    obtain ⟨hc1, hc2⟩ := Bool.and_eq_true_iff.mp hok
    by_cases hb0 : bytes = 0
    · subst hb0; omega
    · have hlo' : 8 * nPriv ≤ dist.toNat := by
        have hbv : frameBytes.toNat ≤ dist.toNat := by
          dsimp only [c1, BitVec.ule] at hc1; exact BitVec.le_def.mp (of_decide_eq_true hc1)
        simpa [frameBytes, Nat.mod_eq_of_lt (by omega : 8 * nPriv < 2 ^ 64)] using hbv
      have hhi' : dist.toNat ≤ 2 ^ 64 - bytes := by
        have hbv : dist.toNat ≤ hiBound.toNat := by
          dsimp only [c2, BitVec.ule] at hc2; exact BitVec.le_def.mp (of_decide_eq_true hc2)
        simpa [hiBound, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - bytes < 2 ^ 64)] using hbv
      exact disjoint_frame_of_range sp0 aa.val h64 hbytes hlo' hhi' hk' hj hi
  dsimp only [bodyWp]
  refine hk (c1 && c2) s9 hval9 hdisj ?_ ?_ ?_ (by simpa [s9, s8, s7, s6, s5, s4, s3, s2] using hm1)
  · simp only [s9, s8, s7, s6, s5, s4, s3, s2, envRel_setFlags,
      envRel_setGprW_work hwf sb d bvs _ .w8 hwk.1 _,
      envRel_setGprW_work hwf sb d bvs _ .w8 hwk.2.2 _,
      envRel_setGprW_work hwf sb d bvs _ .w8 hwk.2.1 _,
      envRel_setGprW_work hwf sb d bvs _ .w64 hwk.1 _,
      envRel_setGprW_work hwf sb d bvs _ .w64 hwk.2.1 _,
      envRel_setGpr_work hwf sb d bvs _ hwk.2.1 _]; exact he1
  · simp only [s9, s8, s7, s6, s5, s4, s3, s2, wordRegsRel_setFlags,
      wordRegsRel_setGprW_work hwf rw _ .w8 (Or.inl hwk.1) _,
      wordRegsRel_setGprW_work hwf rw _ .w8 (Or.inl hwk.2.2) _,
      wordRegsRel_setGprW_work hwf rw _ .w8 (Or.inl hwk.2.1) _,
      wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.1) _,
      wordRegsRel_setGprW_work hwf rw _ .w64 (Or.inl hwk.2.1) _,
      wordRegsRel_setGpr_work hwf rw _ (Or.inl hwk.2.1) _]; exact hr1
  · simp only [s9, s8, s7, s6, s5, s4, s3, s2, MachSt.gpr_setFlags,
      MachSt.gpr_setGprW_ne _ _ _ hwsp.2.1.symm, MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.2.symm,
      MachSt.gpr_setGprW_ne _ _ _ hwsp.2.2.1.symm, MachSt.gpr_setGpr_ne _ _ hwsp.2.2.1.symm,
      hsp1]

private theorem privLoad_slot_eq {nPriv slotIdx : Nat} {sp0 : BitVec 64}
    {slots : List (BitVec 64)} {mConc mPub : Mem 64} {v : BitVec 64}
    (hpos : 0 < nPriv) (hslot : slotIdx < nPriv)
    (hpriv : PrivSlotsRel nPriv sp0 slots mConc mPub)
    (hld : loadVal mConc i64 (slotAddr sp0 slotIdx) = some v) :
    slots[slotIdx]? = some v := by
  obtain ⟨_, _, _, hfr⟩ := privSlotsRel_nonZero_fields hpos hpriv
  dsimp only [FrameRel] at hfr; rw [ite_eq_right (Nat.ne_of_gt hpos)] at hfr
  rcases hfr with ⟨hlenT, _, _, rfl⟩
  obtain ⟨w, hwGet, hldW⟩ := loadVal_writeSlots_slot sp0 0 (slots.take nPriv) mPub slotIdx
    (Nat.zero_le _) (by rw [hlenT]; omega) (by omega)
  rw [hldW] at hld; cases hld
  rwa [← List.getElem?_take_of_lt hslot]

theorem privSlotsRel_take_eq {nPriv sb : Nat} {sp0 : BitVec 64}
    {slots slots' : List (BitVec 64)} {mConc mPub : Mem 64}
    (hsb : nPriv > 0 → nPriv + 1 ≤ sb) (hlen : slots'.length = slots.length)
    (heq : ∀ j < sb, slots'[j]? = slots[j]?)
    (hpriv : PrivSlotsRel nPriv sp0 slots mConc mPub) :
    PrivSlotsRel nPriv sp0 slots' mConc mPub := by
  by_cases hn : nPriv = 0
  · subst hn; simpa [PrivSlotsRel] using hpriv
  · have hpos := Nat.pos_of_ne_zero hn
    have hsb_ge := hsb hpos
    dsimp only [PrivSlotsRel] at hpriv ⊢; rw [ite_eq_right hn] at hpriv ⊢
    rcases hpriv with ⟨hl0, h64, hsp0, hfr⟩
    have htake : slots'.take nPriv = slots.take nPriv := List.ext_getElem
      (by rw [List.length_take, List.length_take, hlen])
      (fun j hj1 _ => by
        have hj' : j < nPriv := by rw [List.length_take] at hj1; omega
        rw [← Option.some_inj, ← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem,
          List.getElem?_take_of_lt hj', List.getElem?_take_of_lt hj']
        exact heq j (by omega))
    exact ⟨by omega, h64, by rw [heq nPriv (by omega), hsp0], by rw [htake]; exact hfr⟩

theorem lowerMemLoad_priv_direct_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax nPriv : Nat} {sp0 : BitVec 64}
    {t : Ty} {a : Arg K i64} {bvs : List ((u : Ty) × Val u)} {aa : Arg Val i64}
    {rw : Regs} {slots : List (BitVec 64)} {mConc mPub : Mem 64} {G : Mem 64 → Prop}
    {s : MachSt A} {is : List (Instr A)} {v : Val t}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hsb_ge : nPriv > 0 → nPriv + 1 ≤ sb)
    (hd : d < dMax) (h6 : 6 ≤ d) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (hdisj : nPriv = 0 ∨ ∀ k i j, k < nPriv → i < 8 → j < t.bytes →
      aa.val + BitVec.ofNat 64 j ≠ slotAddr sp0 k + BitVec.ofNat 64 i)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hpriv : PrivSlotsRel nPriv sp0 slots mConc mPub)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem)
    (ha : denoteArg bvs a = some aa) (hld : loadVal mConc t aa.val = some v)
    (hlo : lowerMemLoad b sb d t a = .ok is)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      PrivSlotsRel nPriv sp0 slots' mConc mPub →
      EnvRel b sb (d + 1) (⟨t, v⟩ :: bvs) s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mPub ⋆ G)) s'.mem → Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  have hldPub : loadVal mPub t aa.val = some v := by
    by_cases hn : nPriv = 0
    · subst hn; rw [← privSlotsRel_zero hpriv]; exact hld
    · rcases hdisj with rfl | hd_pos
      · exact absurd rfl hn
      · obtain ⟨_, _, _, hfr⟩ := privSlotsRel_nonZero_fields (Nat.pos_of_ne_zero hn) hpriv
        dsimp only [FrameRel] at hfr; rw [ite_eq_right hn] at hfr
        rcases hfr with ⟨hlenT, _, _, rfl⟩
        have hdis := loadVal_writeSlots_disjoint mPub sp0 t aa.val 0 (slots.take nPriv)
          (fun k i j _ hk2 hi hj => hd_pos k i j (by omega) hi hj)
        exact hdis.symm.trans hld
  refine lowerMemLoad_bodyWp hwf hd h6 hbound he hr hm ha hldPub hlo ?_
  intro s' slots' hlen' hsb' he' hr' hsp' hm'
  exact hk s' slots' hlen' hsb'
    (privSlotsRel_take_eq hsb_ge hlen' hsb' hpriv) he' hr' hsp' hm'

theorem lowerMemStore_priv_direct_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax nPriv : Nat} {sp0 : BitVec 64}
    {t : Ty} {v : Arg K t} {a : Arg K i64} {bvs : List ((u : Ty) × Val u)}
    {va : Arg Val t} {aa : Arg Val i64} {rw : Regs} {slots : List (BitVec 64)}
    {mConc mPub : Mem 64} {G : Mem 64 → Prop} {s : MachSt A} {is : List (Instr A)}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hd : d ≤ dMax) (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (hdisj : nPriv = 0 ∨ ∀ k i j, k < nPriv → i < 8 → j < t.bytes →
      aa.val + BitVec.ofNat 64 j ≠ slotAddr sp0 k + BitVec.ofNat 64 i)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hpriv : PrivSlotsRel nPriv sp0 slots mConc mPub)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem)
    (hvD : denoteArg bvs v = some va) (haD : denoteArg bvs a = some aa)
    (hst : storeOk mConc t aa.val)
    (hlo : lowerMemStore b sb d v a = .ok is)
    (hk : ∀ s',
      PrivSlotsRel nPriv sp0 slots (storeMem mConc t aa.val va.val)
        (storeMem mPub t aa.val va.val) →
      EnvRel b sb d bvs s' → WordRegsRel b rw s' → s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots ⋆ (Eq (storeMem mPub t aa.val va.val) ⋆ G)) s'.mem →
      Kpost s') :
    bodyWp A symAddr is Kpost Ψ H s := by
  by_cases hn : nPriv = 0
  · subst hn; have hmeq := privSlotsRel_zero hpriv
    have hstP : storeOk mPub t aa.val := by simpa [hmeq] using hst
    refine lowerMemStore_bodyWp hwf hd hbound he hr hm hvD haD hstP hlo ?_
    intro s' he' hr' hsp' hm'
    exact hk s' (by simp [PrivSlotsRel, hmeq]) he' hr' hsp' hm'
  · rcases hdisj with rfl | hd_pos
    · exact absurd rfl hn
    · obtain ⟨hl, h64, hsp0, hfr⟩ := privSlotsRel_nonZero_fields (Nat.pos_of_ne_zero hn) hpriv
      have hstP : storeOk mPub t aa.val := by
        have hfr' := hfr; dsimp only [FrameRel] at hfr'; rw [ite_eq_right hn] at hfr'
        rcases hfr' with ⟨hlenT, _, _, rfl⟩
        exact (storeOk_writeSlots_disjoint mPub sp0 t aa.val 0 (slots.take nPriv)
          (fun k i j _ hk2 hi hj => hd_pos k i j (by omega) hi hj)).mp hst
      have hpriv' : PrivSlotsRel nPriv sp0 slots
          (storeMem mConc t aa.val va.val) (storeMem mPub t aa.val va.val) := by
        dsimp only [PrivSlotsRel]; rw [ite_eq_right hn]
        exact ⟨hl, h64, hsp0, frameRel_store_disjoint hfr t aa.val va.val hd_pos⟩
      refine lowerMemStore_bodyWp hwf hd hbound he hr hm hvD haD hstP hlo ?_
      intro s' he' hr' hsp' hm'
      exact hk s' hpriv' he' hr' hsp' hm'

theorem lowerMemLoad_priv_slot_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax nPriv slotIdx : Nat} {sp0 : BitVec 64}
    {a : Arg K i64} {bvs : List ((u : Ty) × Val u)} {aa : Arg Val i64}
    {rw : Regs} {slots : List (BitVec 64)} {mConc mPub : Mem 64} {G : Mem 64 → Prop}
    {s : MachSt A} {v : Val i64} {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)}
    {Kpost : MachSt A → Prop}
    (hpos : 0 < nPriv) (hsb_ge : nPriv + 1 ≤ sb) (hd : d < dMax) (h6 : 6 ≤ d)
    (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (hlt : slotIdx < nPriv) (haa : aa.val = slotAddr sp0 slotIdx)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hpriv : PrivSlotsRel nPriv sp0 slots mConc mPub)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem)
    (_ha : denoteArg bvs a = some aa) (hld : loadVal mConc i64 aa.val = some v)
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, slots'[j]? = slots[j]?) →
      PrivSlotsRel nPriv sp0 slots' mConc mPub →
      EnvRel b sb (d + 1) (⟨i64, v⟩ :: bvs) s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mPub ⋆ G)) s'.mem → Kpost s') :
    bodyWp A symAddr
      (emitToLoc b.w0 (locOf b sb d) fun rd => [.slotLd rd slotIdx]) Kpost Ψ H s := by
  have hs_v : slots[slotIdx]? = some v := privLoad_slot_eq hpos hlt hpriv (haa ▸ hld)
  have hlen : slotIdx < slots.length := by
    have := privSlotsRel_nonZero_fields hpos hpriv; omega
  have hs_eq : slots[slotIdx] = v := by
    rw [← Option.some_inj, ← List.getElem?_eq_getElem hlen]; exact hs_v
  have hld_arr := @loadVal_array64 (s.gpr A.abi.sp) slots slotIdx (Eq mPub ⋆ G) s.mem hlen hm
  rw [hs_eq] at hld_arr
  have hwk := w_mem_workRegs b; have hwsp := work_not_sp hwf
  have hcore : ∀ rd (hrd : rd = b.w0 ∨ locOf b sb d = .gpr rd),
      bodyWp A symAddr [.slotLd rd slotIdx] (fun s' =>
        ValHolds64 i64 v (s'.gpr rd) ∧ s'.gpr A.abi.sp = s.gpr A.abi.sp ∧
        EnvRel b sb d bvs s' ∧ WordRegsRel b rw s' ∧
        ∃ slots' : List (BitVec 64), slots'.length = slots.length ∧
          (∀ j < sb, slots'[j]? = slots[j]?) ∧
          (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mPub ⋆ G)) s'.mem) Ψ H s := by
    intro rd hrd
    refine instrWp_slotLd hld_arr ?_
    have hsp_rd : A.abi.sp ≠ rd := by
      rcases hrd with rfl | hlrd
      · exact hwsp.2.1.symm
      · exact (locOf_gpr_ne_sp hwf sb d hlrd).symm
    have hspr : (s.setGpr rd v).gpr A.abi.sp = s.gpr A.abi.sp := MachSt.gpr_setGpr_ne _ _ hsp_rd
    refine ⟨⟨by decide, by simp [MachSt.gpr_setGpr_same, BitVec.setWidth_eq]⟩, hspr, ?_, ?_,
      slots, rfl, fun _ _ => rfl, by simpa [hspr] using hm⟩
    · rcases hrd with rfl | hlrd
      · exact (envRel_setGpr_work hwf sb d bvs s hwk.1 _).mpr he
      · exact envRel_setGpr_new hwf hlrd _ he
    · rcases hrd with rfl | hlrd
      · exact wordRegsRel_updWork hwf hr b.w0 hwk.1 (fun q hq => MachSt.gpr_setGpr_ne _ _ hq)
      · exact wordRegsRel_upd_ge6' hwf hr h6 hlrd (fun q hq => MachSt.gpr_setGpr_ne _ _ hq)
  refine emitToLoc_bodyWp hwf hd hbound (fun rd h => hcore rd (Or.inr h))
    (fun _ _ => hcore b.w0 (Or.inl rfl)) ?_
  intro s' slots' hlen' hsb' he' hr' hsp' hm'
  exact hk s' slots' hlen' hsb' (privSlotsRel_take_eq (fun _ => hsb_ge) hlen' hsb' hpriv)
    he' hr' hsp' hm'

theorem lowerMemStore_priv_slot_bodyWp {A : Arch} {b : WordRegBind A} (hwf : b.Wf)
    {symAddr : Sym → BitVec 64} {sb d dMax nPriv slotIdx : Nat} {sp0 : BitVec 64}
    {v : Arg K i64} {a : Arg K i64} {bvs : List ((u : Ty) × Val u)}
    {va aa : Arg Val i64} {rw : Regs} {slots : List (BitVec 64)} {mConc mPub : Mem 64}
    {G : Mem 64 → Prop} {s : MachSt A} {cv : List (Instr A)} {rv : A.Reg}
    {Ψ : Xcap.CodeSpec (MachSt A)} {H : Xcap.Halt (MachSt A)} {Kpost : MachSt A → Prop}
    (hpos : 0 < nPriv) (hsb_ge : nPriv + 1 ≤ sb) (hd : d ≤ dMax)
    (hbound : sb + tempSpillCount b dMax ≤ slots.length)
    (hlt : slotIdx < nPriv) (haa : aa.val = slotAddr sp0 slotIdx)
    (he : EnvRel b sb d bvs s) (hr : WordRegsRel b rw s)
    (hpriv : PrivSlotsRel nPriv sp0 slots mConc mPub)
    (hm : (array64 (s.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s.mem)
    (hvD : denoteArg bvs v = some va) (_haD : denoteArg bvs a = some aa)
    (hload : loadArgToGpr b sb d b.w1 v = .ok (cv, rv))
    (hk : ∀ s' (slots' : List (BitVec 64)),
      slots'.length = slots.length → (∀ j < sb, nPriv ≤ j → slots'[j]? = slots[j]?) →
      PrivSlotsRel nPriv sp0 slots' (storeMem mConc i64 aa.val va.val) mPub →
      EnvRel b sb d bvs s' → WordRegsRel b rw s' →
      s'.gpr A.abi.sp = s.gpr A.abi.sp →
      (array64 (s'.gpr A.abi.sp) slots' ⋆ (Eq mPub ⋆ G)) s'.mem → Kpost s') :
    bodyWp A symAddr (cv ++ [.slotSt slotIdx rv]) Kpost Ψ H s := by
  obtain ⟨hlen, h64, hsp0, hfr⟩ := privSlotsRel_nonZero_fields hpos hpriv
  have hwk := w_mem_workRegs b; have hwsp := work_not_sp hwf
  refine bodyWp_append cv _ _ (loadArgToGpr_bodyWp hwf hwk.2.1 he hvD hm hload ?_)
  intro s1 hs1_ne hvv hm1 he1
  have hsp1 : s1.gpr A.abi.sp = s.gpr A.abi.sp := hs1_ne A.abi.sp hwsp.2.2.1.symm
  have hr1 := wordRegsRel_updWork hwf hr b.w1 hwk.2.1 hs1_ne
  have hm1' : (array64 (s1.gpr A.abi.sp) slots ⋆ (Eq mPub ⋆ G)) s1.mem := by
    simpa [hsp1, hm1] using hm
  have hvv' : s1.gpr rv = va.val := by
    dsimp only [ValHolds64] at hvv; simpa [BitVec.setWidth_eq] using hvv.2
  have hst1 := @store_array64 (s1.gpr A.abi.sp) slots slotIdx (s1.gpr rv) (Eq mPub ⋆ G)
    s1.mem (by omega) hm1'
  refine instrWp_slotSt hst1.1 ?_
  have hsl : ∀ lvl < d, ∀ j, locOf b sb lvl = .slot j → j < slots.length :=
    envRel_slots_bound b hd hbound
  have hks : ∀ lvl < d, locOf b sb lvl ≠ .slot slotIdx := fun lvl _ =>
    locOf_slot_ne_lt_sb b (by omega)
  have htake : (slots.set slotIdx (s1.gpr rv)).take nPriv =
      (slots.take nPriv).set slotIdx va.val := by
    rw [List.take_set, hvv']
  have hpriv' : PrivSlotsRel nPriv sp0 (slots.set slotIdx (s1.gpr rv))
      (storeMem mConc i64 aa.val va.val) mPub := by
    dsimp only [PrivSlotsRel]; rw [ite_eq_right (Nat.ne_of_gt hpos)]
    refine ⟨by simp; omega, h64, ?_, ?_⟩
    · rw [List.getElem?_set_ne (by omega)]; exact hsp0
    · rw [htake, haa]; exact frameRel_set_slot (Nat.ne_of_gt hpos) hfr hlt va.val
  refine hk _ (slots.set slotIdx (s1.gpr rv)) (List.length_set)
    (fun j _ hj => List.getElem?_set_ne (by omega)) hpriv'
    (envRel_setSlot_ge (by omega) hks hsl hm1' (s1.gpr rv) he1)
    ((wordRegsRel_setMem _ _ _ _).mpr hr1) hsp1 (by simpa [MachSt.mem_setMem] using hst1.2)

/-! ## §2. `VllCodeMap.Wf`, `SymAddr` Preservation, and Budget Bounds -/

private theorem nodup_of_listNodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ xs : List α, listNodup xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    dsimp only [listNodup] at h
    rw [Bool.and_eq_true] at h
    have hn : xs.contains x = false := by cases hc : xs.contains x <;> simp_all
    have hm_not : x ∉ xs := fun hm => by rw [List.contains_iff_mem.mpr hm] at hn; cases hn
    exact List.nodup_cons.mpr ⟨hm_not, nodup_of_listNodup xs h.2⟩

private theorem nodup_getElem_inj {α : Type} :
    ∀ {xs : List α}, xs.Nodup → ∀ {i j} (hi : i < xs.length) (hj : j < xs.length),
      xs[i] = xs[j] → i = j
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | _ :: xs, hnd, 0, j + 1, _, hj, heq => by
    exfalso; rw [List.nodup_cons] at hnd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    exact hnd.1 (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj))
  | _ :: xs, hnd, i + 1, 0, hi, _, heq => by
    exfalso; rw [List.nodup_cons] at hnd
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
    exact hnd.1 (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi))
  | _ :: xs, hnd, i + 1, j + 1, hi, hj, heq => by
    rw [List.nodup_cons] at hnd
    exact congrArg Nat.succ (nodup_getElem_inj hnd.2
      (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

private theorem nodup_of_labelsUniqueGo :
    ∀ xs : List Sym, VllCodeMap.labelsUnique.go xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hgo => by
    dsimp only [VllCodeMap.labelsUnique.go] at hgo
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hgo
    have hx_not : x ∉ xs := fun hm => by rw [List.contains_iff_mem.mpr hm] at hgo; cases hgo.1
    exact List.nodup_cons.mpr ⟨hx_not, nodup_of_labelsUniqueGo xs hgo.2⟩

private theorem nodup_of_addrsUniqueGo :
    ∀ xs : List (BitVec 64), VllCodeMap.addrsUnique.go xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hgo => by
    dsimp only [VllCodeMap.addrsUnique.go] at hgo
    rw [Bool.and_eq_true, Bool.not_eq_true'] at hgo
    have hx_not : x ∉ xs := fun hm => by rw [List.contains_iff_mem.mpr hm] at hgo; cases hgo.1
    exact List.nodup_cons.mpr ⟨hx_not, nodup_of_addrsUniqueGo xs hgo.2⟩

theorem lookupSymAddr_mem {pairs : List (Sym × BitVec 64)} {s : Sym} {a : BitVec 64}
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

theorem lookupSymAddr_none_of_not_mem {pairs : List (Sym × BitVec 64)} {s : Sym}
    (hnot : s ∉ pairs.map Prod.fst) :
    lookupSymAddr pairs s = none := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨k, v⟩
    have hne : k ≠ s := fun e => hnot (by simp [e])
    have htail : s ∉ ps.map Prod.fst := fun hm => hnot (by simp [hm])
    simp [lookupSymAddr, beq_false_of_ne hne, ih htail]

theorem lookupSymAddr_append (p₁ p₂ : List (Sym × BitVec 64)) (s : Sym) :
    lookupSymAddr (p₁ ++ p₂) s = (lookupSymAddr p₁ s).orElse fun _ => lookupSymAddr p₂ s := by
  induction p₁ with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨k, v⟩
    dsimp only [List.cons_append, lookupSymAddr]
    cases h : k == s <;> simp [ih]

theorem buildVllSymAddr_base {A : Arch} {base : List (Sym × BitVec 64)}
    {blocks : List (Block A)} (hn : (base.map Prod.fst).Nodup) {s : Sym} {a : BitVec 64}
    (hm : (s, a) ∈ base) :
    buildVllSymAddr base blocks s = a := by
  dsimp only [buildVllSymAddr]
  rw [lookupSymAddr_mem hn hm]

theorem buildVllSymAddr_eq_of_lookup {A : Arch} (base : List (Sym × BitVec 64))
    (blocks : List (Block A)) {s : Sym} {a : BitVec 64} (h : lookupSymAddr base s = some a) :
    buildVllSymAddr base blocks s = a := by
  dsimp only [buildVllSymAddr]; rw [h]

theorem codeMap_lookupAddr_of_mem {cm : CodeMap} (hnd : cm.AddrsNodup) {e : CodeEntry}
    (he : e ∈ cm) : cm.lookupAddr e.addr = some e.block := by
  induction cm with
  | nil => cases he
  | cons x xs ih =>
    rw [CodeMap.AddrsNodup, List.map_cons, List.nodup_cons] at hnd
    dsimp only [CodeMap.lookupAddr]
    rcases List.mem_cons.mp he with rfl | hTail
    · simp
    · have hne : x.addr ≠ e.addr := fun eq => hnd.1 (eq ▸ List.mem_map.mpr ⟨e, hTail, rfl⟩)
      simp [beq_false_of_ne hne, ih hnd.2 hTail]

theorem codeMap_addrOf_of_mem {cm : CodeMap} (hnd : cm.NamesNodup) {e : CodeEntry}
    (he : e ∈ cm) : cm.addrOf? e.name = some e.addr := by
  induction cm with
  | nil => cases he
  | cons x xs ih =>
    rw [CodeMap.NamesNodup, List.map_cons, List.nodup_cons] at hnd
    dsimp only [CodeMap.addrOf?]
    rcases List.mem_cons.mp he with rfl | hTail
    · simp
    · have hne : x.name ≠ e.name := fun eq => hnd.1 (eq ▸ List.mem_map.mpr ⟨e, hTail, rfl⟩)
      simp [beq_false_of_ne hne, ih hnd.2 hTail]

theorem finalizeVllCodeMap_wf {A : Arch} {cm₀ cm : VllCodeMap A}
    (h : finalizeVllCodeMap cm₀ = .ok cm) :
    cm = cm₀ ∧ cm.Wf ∧ cm.labelsUnique = true ∧ cm.addrsUnique = true ∧ cm.padsOk = true := by
  dsimp only [finalizeVllCodeMap] at h
  cases hlu : cm₀.labelsUnique <;> simp [hlu] at h
  cases hau : cm₀.addrsUnique <;> simp [hau] at h
  cases hpu : cm₀.padsOk <;> simp [hpu] at h
  subst h
  have hndL : cm₀.labels.Nodup := nodup_of_labelsUniqueGo cm₀.labels hlu
  have hndA : (cm₀.blocks.map fun b => cm₀.symAddr b.label).Nodup :=
    nodup_of_addrsUniqueGo _ hau
  have hinj : ∀ b₁ ∈ cm₀.blocks, ∀ b₂ ∈ cm₀.blocks,
      cm₀.symAddr b₁.label = cm₀.symAddr b₂.label → b₁ = b₂ := by
    intro b₁ hb₁ b₂ hb₂ heq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb₁
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb₂
    have hiM : i < (cm₀.blocks.map fun b => cm₀.symAddr b.label).length := by simp [hi]
    have hjM : j < (cm₀.blocks.map fun b => cm₀.symAddr b.label).length := by simp [hj]
    have hij : i = j := nodup_getElem_inj hndA hiM hjM (by simpa using heq)
    subst hij; rfl
  exact ⟨rfl, ⟨hndL, hinj, fun l hl b hb => VllCodeMap.padsOk_spec hpu hl hb⟩, hlu, hau, hpu⟩

theorem vllLookupLabel_of_wf {A : Arch} {cm : VllCodeMap A} (hwf : cm.Wf) {b : Block A}
    (hb : b ∈ cm.blocks) : cm.lookupLabel b.label = some b := by
  have hnd := hwf.labels_nodup
  dsimp only [VllCodeMap.labels] at hnd
  dsimp only [VllCodeMap.lookupLabel]
  match hbl : cm.blocks with
  | [] => rw [hbl] at hb; cases hb
  | x :: xs =>
    rw [hbl] at hb hnd
    have hrec : ∀ (l : List (Block A)), (l.map Block.label).Nodup → b ∈ l →
        l.find? (fun c => c.label == b.label) = some b := by
      intro l hl hm
      induction l with
      | nil => cases hm
      | cons y ys ih =>
        rw [List.map_cons, List.nodup_cons] at hl
        dsimp only [List.find?]
        rcases List.mem_cons.mp hm with rfl | htail
        · simp
        · have hne : y.label ≠ b.label := fun h => hl.1 (h ▸ List.mem_map.mpr ⟨b, htail, rfl⟩)
          simp [beq_false_of_ne hne, ih hl.2 htail]
    exact hrec (x :: xs) hnd hb

private theorem lowerM_bind_ok {α β : Type} {m : LowerM α} {f : α → LowerM β} {s0 s1 : Nat}
    {r : β} (h : (m >>= f).run s0 = .ok (r, s1)) :
    ∃ a sMid, m.run s0 = .ok (a, sMid) ∧ (f a).run sMid = .ok (r, s1) := by
  change Except.bind (m.run s0) (fun p => (f p.1).run p.2) = .ok (r, s1) at h
  cases hm : m.run s0 with
  | error e => rw [hm] at h; cases h
  | ok p => rw [hm] at h; exact ⟨p.1, p.2, rfl, h⟩

private theorem lowerM_mapM_mem {α β : Type} (f : α → LowerM (List β)) :
    ∀ (xs : List α) (s0 s1 : Nat) (xss : List (List β)),
      (xs.mapM f).run s0 = .ok (xss, s1) →
      ∀ x ∈ xs, ∃ sA sB ys, (f x).run sA = .ok (ys, sB) ∧ ∀ y ∈ ys, y ∈ xss.flatten
  | [], _, _, _, _, _, hx => by cases hx
  | x :: xs, s0, s1, xss, h, z, hz => by
    rw [List.mapM_cons] at h
    obtain ⟨y0, sMid, hx, h1⟩ := lowerM_bind_ok h
    obtain ⟨xss', sEnd, hxs, h2⟩ := lowerM_bind_ok h1
    change Except.ok (y0 :: xss', sEnd) = Except.ok _ at h2
    cases h2
    rcases List.mem_cons.mp hz with rfl | hzTail
    · exact ⟨s0, sMid, y0, hx, fun y hy => List.mem_flatten.mpr ⟨y0, List.mem_cons_self, hy⟩⟩
    · obtain ⟨sA, sB, ys, hfy, hmem⟩ := lowerM_mapM_mem f xs sMid s1 xss' hxs z hzTail
      exact ⟨sA, sB, ys, hfy, fun y hy => by
        have := hmem y hy
        rw [List.flatten_cons]; exact List.mem_append_right _ this⟩

private theorem lowerPlainBody_head {A : Arch} (b : WordRegBind A) (cm : CodeMap) (auxPfx : Sym)
    (frameSlots? : Option Nat) :
    ∀ (blk : BlockFlat) (curLbl : Sym) (pad? : Option PadKind) (acc : List (Instr A)) (d : Nat)
      {s0 s1 : Nat} {bs : List (Block A)},
      (lowerPlainBody b cm auxPfx frameSlots? curLbl pad? acc d blk).run s0 = .ok (bs, s1) →
      ∃ blk0 rest, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = pad?
  | .let_ _ k, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨_, sMid, _, hk⟩ := lowerM_bind_ok h
    exact lowerPlainBody_head b cm auxPfx frameSlots? k l p _ _ hk
  | .load _ _ k, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨_, sMid, _, hk⟩ := lowerM_bind_ok h
    exact lowerPlainBody_head b cm auxPfx frameSlots? k l p _ _ hk
  | .store _ _ k, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨_, sMid, _, hk⟩ := lowerM_bind_ok h
    exact lowerPlainBody_head b cm auxPfx frameSlots? k l p _ _ hk
  | .codeAddr _ k, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    split at h
    · dsimp only [liftEx, StateT.lift] at h; cases h
    · exact lowerPlainBody_head b cm auxPfx frameSlots? k l p _ _ h
  | .jnz _ _ _, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
    obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
    obtain ⟨_, s3', _, h4⟩ := lowerM_bind_ok h3
    obtain ⟨_, s4', _, h5⟩ := lowerM_bind_ok h4
    obtain ⟨_, s5', _, h6⟩ := lowerM_bind_ok h5
    change StateT.pure _ s5' = Except.ok _ at h6
    cases h6
    exact ⟨_, _, rfl, rfl, rfl⟩
  | .ijmp _ _, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
    obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
    change StateT.pure _ s2' = Except.ok _ at h3
    cases h3
    exact ⟨_, _, rfl, rfl, rfl⟩
  | .halt _, l, p, acc, d, _, _, _, h => by
    dsimp only [lowerPlainBody] at h
    obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
    change StateT.pure _ s1' = Except.ok _ at h2
    cases h2
    exact ⟨_, _, rfl, rfl, rfl⟩
  | .hlt, _, _, _, _, _, _, _, h => by
    dsimp only [lowerPlainBody, liftEx, StateT.lift] at h; cases h

private theorem lowerStrideCascade_head {A : Arch} (b : WordRegBind A) (cr : ContifyRegion)
    (nPriv ns : Nat) (needFrame needGuard : Bool) (ccEq : A.Cond) :
    ∀ (targets : List (BitVec 64)) (curLbl : Sym) (acc : List (Instr A)) (idx : Nat)
      {s0 s1 : Nat} {bs : List (Block A)},
      (lowerStrideCascade b cr nPriv ns needFrame needGuard ccEq curLbl acc idx targets).run s0 =
        .ok (bs, s1) →
      ∃ blk0 rest, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none
  | [], l, _, _, s0, _, _, h => by
    dsimp only [lowerStrideCascade] at h
    change StateT.pure _ s0 = Except.ok _ at h; cases h; exact ⟨_, _, rfl, rfl, rfl⟩
  | [lastPc], l, _, _, s0, _, _, h => by
    dsimp only [lowerStrideCascade] at h
    split at h
    · change StateT.pure _ s0 = Except.ok _ at h; cases h; exact ⟨_, _, rfl, rfl, rfl⟩
    · obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
      change StateT.pure _ s1' = Except.ok _ at h2; cases h2; exact ⟨_, _, rfl, rfl, rfl⟩
  | _ :: _ :: _, l, _, _, _, _, _, h => by
    dsimp only [lowerStrideCascade] at h
    obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
    obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
    change StateT.pure _ s2' = Except.ok _ at h3; cases h3; exact ⟨_, _, rfl, rfl, rfl⟩

private theorem lowerGuardedTargets_head {A : Arch} (b : WordRegBind A) (cr : ContifyRegion)
    (nPriv ns : Nat) (needFrame : Bool) (ccEq : A.Cond) :
    ∀ (targets : List (BitVec 64)) (curLbl : Sym) (acc : List (Instr A))
      {s0 s1 : Nat} {bs : List (Block A)},
      (lowerGuardedTargets b cr nPriv ns needFrame ccEq curLbl acc targets).run s0 = .ok (bs, s1) →
      ∃ blk0 rest, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none
  | [], l, _, s0, _, _, h => by
    dsimp only [lowerGuardedTargets] at h
    change StateT.pure _ s0 = Except.ok _ at h; cases h; exact ⟨_, _, rfl, rfl, rfl⟩
  | _ :: _, l, _, _, _, _, h => by
    dsimp only [lowerGuardedTargets] at h
    obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
    obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
    change StateT.pure _ s2' = Except.ok _ at h3; cases h3; exact ⟨_, _, rfl, rfl, rfl⟩

private theorem lowerContEdge_head {A : Arch} (b : WordRegBind A) (cr : ContifyRegion)
    (spillBase ns : Nat) (needFrame : Bool) (st : ContSymState) (d : Nat)
    (curLbl : Sym) (acc : List (Instr A)) (tgt : Arg K i64) (nxt : RegsExpr K)
    (kind : EdgeKind) {s0 s1 : Nat} {bs : List (Block A)}
    (h : (lowerContEdge b cr spillBase ns needFrame st d curLbl acc tgt nxt kind).run s0 =
      .ok (bs, s1)) :
    ∃ blk0 rest, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none := by
  dsimp only [lowerContEdge] at h
  cases kind with
  | direct _ =>
    dsimp only at h
    obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
    change StateT.pure _ s1' = Except.ok _ at h2; cases h2; exact ⟨_, _, rfl, rfl, rfl⟩
  | select _ _ =>
    dsimp only at h; split at h
    · obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
      change StateT.pure _ s1' = Except.ok _ at h2; cases h2; exact ⟨_, _, rfl, rfl, rfl⟩
    · dsimp only [liftEx, StateT.lift] at h; cases h
  | strideTable _ _ needGuard =>
    dsimp only at h; split at h
    · cases hcc : b.condOfCmp? .eq with
      | none => rw [hcc] at h; dsimp only [liftEx, StateT.lift] at h; cases h
      | some cc =>
        rw [hcc] at h
        cases needGuard
        · obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
          obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
          exact lowerStrideCascade_head b cr cr.privFrame.numSlots ns needFrame _ cc _ _ _ _ h3
        · obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
          obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
          exact lowerStrideCascade_head b cr cr.privFrame.numSlots ns needFrame _ cc _ _ _ _ h3
    · dsimp only [liftEx, StateT.lift] at h; cases h
  | contCall _ _ dualRet _ altRetPc? =>
    cases habi : cr.abi <;> rw [habi] at h <;> dsimp only at h
    · obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
      cases dualRet
      · simp only [Bool.false_eq_true, ↓reduceIte] at h2
        change StateT.pure _ s1' = Except.ok _ at h2; cases h2; exact ⟨_, _, rfl, rfl, rfl⟩
      · simp only [↓reduceIte] at h2
        cases halt : altRetPc? with
        | none => rw [halt] at h2; dsimp only [liftEx, StateT.lift] at h2; cases h2
        | some _ =>
          rw [halt] at h2; dsimp only at h2
          obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
          change StateT.pure _ s2' = Except.ok _ at h3; cases h3; exact ⟨_, _, rfl, rfl, rfl⟩
    · dsimp only [liftEx, StateT.lift] at h; cases h
  | contRet isAlt =>
    cases habi : cr.abi <;> rw [habi] at h
    · cases isAlt <;> (dsimp only [liftEx, StateT.lift] at h; cases h)
    · rename_i dualRet; cases dualRet <;> cases isAlt
      · dsimp only at h; obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
        change StateT.pure _ s1' = Except.ok _ at h2; cases h2; exact ⟨_, _, rfl, rfl, rfl⟩
      · dsimp only [liftEx, StateT.lift] at h; cases h
      · dsimp only at h; obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
        change StateT.pure _ s1' = Except.ok _ at h2; cases h2; exact ⟨_, _, rfl, rfl, rfl⟩
      · dsimp only at h; obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
        change StateT.pure _ s1' = Except.ok _ at h2; cases h2; exact ⟨_, _, rfl, rfl, rfl⟩
  | guarded _ =>
    cases habi : cr.abi <;> rw [habi] at h <;> dsimp only at h
    · cases hcc : b.condOfCmp? .eq with
      | none => rw [hcc] at h; dsimp only [liftEx, StateT.lift] at h; cases h
      | some cc =>
        rw [hcc] at h; dsimp only at h
        obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
        obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
        exact lowerGuardedTargets_head b cr cr.privFrame.numSlots ns needFrame cc _ _ _ h3
    · dsimp only [liftEx, StateT.lift] at h; cases h
  | bailout =>
    cases habi : cr.abi <;> rw [habi] at h <;> dsimp only at h
    · obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
      obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
      change StateT.pure _ s2' = Except.ok _ at h3; cases h3; exact ⟨_, _, rfl, rfl, rfl⟩
    · dsimp only [liftEx, StateT.lift] at h; cases h
  | memTableRo _ | memTableGuarded _ _ =>
    cases habi : cr.abi <;> rw [habi] at h <;> dsimp only [liftEx, StateT.lift] at h <;> cases h

private theorem lowerContBlock_head {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) (pc : BitVec 64) (spillBase ns : Nat) (needFrame : Bool) :
    ∀ (blk : BlockFlat) (curLbl : Sym) (acc : List (Instr A)) (d : Nat) (path : BranchPath)
      (st : ContSymState) {s0 s1 : Nat} {bs : List (Block A)},
      (lowerContBlock b cm cr pc spillBase ns needFrame curLbl acc d path st blk).run s0 =
        .ok (bs, s1) →
      ∃ blk0 rest, bs = blk0 :: rest ∧ blk0.label = curLbl ∧ blk0.pad? = none
  | .let_ _ k, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    obtain ⟨_, sMid, _, hk⟩ := lowerM_bind_ok h
    exact lowerContBlock_head b cm cr pc spillBase ns needFrame k l _ _ _ _ hk
  | .load t a k, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    cases hslot : (if cr.privFrame.numSlots > 0 && t == i64 then spSlotOf? cr.privFrame.numSlots
        (st.evalArg a) else none) with
    | some _ =>
      rw [hslot] at h
      exact lowerContBlock_head b cm cr pc spillBase ns needFrame k l _ _ _ _ h
    | none =>
      rw [hslot] at h; dsimp only at h
      split at h
      · obtain ⟨_, sMid, _, hk⟩ := lowerM_bind_ok h
        exact lowerContBlock_head b cm cr pc spillBase ns needFrame k l _ _ _ _ hk
      · obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
        obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
        obtain ⟨_, s3', _, h4⟩ := lowerM_bind_ok h3
        obtain ⟨_, s4', _, h5⟩ := lowerM_bind_ok h4
        obtain ⟨_, s5', _, h6⟩ := lowerM_bind_ok h5
        obtain ⟨_, s6', _, h7⟩ := lowerM_bind_ok h6
        change StateT.pure _ s6' = Except.ok _ at h7; cases h7; exact ⟨_, _, rfl, rfl, rfl⟩
  | .store v a k, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    cases hslot : (if cr.privFrame.numSlots > 0 && _ == i64 then spSlotOf? cr.privFrame.numSlots
        (st.evalArg a) else none) with
    | some _ =>
      rw [hslot] at h
      obtain ⟨_, sMid, _, hk⟩ := lowerM_bind_ok h
      exact lowerContBlock_head b cm cr pc spillBase ns needFrame k l _ _ _ _ hk
    | none =>
      rw [hslot] at h; dsimp only at h
      split at h
      · obtain ⟨_, sMid, _, hk⟩ := lowerM_bind_ok h
        exact lowerContBlock_head b cm cr pc spillBase ns needFrame k l _ _ _ _ hk
      · obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
        obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
        obtain ⟨_, s3', _, h4⟩ := lowerM_bind_ok h3
        obtain ⟨_, s4', _, h5⟩ := lowerM_bind_ok h4
        obtain ⟨_, s5', _, h6⟩ := lowerM_bind_ok h5
        obtain ⟨_, s6', _, h7⟩ := lowerM_bind_ok h6
        change StateT.pure _ s6' = Except.ok _ at h7; cases h7; exact ⟨_, _, rfl, rfl, rfl⟩
  | .codeAddr _ k, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    cases hca : cm.addrOf? _ with
    | none => rw [hca] at h; dsimp only [liftEx, StateT.lift] at h; cases h
    | some _ =>
      rw [hca] at h
      exact lowerContBlock_head b cm cr pc spillBase ns needFrame k l _ _ _ _ h
  | .jnz _ _ _, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
    obtain ⟨_, s2', _, h3⟩ := lowerM_bind_ok h2
    obtain ⟨_, s3', _, h4⟩ := lowerM_bind_ok h3
    obtain ⟨_, s4', _, h5⟩ := lowerM_bind_ok h4
    obtain ⟨_, s5', _, h6⟩ := lowerM_bind_ok h5
    change StateT.pure _ s5' = Except.ok _ at h6; cases h6; exact ⟨_, _, rfl, rfl, rfl⟩
  | .ijmp tgt nxt, l, acc, d, path, st, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    cases hfe : cr.toRegionWitness.findEdge pc path with
    | none => rw [hfe] at h; dsimp only [liftEx, StateT.lift] at h; cases h
    | some _ =>
      rw [hfe] at h
      exact lowerContEdge_head b cr spillBase ns needFrame st d l acc tgt nxt _ h
  | .halt _, l, acc, d, _, _, _, _, _, h => by
    dsimp only [lowerContBlock] at h
    obtain ⟨_, s1', _, h2⟩ := lowerM_bind_ok h
    change StateT.pure _ s1' = Except.ok _ at h2; cases h2; exact ⟨_, _, rfl, rfl, rfl⟩
  | .hlt, _, _, _, _, _, _, _, _, h => by
    dsimp only [lowerContBlock, liftEx, StateT.lift] at h; cases h

theorem fromWord_wf {A : Arch} {b : WordRegBind A} {cm : CodeMap} {vcm : VllCodeMap A}
    (h : fromWord b cm = .ok vcm) :
    cm.Wf ∧ vcm.Wf ∧ vcm.padsOk = true ∧
      (∀ sym a, cm.addrOf? sym = some a → vcm.symAddr sym = a) ∧
      (∀ e ∈ cm, vcm.symAddr e.name = e.addr ∧
        ∃ (blk : Block A) (sA sB : Nat) (bs : List (Block A)),
          (lowerPlainEntry b cm e).run sA = .ok (bs, sB) ∧ bs.head? = some blk ∧
          blk ∈ vcm.blocks ∧ blk.label = e.name ∧ blk.pad? = some b.padKind ∧
          vcm.lookupPc e.addr = some blk) := by
  dsimp only [fromWord] at h
  cases hck : cm.checkWf with
  | false => rw [hck] at h; cases h
  | true =>
    rw [hck] at h
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    have hcmwf : cm.Wf := CodeMap.wf_of_checkWf hck
    cases hrun : (cm.mapM (lowerPlainEntry b cm)).run 0 with
    | error err =>
      change Except.bind ((cm.mapM (lowerPlainEntry b cm)).run 0) _ = .ok vcm at h
      rw [hrun] at h; cases h
    | ok p =>
      rcases p with ⟨blocksList, sEnd⟩
      change Except.bind ((cm.mapM (lowerPlainEntry b cm)).run 0) _ = .ok vcm at h
      rw [hrun] at h; dsimp only [Except.bind] at h
      obtain ⟨rfl, hvwf, _, _, hpads⟩ := finalizeVllCodeMap_wf h
      have hnd0 : (cm.map fun e => e.name).Nodup := hcmwf.namesNodup
      have hndNames : ((cm.map fun e => (e.name, e.addr)).map Prod.fst).Nodup := by
        simpa [Function.comp_def] using hnd0
      refine ⟨hcmwf, hvwf, hpads, ?_, ?_⟩
      · intro sym a ha
        obtain ⟨e, he, rfl, rfl⟩ := CodeMap.addrOf?_mem ha
        exact buildVllSymAddr_base hndNames (List.mem_map.mpr ⟨e, he, rfl⟩)
      · intro e he
        have hsa : buildVllSymAddr (cm.map fun e => (e.name, e.addr)) blocksList.flatten e.name =
            e.addr := buildVllSymAddr_base hndNames (List.mem_map.mpr ⟨e, he, rfl⟩)
        obtain ⟨sA, sB, bs, hbe, hsub⟩ :=
          lowerM_mapM_mem (lowerPlainEntry b cm) cm 0 sEnd blocksList hrun e he
        have hbe' := hbe
        dsimp only [lowerPlainEntry] at hbe'
        obtain ⟨blk0, rest, rfl, hlbl, hpad⟩ :=
          lowerPlainBody_head b cm e.name _ e.block e.name (some b.padKind) _ 6 hbe'
        have hbMem : blk0 ∈ blocksList.flatten := hsub blk0 List.mem_cons_self
        refine ⟨hsa, blk0, sA, sB, blk0 :: rest, hbe, rfl, hbMem, hlbl, hpad, ?_⟩
        exact by rw [← hsa, ← hlbl]; exact VllCodeMap.lookupPc_of_wf hvwf hbMem

private theorem buildVllSymAddr_contify_cm {A : Arch} {cm : CodeMap} {wit : ContifyWitness}
    (hcmwf : cm.Wf) (hwck : wit.check cm = true) (blocks : List (Block A))
    (hCons : ∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc)
    {sym : Sym} {a : BitVec 64} (ha : cm.addrOf? sym = some a) :
    buildVllSymAddr (wit.regions.map (fun cr => (cr.name, cr.entryPc)) ++
      cm.map (fun e => (e.name, e.addr))) blocks sym = a := by
  let regPairs := wit.regions.map fun cr => (cr.name, cr.entryPc)
  let cmPairs := cm.map fun e => (e.name, e.addr)
  have hwck' := hwck; dsimp only [ContifyWitness.check] at hwck'
  simp only [Bool.and_eq_true] at hwck'
  have hRegNd : (regPairs.map Prod.fst).Nodup := by
    simpa [regPairs, Function.comp_def] using nodup_of_listNodup _ hwck'.1.1
  have hnd0 : (cm.map fun e => e.name).Nodup := hcmwf.namesNodup
  have hCmNd : (cmPairs.map Prod.fst).Nodup := by
    simpa [cmPairs, Function.comp_def] using hnd0
  obtain ⟨e, he, rfl, rfl⟩ := CodeMap.addrOf?_mem ha
  refine buildVllSymAddr_eq_of_lookup (regPairs ++ cmPairs) _ ?_
  rw [lookupSymAddr_append]
  by_cases hReg : e.name ∈ regPairs.map Prod.fst
  · obtain ⟨p, hrp, hfst⟩ := List.mem_map.mp hReg
    obtain ⟨cr, hcr, hpair⟩ := List.mem_map.mp hrp
    subst hpair; dsimp only at hfst
    have haddr : e.addr = cr.entryPc := hCons cr hcr e he hfst.symm
    rw [haddr, ← hfst, lookupSymAddr_mem hRegNd (List.mem_map.mpr ⟨cr, hcr, rfl⟩)]
    rfl
  · rw [lookupSymAddr_none_of_not_mem hReg]
    dsimp only [Option.orElse]
    exact lookupSymAddr_mem hCmNd (List.mem_map.mpr ⟨e, he, rfl⟩)

theorem fromWordContify_wf {A : Arch} {b : WordRegBind A} {cm : CodeMap}
    {wit : ContifyWitness} {vcm : VllCodeMap A} (h : fromWordContify b cm wit = .ok vcm) :
    cm.Wf ∧ wit.check cm = true ∧ vcm.Wf ∧ vcm.padsOk = true ∧
      (∀ cr ∈ wit.regions, vcm.symAddr cr.name = cr.entryPc ∧
        ∃ blk ∈ vcm.blocks, blk.label = cr.name ∧ blk.pad? = some b.padKind ∧
          vcm.lookupPc cr.entryPc = some blk) ∧
      (∀ cr ∈ wit.regions, ∀ pc ∈ cr.allPcs,
        ∃ (blk : Block A) (ceBlock : BlockFlat) (sA sB : Nat) (bs : List (Block A)),
          cm.lookupAddr pc = some ceBlock ∧
          (lowerContBlock b cm cr pc (regionSpillBase cr) (regionFrameSlots b cm cr)
            (regionNeedFrame b cm cr) (innerLabel cr pc) [] 6 []
            ContSymState.init ceBlock).run sA = .ok (bs, sB) ∧
          bs.head? = some blk ∧ blk ∈ vcm.blocks ∧ blk.label = innerLabel cr pc ∧
          vcm.lookupLabel (innerLabel cr pc) = some blk) ∧
      (∀ e ∈ residualContifyCodeMap cm wit, vcm.symAddr e.name = e.addr ∧
        ∃ (blk : Block A) (sA sB : Nat) (bs : List (Block A)),
          (lowerPlainEntry b cm e).run sA = .ok (bs, sB) ∧ bs.head? = some blk ∧
          blk ∈ vcm.blocks ∧ blk.label = e.name ∧ blk.pad? = some b.padKind ∧
          vcm.lookupPc e.addr = some blk) ∧
      (∀ sym a, (∀ cr ∈ wit.regions, ∀ e ∈ cm, e.name = cr.name → e.addr = cr.entryPc) →
        cm.addrOf? sym = some a → vcm.symAddr sym = a) := by
  dsimp only [fromWordContify] at h
  cases hck : cm.checkWf with
  | false => rw [hck] at h; cases h
  | true =>
    rw [hck] at h
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hwck : wit.check cm = true
    case neg =>
      have hwfF : wit.check cm = false := Bool.eq_false_iff.mpr hwck
      rw [hwfF] at h
      dsimp only [Bool.not_false, ↓reduceIte, Bind.bind, Except.bind] at h
      cases h
    case pos =>
      rw [hwck] at h
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hcmwf : cm.Wf := CodeMap.wf_of_checkWf hck
      cases hr1 : (wit.regions.mapM (lowerContRegion b cm)).run 0 with
      | error err =>
        change Except.bind ((wit.regions.mapM (lowerContRegion b cm)).run 0) _ = .ok vcm at h
        rw [hr1] at h; cases h
      | ok p1 =>
        rcases p1 with ⟨regBlocksList, st1⟩
        change Except.bind ((wit.regions.mapM (lowerContRegion b cm)).run 0) _ = .ok vcm at h
        rw [hr1] at h; dsimp only [Except.bind] at h
        let wRes := residualContifyCodeMap cm wit
        cases hr2 : (wRes.mapM (lowerPlainEntry b cm)).run st1 with
        | error err =>
          change Except.bind ((wRes.mapM (lowerPlainEntry b cm)).run st1) _ = .ok vcm at h
          rw [hr2] at h; cases h
        | ok p2 =>
          rcases p2 with ⟨resBlocksList, st2⟩
          change Except.bind ((wRes.mapM (lowerPlainEntry b cm)).run st1) _ = .ok vcm at h
          rw [hr2] at h; dsimp only [Except.bind] at h
          obtain ⟨rfl, hvwf, _, _, hpads⟩ := finalizeVllCodeMap_wf h
          let regPairs := wit.regions.map fun cr => (cr.name, cr.entryPc)
          let cmPairs := cm.map fun e => (e.name, e.addr)
          have hwck' := hwck; dsimp only [ContifyWitness.check] at hwck'
          simp only [Bool.and_eq_true] at hwck'
          have hRegNd : (regPairs.map Prod.fst).Nodup := by
            simpa [regPairs, Function.comp_def] using nodup_of_listNodup _ hwck'.1.1
          have hnd0 : (cm.map fun e => e.name).Nodup := hcmwf.namesNodup
          have hCmNd : (cmPairs.map Prod.fst).Nodup := by
            simpa [cmPairs, Function.comp_def] using hnd0
          have hRegSym : ∀ cr ∈ wit.regions,
              buildVllSymAddr (regPairs ++ cmPairs)
                (regBlocksList.flatten ++ resBlocksList.flatten) cr.name = cr.entryPc :=
            fun cr hcr => by
              refine buildVllSymAddr_eq_of_lookup (regPairs ++ cmPairs) _ ?_
              rw [lookupSymAddr_append,
                lookupSymAddr_mem hRegNd (List.mem_map.mpr ⟨cr, hcr, rfl⟩)]
              rfl
          have hRegBlk : ∀ cr ∈ wit.regions, ∃ blk ∈ regBlocksList.flatten,
              blk.label = cr.name ∧ blk.pad? = some b.padKind := fun cr hcr => by
            obtain ⟨sA, sB, rbs, hregRun, hsub⟩ :=
              lowerM_mapM_mem (lowerContRegion b cm) wit.regions 0 st1 regBlocksList hr1 cr hcr
            dsimp only [lowerContRegion] at hregRun
            obtain ⟨_, _, _, hrest⟩ := lowerM_bind_ok hregRun
            change StateT.pure _ _ = Except.ok _ at hrest; cases hrest
            exact ⟨_, hsub _ List.mem_cons_self, rfl, rfl⟩
          refine ⟨hcmwf, hwck, hvwf, hpads, ?_, ?_, ?_, ?_⟩
          · intro cr hcr
            obtain ⟨blk, hmemR, hlbl, hpad⟩ := hRegBlk cr hcr
            have hmem : blk ∈ regBlocksList.flatten ++ resBlocksList.flatten :=
              List.mem_append_left _ hmemR
            refine ⟨hRegSym cr hcr, blk, hmem, hlbl, hpad, ?_⟩
            rw [← hRegSym cr hcr, ← hlbl]
            exact VllCodeMap.lookupPc_of_wf hvwf hmem
          · intro cr hcr pc hpc
            obtain ⟨sA, sB, rbs, hregRun, hsub⟩ :=
              lowerM_mapM_mem (lowerContRegion b cm) wit.regions 0 st1 regBlocksList hr1 cr hcr
            dsimp only [lowerContRegion] at hregRun
            obtain ⟨innerLists, sMid, hInners, hrest⟩ := lowerM_bind_ok hregRun
            change StateT.pure _ _ = Except.ok _ at hrest; cases hrest
            obtain ⟨sA', sB', bs, hpcRun, hpcSub⟩ :=
              lowerM_mapM_mem (fun pc => do
                let some ceBlock := cm.lookupAddr pc
                  | liftEx (.error s!"FromWord: missing pc {pc}")
                lowerContBlock b cm cr pc (regionSpillBase cr) (regionFrameSlots b cm cr)
                  (regionNeedFrame b cm cr) (innerLabel cr pc) [] 6 []
                  ContSymState.init ceBlock) cr.allPcs sA sB innerLists hInners pc hpc
            cases hlu : cm.lookupAddr pc with
            | none => rw [hlu] at hpcRun; dsimp only [liftEx, StateT.lift] at hpcRun; cases hpcRun
            | some ceBlock =>
              rw [hlu] at hpcRun
              obtain ⟨blk0, rest, rfl, hlbl, _⟩ :=
                lowerContBlock_head b cm cr pc _ _ _ _ _ _ _ _ _ hpcRun
              have hbMem : blk0 ∈ regBlocksList.flatten ++ resBlocksList.flatten :=
                List.mem_append_left _
                  (hsub _ (List.mem_cons_of_mem _ (hpcSub _ List.mem_cons_self)))
              exact ⟨blk0, ceBlock, sA', sB', blk0 :: rest, rfl, hpcRun, rfl, hbMem, hlbl,
                hlbl ▸ vllLookupLabel_of_wf hvwf hbMem⟩
          · intro e he
            obtain ⟨sA, sB, bs, hbe, hsub⟩ :=
              lowerM_mapM_mem (lowerPlainEntry b cm) wRes st1 st2 resBlocksList hr2 e he
            have hbe' := hbe; dsimp only [lowerPlainEntry] at hbe'
            obtain ⟨blk0, rest, rfl, hlbl, hpad⟩ :=
              lowerPlainBody_head b cm e.name _ e.block e.name (some b.padKind) _ 6 hbe'
            have hbRes : blk0 ∈ resBlocksList.flatten := hsub blk0 List.mem_cons_self
            have hbMem : blk0 ∈ regBlocksList.flatten ++ resBlocksList.flatten :=
              List.mem_append_right _ hbRes
            have hnotReg : e.name ∉ regPairs.map Prod.fst := by
              intro hIn
              obtain ⟨p, hrp, hp⟩ := List.mem_map.mp hIn
              obtain ⟨cr, hcr, hpair⟩ := List.mem_map.mp hrp
              subst hpair; dsimp only at hp
              obtain ⟨blkR, hmemR, hlblR, _⟩ := hRegBlk cr hcr
              have hNdLbl : (regBlocksList.flatten.map Block.label ++
                  resBlocksList.flatten.map Block.label).Nodup := by
                have h1 := hvwf.labels_nodup
                dsimp only [VllCodeMap.labels] at h1
                rwa [List.map_append] at h1
              exact (List.nodup_append.mp hNdLbl).2.2 cr.name
                (List.mem_map.mpr ⟨blkR, hmemR, hlblR⟩) e.name
                (List.mem_map.mpr ⟨blk0, hbRes, hlbl⟩) hp
            have heCm : e ∈ cm := by
              dsimp only [wRes, residualContifyCodeMap] at he
              exact (List.mem_filter.mp he).1
            have hsa : buildVllSymAddr (regPairs ++ cmPairs)
                (regBlocksList.flatten ++ resBlocksList.flatten) e.name = e.addr := by
              refine buildVllSymAddr_eq_of_lookup (regPairs ++ cmPairs) _ ?_
              rw [lookupSymAddr_append, lookupSymAddr_none_of_not_mem hnotReg]
              dsimp only [Option.orElse]
              exact lookupSymAddr_mem hCmNd (List.mem_map.mpr ⟨e, heCm, rfl⟩)
            refine ⟨hsa, blk0, sA, sB, blk0 :: rest, hbe, rfl, hbMem, hlbl, hpad, ?_⟩
            rw [← hsa, ← hlbl]
            exact VllCodeMap.lookupPc_of_wf hvwf hbMem
          · intro sym a hCons ha
            exact buildVllSymAddr_contify_cm hcmwf hwck _ hCons ha

private theorem foldl_step_ge_init {α : Type} (step : Nat → α → Nat)
    (hge : ∀ m x, m ≤ step m x) :
    ∀ (xs : List α) (m : Nat), m ≤ xs.foldl step m
  | [], _ => Nat.le_refl _
  | x :: xs, m => Nat.le_trans (hge m x) (foldl_step_ge_init step hge xs _)

private theorem foldl_step_bound {α : Type} (step : Nat → α → Nat)
    (hge : ∀ m x, m ≤ step m x) {bound : Nat} {x : α} (hbound : ∀ m, bound ≤ step m x) :
    ∀ (xs : List α) (m : Nat), x ∈ xs → bound ≤ xs.foldl step m
  | [], _, hx => by cases hx
  | y :: ys, m, hx => by
    dsimp only [List.foldl]
    rcases List.mem_cons.mp hx with rfl | htail
    · exact Nat.le_trans (hbound m) (foldl_step_ge_init step hge ys _)
    · exact foldl_step_bound step hge hbound ys (step m y) htail

private theorem foldl_max_entry_ge_init {A : Arch} (b : WordRegBind A) :
    ∀ (xs : CodeMap) (m : Nat),
      m ≤ xs.foldl (fun acc e => Nat.max acc (plainEntryBudget b e.block)) m
  | [], _ => Nat.le_refl _
  | _ :: es, m => Nat.le_trans (Nat.le_max_left m _) (foldl_max_entry_ge_init b es _)

theorem plainEntryBudget_le_codeMapMaxBudget {A : Arch} (b : WordRegBind A) {cm : CodeMap}
    {e : CodeEntry} (he : e ∈ cm) :
    plainEntryBudget b e.block ≤ codeMapMaxBudget b cm := by
  dsimp only [codeMapMaxBudget]
  suffices h : ∀ (xs : CodeMap) (m : Nat), e ∈ xs →
      plainEntryBudget b e.block ≤
        xs.foldl (fun acc e' => Nat.max acc (plainEntryBudget b e'.block)) m from
    h cm 0 he
  intro xs
  induction xs with
  | nil => intro _ hm; cases hm
  | cons x ys ih =>
    intro m hm
    dsimp only [List.foldl]
    rcases List.mem_cons.mp hm with rfl | htail
    · exact Nat.le_trans (Nat.le_max_right m _) (foldl_max_entry_ge_init b ys _)
    · exact ih _ htail

theorem maxBlockDepth_le : ∀ (blk : BlockFlat) (d : Nat), d ≤ maxBlockDepth blk d
  | .let_ (ts := ts) _ k, d => Nat.le_trans (Nat.le_add_right d ts.length) (maxBlockDepth_le k _)
  | .load _ _ k, d => Nat.le_trans (Nat.le_succ d) (maxBlockDepth_le k (d + 1))
  | .store _ _ k, d => maxBlockDepth_le k d
  | .codeAddr _ k, d => Nat.le_trans (Nat.le_succ d) (maxBlockDepth_le k (d + 1))
  | .jnz _ t _, d => Nat.le_trans (maxBlockDepth_le t d) (Nat.le_max_left _ _)
  | .ijmp _ _, d => Nat.le_refl d
  | .halt _, d => Nat.le_refl d
  | .hlt, d => Nat.le_refl d

theorem tempSpillCount_mono {A : Arch} (b : WordRegBind A) {d₁ d₂ : Nat} (h : d₁ ≤ d₂) :
    tempSpillCount b d₁ ≤ tempSpillCount b d₂ := by
  dsimp only [tempSpillCount]; omega

theorem regionMaxDepth_ge {cm : CodeMap} {cr : ContifyRegion} {pc : BitVec 64} {blk : BlockFlat}
    (hpc : pc ∈ cr.allPcs) (hlu : cm.lookupAddr pc = some blk) :
    6 ≤ regionMaxDepth cm cr ∧ maxBlockDepth blk 6 ≤ regionMaxDepth cm cr := by
  dsimp only [regionMaxDepth]
  refine ⟨foldl_step_ge_init _
    (fun m p => by cases cm.lookupAddr p <;> simp [Nat.le_max_left]) cr.allPcs 6, ?_⟩
  exact foldl_step_bound _
    (fun m p => by cases cm.lookupAddr p <;> simp [Nat.le_max_left])
    (fun m => by simp [hlu, Nat.le_max_right]) cr.allPcs 6 hpc

theorem regionNeedFrame_of_hasCalls {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    {cr : ContifyRegion} {ew : EdgeWitness} (hew : ew ∈ cr.edges)
    {callee : Sym} {calleePc : BitVec 64} {dualRet : Bool} {retPc : BitVec 64}
    {altPc? : Option (BitVec 64)} (hk : ew.kind = .contCall callee calleePc dualRet retPc altPc?) :
    regionHasCalls cr = true ∧ regionNeedFrame b cm cr = true := by
  have hc : regionHasCalls cr = true := by
    dsimp only [regionHasCalls]; exact List.any_eq_true.mpr ⟨ew, hew, by simp [hk]⟩
  exact ⟨hc, by simp [regionNeedFrame, hc]⟩

private theorem witnessBudgets_append {A : Arch} (b : WordRegBind A) (cm : CodeMap) :
    ∀ (r₁ r₂ : List ContifyRegion) (acc : List (Sym × Nat)),
      witnessBudgets b cm (r₁ ++ r₂) acc =
      witnessBudgets b cm r₂ (witnessBudgets b cm r₁ acc)
  | [], _, _ => rfl
  | _ :: r₁, r₂, _ => witnessBudgets_append b cm r₁ r₂ _

private theorem witnessBudgets_find_not_mem {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (k : Sym) :
    ∀ (xs : List ContifyRegion) (acc : List (Sym × Nat)),
      (∀ cr ∈ xs, cr.name ≠ k) →
      (witnessBudgets b cm xs acc).find? (fun p => p.1 == k) =
        acc.find? (fun p => p.1 == k)
  | [], _, _ => rfl
  | cr :: xs, acc, hne => by
    have hcr : cr.name ≠ k := hne cr List.mem_cons_self
    dsimp only [witnessBudgets]
    rw [witnessBudgets_find_not_mem b cm k xs _
      (fun c hc => hne c (List.mem_cons_of_mem _ hc))]
    simp [List.find?, beq_false_of_ne hcr]

private theorem witnessBudgets_find_head {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    (cr : ContifyRegion) (post : List ContifyRegion) (acc : List (Sym × Nat))
    (hnd : cr.name ∉ post.map (·.name)) :
    (witnessBudgets b cm (cr :: post) acc).find? (fun p => p.1 == cr.name) =
      some (cr.name,
        (if regionNeedFrame b cm cr then A.abi.frameSize (regionFrameSlots b cm cr) else 0) +
        cr.edges.foldl (fun accB ew =>
          match ew.kind with
          | .contCall callee _ _ _ _ =>
            let cb := (acc.find? fun p => p.1 == callee).map Prod.snd |>.getD 0
            Nat.max accB (A.abi.raBytes + cb)
          | _ => accB) 0) := by
  dsimp only [witnessBudgets]
  rw [witnessBudgets_find_not_mem b cm cr.name post _
    (fun c hc heq => hnd (List.mem_map.mpr ⟨c, hc, heq⟩))]
  simp only [List.find?, beq_self_eq_true, Option.some.injEq, Prod.mk.injEq, true_and]
  rfl

theorem witnessBudgets_split {A : Arch} (b : WordRegBind A) (cm : CodeMap)
    {wit : ContifyWitness} (hwck : wit.check cm = true)
    {pre : List ContifyRegion} {cr : ContifyRegion} {post : List ContifyRegion}
    (hSplit : wit.regions = pre ++ cr :: post) :
    let accPre := witnessBudgets b cm pre []
    let selfFrame :=
      if regionNeedFrame b cm cr then A.abi.frameSize (regionFrameSlots b cm cr) else 0
    let maxCallee := cr.edges.foldl (fun accB ew =>
      match ew.kind with
      | .contCall callee _ _ _ _ =>
        let cb := (accPre.find? fun p => p.1 == callee).map Prod.snd |>.getD 0
        Nat.max accB (A.abi.raBytes + cb)
      | _ => accB) 0
    regionStackBudget b cm wit cr = selfFrame + maxCallee ∧
    selfFrame ≤ regionStackBudget b cm wit cr ∧
    ∀ {cr_c : ContifyRegion}, cr_c ∈ pre → ∀ {ew : EdgeWitness}, ew ∈ cr.edges →
      ∀ {calleePc : BitVec 64} {dualRet : Bool} {retPc : BitVec 64}
        {altPc? : Option (BitVec 64)},
        ew.kind = .contCall cr_c.name calleePc dualRet retPc altPc? →
        selfFrame + (A.abi.raBytes + regionStackBudget b cm wit cr_c) ≤
          regionStackBudget b cm wit cr := by
  have hw := hwck; dsimp only [ContifyWitness.check] at hw
  simp only [Bool.and_eq_true] at hw
  have hNd : (wit.regions.map (·.name)).Nodup := nodup_of_listNodup _ hw.1.1
  rw [hSplit, List.map_append, List.map_cons] at hNd
  have hDisj := List.nodup_append.mp hNd
  have hcrPost : cr.name ∉ post.map (·.name) := (List.nodup_cons.mp hDisj.2.1).1
  have hfindCr : regionStackBudget b cm wit cr =
      (if regionNeedFrame b cm cr then A.abi.frameSize (regionFrameSlots b cm cr) else 0) +
      cr.edges.foldl (fun accB ew =>
        match ew.kind with
        | .contCall callee _ _ _ _ =>
          let cb :=
            Option.getD ((witnessBudgets b cm pre []).find? (fun p => p.1 == callee) |>.map
              Prod.snd) 0
          Nat.max accB (A.abi.raBytes + cb)
        | _ => accB) 0 := by
    dsimp only [regionStackBudget]
    rw [hSplit, witnessBudgets_append, witnessBudgets_find_head b cm cr post _ hcrPost]
    rfl
  refine ⟨hfindCr, by rw [hfindCr]; omega, ?_⟩
  intro cr_c hcr_c ew hew calleePc dualRet retPc altPc? hk
  have h_not_post : ∀ x ∈ cr :: post, x.name ≠ cr_c.name := fun x hx heq =>
    (hDisj.2.2 cr_c.name (List.mem_map.mpr ⟨cr_c, hcr_c, rfl⟩)
      x.name (List.mem_map.mpr ⟨x, hx, rfl⟩) heq.symm)
  have hcrc_eq : regionStackBudget b cm wit cr_c =
      Option.getD
        (((witnessBudgets b cm pre []).find? fun p => p.1 == cr_c.name).map Prod.snd) 0 := by
    dsimp only [regionStackBudget]
    rw [hSplit, witnessBudgets_append,
      witnessBudgets_find_not_mem b cm cr_c.name (cr :: post) _ h_not_post]
  have hmem := foldl_step_bound (fun accB (e : EdgeWitness) =>
      match e.kind with
      | .contCall callee _ _ _ _ =>
        let cb :=
          Option.getD (((witnessBudgets b cm pre []).find? fun p => p.1 == callee).map
            Prod.snd) 0
        Nat.max accB (A.abi.raBytes + cb)
      | _ => accB)
    (fun accB e => by cases e.kind <;> simp [Nat.le_max_left])
    (bound := A.abi.raBytes + regionStackBudget b cm wit cr_c)
    (fun accB => by dsimp only; rw [hk]; dsimp only; rw [← hcrc_eq]; exact Nat.le_max_right _ _)
    cr.edges 0 hew
  rw [hfindCr]; omega

end LeanQbe.T.Vll
