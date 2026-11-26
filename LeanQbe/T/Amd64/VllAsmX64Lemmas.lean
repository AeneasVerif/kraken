module

public import LeanQbe.T.Amd64.VllAsmX64Lemmas1
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.AbiLemmas

/-!
# Assembler Verification & Simulation Proofs for SysV x86-64 (`Amd64.VllAsmX64Lemmas`)

Completes verification of `asmX64` / `asmX64List` / `asmX64Block` / `asmX64Prog`:
* `NoLab` & label-map `ρ` preservation (`asmOffset`, `asmX64_noLab`, `asmX64List_labelAddr`).
* Per-instruction and unified straight-line simulation (`asmX64_fallsTo`).
* Inductive sequence simulation (`asmX64List_fallsTo`).
* Control-flow simulation (`asmX64_jmp_run`, `asmX64_jcc_run`, `asmX64_call_run`,
  `asmX64_icall_run`, `asmX64_ret_run`, `asmX64_exitJmp_run`, `asmX64_tailJmpR_run`,
  `asmX64_ijmp_run`, `asmX64_jump`).
* Basic-block execution correspondence (`asmX64Block_run`).

Zero `Arm64`/`Kraken.AArch64` imports, zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll
open Std Std.ExtHashMap

/-! ## 1. `NoLab` and Label-Map `ρ` Preservation -/

/-- Instruction emits no `.label` directives when assembled via `asmX64`. -/
@[expose] def instrNoLab : Instr x64Arch → Prop
  | .label _ => False
  | .native d => ∀ l, Kraken.Directive.label l ≠ d
  | _ => True

/-- Offset in Kraken directives emitted for the first `idx` VLL instructions of `vis`. -/
@[expose] def asmOffset (vis : List (Instr x64Arch)) (idx : Nat) : Nat :=
  (asmX64List (vis.take idx)).length

theorem asmX64_label (l : Sym) : asmX64 (.label l) = [Kraken.Directive.label l] := rfl

theorem asmX64_noLab {i : Instr x64Arch} (hi : instrNoLab i) (l : Sym) :
    Kraken.Directive.label l ∉ asmX64 i := by
  cases i with
  | label _ => exact False.elim hi
  | native d =>
    intro hm
    simp only [asmX64, List.mem_singleton] at hm
    exact hi l hm
  | load w ext rd addr =>
    dsimp only [asmX64]
    cases ext with
    | zx =>
      cases h : x64Load w.toTy rd addr with
      | none => simp
      | some p => simp only [Option.map_some, Option.getD_some]; exact x64Gpr_load_noLab h l
    | sx =>
      cases w with
      | w64 =>
        cases h : x64Load (.bits 64) rd addr with
        | none => simp
        | some p => simp only [Option.map_some, Option.getD_some]; exact x64Gpr_load_noLab h l
      | w8 | w16 | w32 =>
        cases h : x64LoadSext _ 64 rd addr with
        | none => simp
        | some p =>
          simp only [Option.map_some, Option.getD_some]; exact x64Gpr_loadSext_noLab h l
    | sub =>
      cases w with
      | w8 | w16 =>
        dsimp only; split
        · exact List.not_mem_nil
        · intro hm
          rcases List.mem_append.mp hm with h1 | h2
          · exact emitClean_noLab _ l h1
          · simp only [List.mem_singleton] at h2; cases h2
      | w32 | w64 =>
        cases h : x64Load _ rd addr with
        | none => simp
        | some p => simp only [Option.map_some, Option.getD_some]; exact x64Gpr_load_noLab h l
  | store w rs addr =>
    dsimp only [asmX64]
    cases h : x64Store w.toTy (.gpr rs) addr with
    | none => simp
    | some p => simp only [Option.map_some, Option.getD_some]; exact x64Gpr_store_noLab h l
  | movi _ _ => simp [asmX64, moviD]
  | pad _ => simp [asmX64, ins]
  | _ => exact emitClean_noLab _ l

theorem asmX64List_append (xs ys : List (Instr x64Arch)) :
    asmX64List (xs ++ ys) = asmX64List xs ++ asmX64List ys :=
  List.flatMap_append

theorem asmX64List_noLab {is : List (Instr x64Arch)} (his : ∀ i ∈ is, instrNoLab i) (l : Sym) :
    Kraken.Directive.label l ∉ asmX64List is := by
  intro hm
  obtain ⟨i, hi, hmem⟩ := List.mem_flatMap.mp hm
  exact asmX64_noLab (his i hi) l hmem

theorem asmX64List_infixAt {h : Host} {k0 vi : Nat} {vis : List (Instr x64Arch)}
    {i : Instr x64Arch}
    (hc : (asmX64List vis).IsInfixAt Host.prog k0) (hvi : vis[vi]? = some i) :
    (asmX64 i).IsInfixAt Host.prog (k0 + asmOffset vis vi) := by
  have hlt : vi < vis.length :=
    Nat.lt_of_not_ge fun hge => by simp [List.getElem?_eq_none hge] at hvi
  have hsplit : vis = vis.take vi ++ i :: vis.drop (vi + 1) := by
    have helem : vis[vi] = i := (List.getElem?_eq_some_iff.mp hvi).2
    have hd := List.drop_eq_getElem_cons hlt
    rw [helem] at hd
    exact (List.take_append_drop vi vis).symm.trans (congrArg (vis.take vi ++ ·) hd)
  have hc' :
      (asmX64List (vis.take vi) ++ (asmX64 i ++ asmX64List (vis.drop (vi + 1)))).IsInfixAt
        Host.prog k0 := by
    have hcons : asmX64List (i :: vis.drop (vi + 1)) = asmX64 i ++ asmX64List (vis.drop (vi + 1)) :=
      List.flatMap_cons
    rw [hsplit, asmX64List_append, hcons] at hc
    exact hc
  exact hc'.append.2.append.1

theorem asmX64List_labelAddr {h : Host} {k0 vi : Nat} {vis : List (Instr x64Arch)} {l : Sym}
    (hc : (asmX64List vis).IsInfixAt Host.prog k0)
    (hvi : vis[vi]? = some (.label l))
    (hnolab : ∀ j < vi, ∀ i', vis[j]? = some i' →
      i' ≠ .label l ∧ ∀ d, i' = .native d → Kraken.Directive.label l ≠ d)
    (hprior : ∀ k < k0, Host.prog[k]? ≠ some (Kraken.Directive.label l)) :
    hostLabel h l = Host.addrOf (k0 + asmOffset vis vi) := by
  letI := h
  have hinf := asmX64List_infixAt hc hvi
  have hpk : Host.prog[k0 + asmOffset vis vi]? = some (Kraken.Directive.label l) :=
    List.isInfixAt_singleton.mp hinf
  refine Host.label_eq_addrOf hpk fun j hj heq => ?_
  by_cases hj0 : j < k0
  · exact hprior j hj0 heq
  · have hlt : vi < vis.length :=
      Nat.lt_of_not_ge fun hge => by simp [List.getElem?_eq_none hge] at hvi
    have hpre_inf : (asmX64List (vis.take vi)).IsInfixAt Host.prog k0 := by
      have hsplit : vis = vis.take vi ++ vis.drop vi := (List.take_append_drop vi vis).symm
      rw [hsplit, asmX64List_append] at hc
      exact hc.append.1
    have hidx_lt : j - k0 < (asmX64List (vis.take vi)).length := by
      dsimp only [asmOffset] at hj; omega
    have hpre_eq : (asmX64List (vis.take vi))[j - k0]? = some (Kraken.Directive.label l) := by
      have hget := (List.isInfixAt_iff_getElem?.mp hpre_inf) (j - k0) hidx_lt
      rw [Nat.add_sub_cancel' (Nat.le_of_not_lt hj0)] at hget
      rw [List.getElem?_eq_getElem hidx_lt, ← hget, heq]
    have hmem : Kraken.Directive.label l ∈ asmX64List (vis.take vi) :=
      List.mem_of_getElem? hpre_eq
    obtain ⟨i', hi', hlmem⟩ := List.mem_flatMap.mp hmem
    obtain ⟨idx, hidx_mem, rfl⟩ := List.getElem_of_mem hi'
    have hlen_lt : idx < vi := by
      have hlen := List.length_take_le vi vis
      omega
    have hget_vis : vis[idx]? = some (vis.take vi)[idx] :=
      (List.getElem?_take_of_lt hlen_lt).symm.trans (List.getElem?_eq_getElem hidx_mem)
    have hcond := hnolab idx hlen_lt _ hget_vis
    have hnol : instrNoLab (vis.take vi)[idx] := by
      generalize hu : (vis.take vi)[idx] = u at hlmem hcond ⊢
      cases u with
      | label s =>
        dsimp only [asmX64] at hlmem
        rw [List.mem_singleton, Kraken.Directive.label.injEq] at hlmem
        subst hlmem
        exact absurd rfl hcond.1
      | native d =>
        intro _ _
        dsimp only [asmX64] at hlmem
        exact absurd (List.mem_singleton.mp hlmem) (hcond.2 d rfl)
      | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _ | test _ _ _
      | clearFlags | setcc _ _ | load _ _ _ _ | store _ _ _ | slotSt _ _ | slotLd _ _
      | prologue _ | epilogue _ | canonAbi _ _ | jmp _ | jcc _ _ | jnzGpr _ _
      | call _ | icall _ | ret | exitJmp _ | tailJmpR _ | symAddr _ _ | ijmp _ | pad _ =>
        trivial
    exact asmX64_noLab hnol l hlmem

theorem asmX64List_hostSymAddr {h : Host} {k0 vi : Nat} {vis : List (Instr x64Arch)} {l : Sym}
    (hc : (asmX64List vis).IsInfixAt Host.prog k0)
    (hvi : vis[vi]? = some (.label l))
    (hnolab : ∀ j < vi, ∀ i', vis[j]? = some i' →
      i' ≠ .label l ∧ ∀ d, i' = .native d → Kraken.Directive.label l ≠ d)
    (hprior : ∀ k < k0, Host.prog[k]? ≠ some (Kraken.Directive.label l)) :
    hostSymAddr h l = (Host.addrOf (k0 + asmOffset vis vi)).toBitVec :=
  congrArg Int64.toBitVec (asmX64List_labelAddr hc hvi hnolab hprior)

theorem asmX64List_labelAddr_of_unique {h : Host} (hu : h.LabelsUnique)
    {k0 vi : Nat} {vis : List (Instr x64Arch)} {l : Sym}
    (hc : (asmX64List vis).IsInfixAt Host.prog k0) (hvi : vis[vi]? = some (.label l)) :
    hostLabel h l = Host.addrOf (k0 + asmOffset vis vi) := by
  letI := h
  exact Host.label_eq_addrOf_of_unique hu (List.isInfixAt_singleton.mp (asmX64List_infixAt hc hvi))

theorem asmX64Block_infixAt {h : Host} {k0 bi : Nat} {bs : List (Block x64Arch)}
    {b : Block x64Arch}
    (hc : (asmX64List (flattenBlocks bs)).IsInfixAt Host.prog k0)
    (hbi : bs[bi]? = some b) :
    let next? := bs[bi + 1]?.map Block.label
    ∃ off, (asmX64Block next? b).IsInfixAt Host.prog (k0 + off) := by
  induction bs generalizing k0 bi with
  | nil => simp at hbi
  | cons x rest ih =>
    cases bi with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hbi; subst hbi
      cases rest with
      | nil => exact ⟨0, by simpa [flattenBlocks, asmX64Block] using hc⟩
      | cons y ys =>
        have h1 : (asmX64List (x.toInstrs (some y.label)) ++
            asmX64List (flattenBlocks (y :: ys))).IsInfixAt Host.prog k0 := by
          simpa [flattenBlocks, asmX64List_append] using hc
        exact ⟨0, by simpa [asmX64Block] using h1.append.1⟩
    | succ bi' =>
      cases rest with
      | nil => simp at hbi
      | cons y ys =>
        have h1 : (asmX64List (x.toInstrs (some y.label)) ++
            asmX64List (flattenBlocks (y :: ys))).IsInfixAt Host.prog k0 := by
          simpa [flattenBlocks, asmX64List_append] using hc
        obtain ⟨off, hoff⟩ := ih h1.append.2 hbi
        refine ⟨(asmX64List (x.toInstrs (some y.label))).length + off, ?_⟩
        simpa [Nat.add_assoc, asmX64Block] using hoff

theorem asmX64Prog_infixAt {h : Host} {k0 bi : Nat} {cm : VllCodeMap x64Arch}
    {b : Block x64Arch}
    (hc : (asmX64Prog cm).IsInfixAt Host.prog k0) (hbi : cm.blocks[bi]? = some b) :
    let next? := cm.blocks[bi + 1]?.map Block.label
    ∃ off, (asmX64Block next? b).IsInfixAt Host.prog (k0 + off) :=
  asmX64Block_infixAt hc hbi

/-! ## 2. Remaining Straight-Line Simulation & Unified `asmX64_fallsTo` -/

private theorem frame_gpr_set {s s' : MachineData} {gClob : List Reg64} {fClob : FlagMask}
    (hkeep : ∀ r, r ∉ gClob → s'.regs.get64 r = s.regs.get64 r)
    (hzm : s'.zmms = s.zmms) (hflg : x64Mach.UpdFlags x64CondReads s s' fClob) :
    x64Mach.Frame x64CondReads s s' gClob [] fClob :=
  ⟨hkeep, fun vr _ => by simp [hzm], hflg⟩

private theorem maskNone_and_not (m : FlagMask) : maskNone &&& ~~~m = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro b _; simp [maskNone]

private theorem and_not_maskAll (f : FlagMask) : f &&& ~~~maskAll = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro b _; simp [maskAll]

private theorem maskNone_or_and_not (m : FlagMask) : (maskNone ||| m) &&& ~~~m = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro b _; simp [maskNone]

private theorem fallsTo_x64MoviI (s : MachineData) (rd : Reg64) (c : BitVec 64) :
    Directive.FallsTo (.instr (x64MoviI rd c)) s
      (· = { s with regs := s.regs.set64 rd c }) := by
  intro _ _ _ _ _ hk
  simp only [t_step_simp, Int64.toBitVec_ofBitVec, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
  exact hk _ rfl

theorem asmX64_label_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {l : Sym}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) :
    x64Mach.FallsTo x64CondReads h k (asmX64 (.label l)) [] [] maskNone sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.label l)).length)).toBitVec (.label l) sv (.fall sv) ∧
        SimState fMask sv sk') post :=
  dir_to_x64FallsTo (fun {_} _ _ _ _ hk => by simp only [Directive.interp]; exact hk sk rfl)
    fun (sk' : MachineData) (h : sk' = sk) => by
      subst h; exact ⟨⟨rfl, hsim⟩, Machine.Frame.refl _ _ _ _ _⟩

theorem asmX64_pad_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {pk : PadKind}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) :
    x64Mach.FallsTo x64CondReads h k (asmX64 (.pad pk)) [] [] maskNone sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.pad pk)).length)).toBitVec (.pad pk) sv (.fall sv) ∧
        SimState fMask sv sk') post :=
  dir_to_x64FallsTo (fun {_} _ _ _ _ hk => by simp only [t_step_simp]; exact hk sk rfl)
    fun (sk' : MachineData) (h : sk' = sk) => by
      subst h; exact ⟨⟨rfl, hsim⟩, Machine.Frame.refl _ _ _ _ _⟩

theorem asmX64_movi_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {rd : Reg64} {imm : BitVec 64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch) :
    let sv' := sv.setGpr rd imm
    x64Mach.FallsTo x64CondReads h k (asmX64 (.movi rd imm)) (rd :: x64Scratch) [] maskNone sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.movi rd imm)).length)).toBitVec
          (.movi rd imm) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  intro sv'
  have _ := hrd
  refine fun hinf hcont => x64Gpr_movi_spec hinf fun sk' ⟨h1, h2⟩ hfr =>
    hcont sk' ⟨rfl, ⟨fun r hr => ?_, fun vr => (hfr.2.1 vr (by simp)).trans (hsim.2.1 vr),
      h2.trans hsim.2.2.1,
      fun cc hc => (hfr.2.2 cc (FlagMask.disjoint_none _)).trans (hsim.2.2.2 cc hc)⟩⟩ hfr
  by_cases hrr : r = rd
  · subst hrr; simp [sv', h1]
  · dsimp only [sv']; rw [MachSt.gpr_setGpr_ne _ _ hrr]
    exact (hfr.1 r (by simp [List.mem_cons, hrr, hr])).trans (hsim.1 r hr)

theorem asmX64_store_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {w : Vll.Width} {rs : Reg64}
    {addr : AddrArg Reg64} {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrs : rs ∉ x64Scratch)
    (ha : ∀ r ∈ addr.regs, r ∉ x64Scratch) (hval : x64AddrValid addr = true)
    (hst : storeOk sv.mem w.toTy (addr.eval sv.gpr)) :
    x64Mach.FallsTo x64CondReads h k (asmX64 (.store w rs addr)) x64Scratch [] maskNone sk
      (fun sk' => ∃ sv', instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.store w rs addr)).length)).toBitVec
          (.store w rs addr) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  have hst_some : ∃ c, x64Store w.toTy (.gpr rs) addr = some (c, maskNone) := by
    cases w <;> cases addr <;>
      simp_all [Vll.Width.toTy, Vll.Width.bits, x64Store, x64StoreIns, withWidth,
        emitCleanPair, Option.map_some, addrToExprIns]
    all_goals (repeat (first | exact rfl | exact ⟨_, rfl⟩ | split))
  obtain ⟨c, hsc⟩ := hst_some
  have heval : addr.eval sk.regs.get64 = addr.eval sv.gpr := by
    cases addr with
    | baseDisp rb d => simp [AddrArg.eval, hsim.1 rb (ha rb (by simp [AddrArg.regs]))]
    | baseIdxDisp rb ri sc d =>
      simp [AddrArg.eval, hsim.1 rb (ha rb (by simp [AddrArg.regs])),
        hsim.1 ri (ha ri (by simp [AddrArg.regs]))]
    | imm a => rfl
  have hok_k : storeOk sk.dmem w.toTy (addr.eval sk.regs.get64) := by
    rw [hsim.2.2.1, heval]; exact hst
  have hpa : x64Mach.PArgHolds sk w.toTy (.gpr rs) ((sv.gpr rs).setWidth w.bits) := by
    cases w <;> simp [Machine.PArgHolds, GprHolds, Vll.Width.bits, hsim.1 rs hrs]
  simp only [asmX64, hsc, Option.map_some, Option.getD_some]
  intro hinf hcont
  refine x64Gpr_store_spec hsc (fun r hr => by
      rcases List.mem_append.mp hr with h1 | h2
      · simp [PArg.gprs] at h1; exact h1 ▸ hrs
      · exact ha r h2) hpa hok_k hinf fun sk' hmem hfr => ?_
  let sv' := sv.setMem (storeMem sv.mem w.toTy (addr.eval sv.gpr) ((sv.gpr rs).setWidth w.bits))
  refine hcont sk' ⟨sv', ⟨hst, rfl⟩, fun r hr => (hfr.1 r hr).trans (hsim.1 r hr),
    fun vr => (hfr.2.1 vr (by simp)).trans (hsim.2.1 vr),
    hmem.trans (by rw [hsim.2.2.1, heval]; rfl),
    fun cc hc => (hfr.2.2 cc (FlagMask.disjoint_none _)).trans (hsim.2.2.2 cc hc)⟩ hfr

theorem asmX64_slotSt_fallsTo {h : Host} {k idx : Nat} {fMask : FlagMask} {rs : Reg64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrs : rs ∉ x64Scratch)
    (hst : storeOk sv.mem i64 (sv.gpr .rsp + BitVec.ofNat 64 (8 * idx))) :
    let sv' := sv.setMem (storeMem sv.mem i64 (sv.gpr .rsp + BitVec.ofNat 64 (8 * idx)) (sv.gpr rs))
    x64Mach.FallsTo x64CondReads h k (asmX64 (.slotSt idx rs)) x64Scratch [] maskNone sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.slotSt idx rs)).length)).toBitVec
          (.slotSt idx rs) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  intro sv'
  obtain ⟨iload, hload⟩ := hst
  have hrsp : Reg64.rsp ∉ x64Scratch := by simp [x64Scratch]
  have hload_k : sk.dmem.loadInt (sv.gpr .rsp + BitVec.ofNat 64 (8 * idx)) 8 = some iload := by
    simpa [hsim.2.2.1, Ty.bytes, Ty.size, i64] using hload
  have hstore_eq : Mem.storeInt sk.dmem (sv.gpr .rsp + BitVec.ofNat 64 (8 * idx)) 8
      (sv.gpr rs).toInt = sv'.mem := by
    rw [hsim.2.2.1, ← storeMem_bits_eq sv.mem (Or.inr (Or.inr (Or.inr rfl)))]; rfl
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  dsimp only [asmX64, x64SlotSt, x64SlotStIns]
  simp only [emitClean_ite, emitClean_cons, emitClean_nil]
  split
  · refine _root_.Program.wp_singleton fun _ _ => ?_
    simp only [t_step_simp, x64StSpI, x64AtSp_interp, Int64_toBitVec_ofNat,
      MachineData.store, Effects.All_require_write_access, _root_.Width.bytes,
      hsim.1 .rsp hrsp, hsim.1 rs hrs, hload_k, hstore_eq]
    exact Or.inl ⟨trivial, ⟨⟨⟨iload, hload⟩, rfl⟩, hsim.1, hsim.2.1, rfl, hsim.2.2.2⟩,
      frame_gpr_set (fun _ _ => rfl) rfl (updFlags_of_status_eq rfl _)⟩
  · refine Program.wp.cons
      (Directive.FallsTo.wp (fallsTo_x64MoviI sk .r10 (BitVec.ofNat 64 (8 * idx)))) ?_
    rintro s1 rfl
    refine _root_.Program.wp_singleton fun _ _ => ?_
    have hrsp1 : (sk.regs.set64 .r10 (BitVec.ofNat 64 (8 * idx))).get64 .rsp = sv.gpr .rsp :=
      (Reg64s.get64_set64_of_ne _ .r10 .rsp _ (by decide)).trans (hsim.1 .rsp hrsp)
    have hrs1 : (sk.regs.set64 .r10 (BitVec.ofNat 64 (8 * idx))).get64 rs = sv.gpr rs :=
      (Reg64s.get64_set64_of_ne _ .r10 rs _ (ne_of_not_mem_x64Scratch hrs).1.symm).trans
        (hsim.1 rs hrs)
    simp only [t_step_simp, x64AtSpR10_interp, hrsp1, Reg64s.get64_set64_same,
      MachineData.store, Effects.All_require_write_access, _root_.Width.bytes, hload_k, hrs1,
      hstore_eq]
    exact Or.inl ⟨trivial, ⟨⟨⟨iload, hload⟩, rfl⟩, fun r hr =>
        (Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm).trans
          (hsim.1 r hr), hsim.2.1, rfl, hsim.2.2.2⟩,
      frame_gpr_set (fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
        (ne_of_not_mem_x64Scratch hr).1.symm) rfl (updFlags_of_status_eq rfl _)⟩

theorem asmX64_slotLd_fallsTo {h : Host} {k idx : Nat} {fMask : FlagMask} {rd : Reg64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch)
    (hld : ∃ v : BitVec 64, loadVal sv.mem i64 (sv.gpr .rsp + BitVec.ofNat 64 (8 * idx)) = some v) :
    x64Mach.FallsTo x64CondReads h k (asmX64 (.slotLd rd idx)) (rd :: x64Scratch) [] maskNone sk
      (fun sk' => ∃ sv', instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.slotLd rd idx)).length)).toBitVec
          (.slotLd rd idx) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  obtain ⟨v, hv⟩ := hld
  obtain ⟨i, hi, rfl⟩ := loadVal_bits_spec (Or.inr (Or.inr (Or.inr rfl))) hv
  have hrsp : Reg64.rsp ∉ x64Scratch := by simp [x64Scratch]
  have hi_k : sk.dmem.loadInt (sk.regs.get64 .rsp + BitVec.ofNat 64 (8 * idx)) 8 = some i := by
    simpa [hsim.2.2.1, hsim.1 .rsp hrsp, Ty.bytes, i64] using hi
  let sv' := sv.setGpr rd (BitVec.ofInt 64 i)
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  dsimp only [asmX64, x64SlotLd, x64SlotLdIns]
  simp only [emitClean_ite, emitClean_cons, emitClean_nil]
  split
  · refine _root_.Program.wp_singleton fun _ _ => ?_
    simp only [t_step_simp, x64LdSpI, x64AtSp_interp, Int64_toBitVec_ofNat,
      MachineData.load, Effects.All_require_read_access, _root_.Width.bytes, hi_k]
    refine Or.inl ⟨trivial, ⟨sv', ⟨BitVec.ofInt 64 i, hv, rfl⟩, fun r hr => ?_, hsim.2.1,
        hsim.2.2.1, hsim.2.2.2⟩,
      frame_gpr_set (fun r hr => Reg64s.get64_set64_of_ne _ rd r _
        (fun e => hr (by simp [e]))) rfl (updFlags_of_status_eq rfl _)⟩
    by_cases hrr : r = rd
    · subst hrr; simp [sv', Reg64s.get64_set64_same]
    · simp [sv', hrr, Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hrr)]
      exact hsim.1 r hr
  · refine Program.wp.cons
      (Directive.FallsTo.wp (fallsTo_x64MoviI sk .r10 (BitVec.ofNat 64 (8 * idx)))) ?_
    rintro s1 rfl
    refine _root_.Program.wp_singleton fun _ _ => ?_
    have hrsp1 : (sk.regs.set64 .r10 (BitVec.ofNat 64 (8 * idx))).get64 .rsp = sv.gpr .rsp :=
      (Reg64s.get64_set64_of_ne _ .r10 .rsp _ (by decide)).trans (hsim.1 .rsp hrsp)
    have hi1 : sk.dmem.loadInt (sv.gpr .rsp + BitVec.ofNat 64 (8 * idx)) 8 = some i := by
      simpa [hsim.1 .rsp hrsp] using hi_k
    simp only [t_step_simp, x64AtSpR10_interp, hrsp1, Reg64s.get64_set64_same,
      MachineData.load, Effects.All_require_read_access, _root_.Width.bytes, hi1]
    refine Or.inl ⟨trivial, ⟨sv', ⟨BitVec.ofInt 64 i, hv, rfl⟩, fun r hr => ?_, hsim.2.1,
        hsim.2.2.1, hsim.2.2.2⟩,
      frame_gpr_set (fun r hr => ?_) rfl (updFlags_of_status_eq rfl _)⟩
    · by_cases hrr : r = rd
      · subst hrr; simp [sv', Reg64s.get64_set64_same]
      · simp [sv', hrr, Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hrr),
          Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm]
        exact hsim.1 r hr
    · simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1)]

theorem asmX64_prologue_fallsTo {h : Host} {k ns : Nat} {fMask : FlagMask}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) :
    let sp' := sv.gpr .rsp - BitVec.ofNat 64 (x64FrameSize ns)
    let sv' := (sv.setGpr .rsp sp').setFlags (x64Arch.prologueFlags ns sv.flags)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.prologue ns)) (.rsp :: x64Scratch) [] maskAll sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.prologue ns)).length)).toBitVec
          (.prologue ns) sv (.fall sv') ∧
        SimState maskAll sv' sk') post := by
  intro sp' sv'
  have hrsp : Reg64.rsp ∉ x64Scratch := by simp [x64Scratch]
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  dsimp only [asmX64, x64Prologue, x64PrologueIns]
  simp only [emitClean_ite, emitClean_cons, emitClean_nil]
  split
  · refine _root_.Program.wp_singleton fun _ _ => ?_
    simp only [x64SubSpI, t_step_simp, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq]
    refine Or.inl ⟨trivial, ⟨rfl, SimState_maskAll (fun r hr => ?_) hsim.2.1 hsim.2.2.1⟩,
      frame_gpr_set (fun r hr => Reg64s.get64_set64_of_ne _ .rsp r _
        (fun e => hr (by simp [e]))) rfl (updFlags_maskAll _ _)⟩
    by_cases hrr : r = .rsp
    · subst hrr; simp [sv', sp', Reg64s.get64_set64_same, hsim.1 .rsp hrsp, x64Arch]
    · simp [sv', hrr, Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hrr), x64Arch]
      exact hsim.1 r hr
  · refine Program.wp.cons
      (Directive.FallsTo.wp (fallsTo_x64MoviI sk .r10 (BitVec.ofNat 64 (x64FrameSize ns)))) ?_
    rintro s1 rfl
    refine _root_.Program.wp_singleton fun _ _ => ?_
    simp only [t_step_simp, Reg64s.get64_set64_of_ne _ .r10 .rsp _ (by decide),
      Reg64s.get64_set64_same]
    refine Or.inl ⟨trivial, ⟨rfl, SimState_maskAll (fun r hr => ?_) hsim.2.1 hsim.2.2.1⟩,
      frame_gpr_set (fun r hr => ?_) rfl (updFlags_maskAll _ _)⟩
    · by_cases hrr : r = .rsp
      · subst hrr; simp [sv', sp', Reg64s.get64_set64_same, hsim.1 .rsp hrsp, x64Arch]
      · simp [sv', hrr, Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hrr),
          Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm, x64Arch]
        exact hsim.1 r hr
    · simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1)]

theorem asmX64_epilogue_fallsTo {h : Host} {k ns : Nat} {fMask : FlagMask}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) :
    let sp' := sv.gpr .rsp + BitVec.ofNat 64 (x64FrameSize ns)
    let sv' := (sv.setGpr .rsp sp').setFlags (x64Arch.epilogueFlags ns sv.flags)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.epilogue ns)) (.rsp :: x64Scratch) [] maskAll sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.epilogue ns)).length)).toBitVec
          (.epilogue ns) sv (.fall sv') ∧
        SimState maskAll sv' sk') post := by
  intro sp' sv'
  have hrsp : Reg64.rsp ∉ x64Scratch := by simp [x64Scratch]
  refine x64_fallsTo_of_wp fun {_} _ => ?_
  dsimp only [asmX64, x64Epilogue, x64EpilogueIns]
  simp only [emitClean_ite, emitClean_cons, emitClean_nil]
  split
  · refine _root_.Program.wp_singleton fun _ _ => ?_
    simp only [x64AddSpI, t_step_simp, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.add_comm]
    refine Or.inl ⟨trivial, ⟨rfl, SimState_maskAll (fun r hr => ?_) hsim.2.1 hsim.2.2.1⟩,
      frame_gpr_set (fun r hr => Reg64s.get64_set64_of_ne _ .rsp r _
        (fun e => hr (by simp [e]))) rfl (updFlags_maskAll _ _)⟩
    by_cases hrr : r = .rsp
    · subst hrr; simp [sv', sp', Reg64s.get64_set64_same, hsim.1 .rsp hrsp, x64Arch]
    · simp [sv', hrr, Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hrr), x64Arch]
      exact hsim.1 r hr
  · refine Program.wp.cons
      (Directive.FallsTo.wp (fallsTo_x64MoviI sk .r10 (BitVec.ofNat 64 (x64FrameSize ns)))) ?_
    rintro s1 rfl
    refine _root_.Program.wp_singleton fun _ _ => ?_
    simp only [t_step_simp, Reg64s.get64_set64_of_ne _ .r10 .rsp _ (by decide),
      Reg64s.get64_set64_same, BitVec.add_comm]
    refine Or.inl ⟨trivial, ⟨rfl, SimState_maskAll (fun r hr => ?_) hsim.2.1 hsim.2.2.1⟩,
      frame_gpr_set (fun r hr => ?_) rfl (updFlags_maskAll _ _)⟩
    · by_cases hrr : r = .rsp
      · subst hrr; simp [sv', sp', Reg64s.get64_set64_same, hsim.1 .rsp hrsp, x64Arch]
      · simp [sv', hrr, Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hrr),
          Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm, x64Arch]
        exact hsim.1 r hr
    · simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hr.1),
        Reg64s.get64_set64_of_ne _ .r10 r _ (Ne.symm hr.2.1)]

theorem asmX64_canonAbi_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {t : Ty} {r : Reg64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hr : r ∉ x64Scratch)
    (ht : match t with | .bits n => n ∈ x64Arch.abi.bitWidths | _ => True) :
    let sv' := (sv.setGpr r (canonAbiVal t (sv.gpr r))).setFlags (x64Arch.canonAbiFlags t sv.flags)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.canonAbi t r)) (r :: x64Scratch) [] maskNone sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.canonAbi t r)).length)).toBitVec
          (.canonAbi t r) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  intro sv'
  have hsingle : ∀ (n : Nat) (d : Directive)
      (hd : Directive.FallsTo d sk (fun s' =>
        s' = { sk with regs := sk.regs.set64 r (((sk.regs.get64 r).setWidth n).setWidth 64) }))
      (hcv : canonAbiVal t (sv.gpr r) = ((sv.gpr r).setWidth n).setWidth 64),
      x64Mach.FallsTo x64CondReads h k [d] (r :: x64Scratch) [] maskNone sk
        (fun sk' => instrRel x64Arch (hostSymAddr h) (Host.addrOf (k + 1)).toBitVec
            (.canonAbi t r) sv (.fall sv') ∧
          SimState fMask sv' sk') post := by
    intro n d hd hcv
    refine dir_to_x64FallsTo hd ?_
    intro sk' hsk'
    subst hsk'
    refine ⟨⟨rfl, fun q hq => ?_, hsim.2.1, hsim.2.2.1, hsim.2.2.2⟩,
      frame_gpr_set (fun q hq => Reg64s.get64_set64_of_ne _ r q _
        (fun e => hq (by simp [e]))) rfl (updFlags_of_status_eq rfl _)⟩
    by_cases hqr : q = r
    · subst hqr; simp [sv', x64Arch, hcv, hsim.1 q hq]
    · simp [sv', x64Arch, hqr, Reg64s.get64_set64_of_ne _ r q _ (Ne.symm hqr), hsim.1 q hq]
  cases t with
  | bool =>
    dsimp only [asmX64, x64CanonAbi, x64CanonAbiIns, emitClean]
    exact hsingle 8 _ (fun {_} _ _ _ _ hk => by
      simp only [t_step_simp, BitVec.zeroExtend]
      have e : (((sk.regs.get64 r).setWidth 8).setWidth 32).setWidth 64 =
          ((sk.regs.get64 r).setWidth 8).setWidth 64 := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [show (i : Nat) < 64 from hi]
      rw [e]; exact hk _ rfl) rfl
  | bits n =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · dsimp only [asmX64, x64CanonAbi, x64CanonAbiIns, emitClean]
      exact hsingle 8 _ (fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, BitVec.zeroExtend]
        have e : (((sk.regs.get64 r).setWidth 8).setWidth 32).setWidth 64 =
            ((sk.regs.get64 r).setWidth 8).setWidth 64 := by
          apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [show (i : Nat) < 64 from hi]
        rw [e]; exact hk _ rfl) rfl
    · dsimp only [asmX64, x64CanonAbi, x64CanonAbiIns, emitClean]
      exact hsingle 16 _ (fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, BitVec.zeroExtend]
        have e : (((sk.regs.get64 r).setWidth 16).setWidth 32).setWidth 64 =
            ((sk.regs.get64 r).setWidth 16).setWidth 64 := by
          apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [show (i : Nat) < 64 from hi]
        rw [e]; exact hk _ rfl) rfl
    · dsimp only [asmX64, x64CanonAbi, x64CanonAbiIns, emitClean]
      exact hsingle 32 _ (fun {_} _ _ _ _ hk => by
        simp only [t_step_simp, BitVec.zeroExtend]; exact hk _ rfl) rfl
    · simp only [asmX64, x64CanonAbi, x64CanonAbiIns, emitClean_nil]
      refine Machine.FallsTo.nil ⟨rfl, fun q hq => ?_, hsim.2.1, hsim.2.2.1, hsim.2.2.2⟩
      by_cases hqr : q = r
      · subst hqr
        simp [sv', x64Arch, canonAbiVal, BitVec.setWidth_eq, hsim.1 q hq]
      · simp [sv', x64Arch, hqr, hsim.1 q hq]
  | float _ | pair _ _ =>
    simp only [asmX64, x64CanonAbi, x64CanonAbiIns, emitClean_nil]
    refine Machine.FallsTo.nil ⟨rfl, fun q hq => ?_, hsim.2.1, hsim.2.2.1, hsim.2.2.2⟩
    by_cases hqr : q = r
    · subst hqr; simp [sv', x64Arch, canonAbiVal, hsim.1 q hq]
    · simp [sv', x64Arch, hqr, hsim.1 q hq]

theorem asmX64_symAddr_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {sym : Sym} {rd : Reg64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch) :
    let sv' := sv.setGpr rd (hostSymAddr h sym)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.symAddr sym rd)) (rd :: x64Scratch) [] maskNone sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.symAddr sym rd)).length)).toBitVec
          (.symAddr sym rd) sv (.fall sv') ∧
        SimState fMask sv' sk') post := by
  intro sv'
  have _ := hrd
  intro hinf hcont
  refine x64SymAddr_spec hinf fun sk' ⟨h1, h2⟩ hfr =>
    hcont sk' ⟨rfl, fun r hr => ?_, fun vr => (hfr.2.1 vr (by simp)).trans (hsim.2.1 vr),
      h2.trans hsim.2.2.1,
      fun cc hc => (hfr.2.2 cc (FlagMask.disjoint_none _)).trans (hsim.2.2.2 cc hc)⟩ hfr
  by_cases hrr : r = rd
  · subst hrr; simp [sv', h1, hostSymAddr]
  · dsimp only [sv']; rw [MachSt.gpr_setGpr_ne _ _ hrr]
    exact (hfr.1 r (by simp [List.mem_cons, hrr, hr])).trans (hsim.1 r hr)

/-- Unified single-instruction straight-line simulation theorem for `asmX64`. -/
theorem asmX64_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {i : Instr x64Arch}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hpre : VllFallPre h k fMask sv sk i) :
    x64Mach.FallsTo x64CondReads h k (asmX64 i) (i.defs ++ x64Scratch) i.clobVec i.clobFlags sk
      (fun sk' => ∃ sv', instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 i).length)).toBitVec i sv (.fall sv') ∧
        SimState (nextFlagMask i fMask) sv' sk') post := by
  have wk_nil : ∀ {c g f} {Q : MachineData → Prop},
      x64Mach.FallsTo x64CondReads h k c g [] f sk Q post →
      (∀ r ∈ g, r ∈ i.defs ++ x64Scratch) →
      (f &&& ~~~i.clobFlags = 0#8) →
      x64Mach.FallsTo x64CondReads h k c (i.defs ++ x64Scratch) i.clobVec i.clobFlags sk Q post :=
    fun hft hg hf => hft.weaken hg (fun _ hx => by cases hx) hf
  cases i with
  | label l =>
    exact wk_nil (Machine.FallsTo.conseq (asmX64_label_fallsTo hsim) fun _ h _ => ⟨sv, h⟩)
      (fun _ h => by cases h) (maskNone_and_not _)
  | pad pk =>
    exact wk_nil (Machine.FallsTo.conseq (asmX64_pad_fallsTo hsim) fun _ h _ => ⟨sv, h⟩)
      (fun _ h => by cases h) (maskNone_and_not _)
  | mov w rd rs =>
    obtain ⟨_, hreg, _⟩ := hpre
    exact wk_nil (Machine.FallsTo.conseq (asmX64_mov_fallsTo hsim
        (hreg rd (by simp [Instr.defs])) (hreg rs (by simp [Instr.uses]))) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simp only [List.mem_singleton] at hr; subst hr; simp [Instr.defs])
      (maskNone_and_not _)
  | movi rd imm =>
    obtain ⟨_, hreg, _⟩ := hpre
    exact wk_nil (Machine.FallsTo.conseq (asmX64_movi_fallsTo hsim
        (hreg rd (by simp [Instr.defs]))) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr) (maskNone_and_not _)
  | alu op w rd lhs rhs sf =>
    obtain ⟨_, hreg, _⟩ := hpre
    rw [show nextFlagMask (.alu op w rd lhs rhs sf) fMask = if sf then maskNone else maskAll from by
      cases sf <;> rfl]
    exact wk_nil (Machine.FallsTo.conseq (asmX64_alu_fallsTo (rhs := rhs) hsim
        (hreg rd (by simp [Instr.defs])) (hreg lhs (by simp [Instr.uses]))
        fun rs hrs => hreg rs (by subst hrs; simp [Instr.uses, Src.regs]))
        fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr)
      (by dsimp only [Instr.clobFlags, x64Arch]; exact and_not_maskAll _)
  | cmp w lhs rhs =>
    obtain ⟨_, hreg, _⟩ := hpre
    exact wk_nil (Machine.FallsTo.conseq (asmX64_cmp_fallsTo (rhs := rhs) hsim
        (hreg lhs (by simp [Instr.uses]))
        fun rs hrs => hreg rs (by subst hrs; simp [Instr.uses, Src.regs]))
        fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr)
      (by dsimp only [Instr.clobFlags, x64Arch]; exact and_not_maskAll _)
  | test w lhs rhs =>
    obtain ⟨_, hreg, _⟩ := hpre
    exact wk_nil (Machine.FallsTo.conseq (asmX64_test_fallsTo (rhs := rhs) hsim
        (hreg lhs (by simp [Instr.uses]))
        fun rs hrs => hreg rs (by subst hrs; simp [Instr.uses, Src.regs]))
        fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr)
      (by dsimp only [Instr.clobFlags, x64Arch]; exact and_not_maskAll _)
  | clearFlags =>
    exact wk_nil (Machine.FallsTo.conseq (asmX64_clearFlags_fallsTo hsim) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr)
      (by dsimp only [Instr.clobFlags, x64Arch]; exact and_not_maskAll _)
  | setcc rd cc =>
    obtain ⟨_, hreg, hflg⟩ := hpre
    exact wk_nil (Machine.FallsTo.conseq (asmX64_setcc_fallsTo hsim
        (hreg rd (by simp [Instr.defs])) hflg) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr) (maskNone_and_not _)
  | load w ext rd addr =>
    obtain ⟨_, hreg, hval, hld⟩ := hpre
    exact wk_nil (asmX64_load_fallsTo hsim (hreg rd (by simp [Instr.defs]))
        (fun r hr => hreg r (by simp [Instr.uses, hr])) hval hld)
      (fun _ hr => by simpa [Instr.defs] using hr) (maskNone_and_not _)
  | store w rs addr =>
    obtain ⟨_, hreg, hval, hst⟩ := hpre
    exact wk_nil (asmX64_store_fallsTo hsim (hreg rs (by simp [Instr.uses]))
        (fun r hr => hreg r (by simp [Instr.uses, hr])) hval hst)
      (fun _ hr => by simpa [Instr.defs] using hr) (maskNone_and_not _)
  | slotSt idx rs =>
    obtain ⟨_, hreg, hst⟩ := hpre
    exact wk_nil (Machine.FallsTo.conseq (asmX64_slotSt_fallsTo hsim
        (hreg rs (by simp [Instr.uses])) hst) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr) (maskNone_and_not _)
  | slotLd rd idx =>
    obtain ⟨_, hreg, hld⟩ := hpre
    exact wk_nil (asmX64_slotLd_fallsTo hsim (hreg rd (by simp [Instr.defs])) hld)
      (fun _ hr => by simpa [Instr.defs] using hr) (maskNone_and_not _)
  | prologue ns =>
    exact wk_nil (Machine.FallsTo.conseq (asmX64_prologue_fallsTo hsim) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs, x64Arch] using hr)
      (by dsimp only [Instr.clobFlags, x64Arch]; exact and_not_maskAll _)
  | epilogue ns =>
    exact wk_nil (Machine.FallsTo.conseq (asmX64_epilogue_fallsTo hsim) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs, x64Arch, Abi.raRegs, RaKind.raRegs] using hr)
      (by dsimp only [Instr.clobFlags, x64Arch]; exact and_not_maskAll _)
  | canonAbi t r =>
    obtain ⟨_, hreg, ht⟩ := hpre
    exact wk_nil (Machine.FallsTo.conseq (asmX64_canonAbi_fallsTo hsim
        (hreg r (by simp [Instr.defs])) ht) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr) (maskNone_and_not _)
  | symAddr sym rd =>
    obtain ⟨_, hreg, _⟩ := hpre
    exact wk_nil (Machine.FallsTo.conseq (asmX64_symAddr_fallsTo hsim
        (hreg rd (by simp [Instr.defs]))) fun _ h _ => ⟨_, h⟩)
      (fun _ hr => by simpa [Instr.defs] using hr) (maskNone_and_not _)
  | native d => exact asmX64_native_fallsTo hpre
  | jmp _ | jcc _ _ | jnzGpr _ _ | call _ | icall _
  | ret | exitJmp _ | tailJmpR _ | ijmp _ =>
    exact False.elim (by simp [VllFallPre, Instr.isStraightLine, Instr.isControl] at hpre)

/-! ## 3. Straight-Line Sequence Simulation (`asmX64List_fallsTo`) -/

private theorem instrRel_noCall_nextPc {sym : Sym → BitVec 64} {np₁ np₂ : BitVec 64}
    {i : Instr x64Arch} {s : MachSt x64Arch} {o : InstrOut x64Arch}
    (hnc : (∀ sym', i ≠ .call sym') ∧ (∀ r, i ≠ .icall r)) :
    instrRel x64Arch sym np₁ i s o ↔ instrRel x64Arch sym np₂ i s o := by
  cases i with
  | call _ => exact False.elim (hnc.1 _ rfl)
  | icall _ => exact False.elim (hnc.2 _ rfl)
  | _ => exact Iff.rfl

private theorem foldl_clobFlags_cons (i : Instr x64Arch) (rest : List (Instr x64Arch)) :
    (i :: rest).foldl (fun m j => m ||| j.clobFlags) FlagMask.none =
      i.clobFlags ||| rest.foldl (fun m j => m ||| j.clobFlags) FlagMask.none := by
  have hgen : ∀ (xs : List (Instr x64Arch)) (acc : FlagMask),
      xs.foldl (fun m j => m ||| j.clobFlags) acc =
        acc ||| xs.foldl (fun m j => m ||| j.clobFlags) FlagMask.none := by
    intro xs
    induction xs with
    | nil => intro acc; apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [FlagMask.none]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih (acc ||| x.clobFlags), ih (FlagMask.none ||| x.clobFlags), FlagMask.none,
        BitVec.zero_or, BitVec.or_assoc]
  rw [List.foldl_cons, FlagMask.none, BitVec.zero_or, hgen]; rfl

theorem asmX64List_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {is : List (Instr x64Arch)}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hpre : VllListPre h k fMask sv sk is) :
    x64Mach.FallsTo x64CondReads h k (asmX64List is)
      (is.flatMap Instr.defs ++ x64Scratch)
      (is.flatMap Instr.clobVec)
      (is.foldl (fun m i => m ||| i.clobFlags) FlagMask.none) sk
      (fun sk' => ∃ sv', ExecBody x64Arch (hostSymAddr h) is sv (.fall sv') ∧
        SimState (nextFlagMaskList is fMask) sv' sk') post := by
  induction is generalizing k fMask sv sk with
  | nil => exact Machine.FallsTo.nil ⟨sv, .nil, hsim⟩
  | cons i rest ih =>
    obtain ⟨hi_pre, hrest_pre⟩ := hpre
    have hnc : (∀ sym', i ≠ .call sym') ∧ (∀ r, i ≠ .icall r) := by
      cases i <;> simp_all [VllFallPre, Instr.isStraightLine, Instr.isControl]
    have hf_sub : (i.clobFlags ||| rest.foldl (fun m j => m ||| j.clobFlags) FlagMask.none) &&&
        ~~~((i :: rest).foldl (fun m j => m ||| j.clobFlags) FlagMask.none) = 0#8 := by
      rw [foldl_clobFlags_cons]
      apply BitVec.eq_of_getLsbD_eq; intro b hb; simp
    refine (Machine.FallsTo.comp (asmX64_fallsTo hsim hi_pre)
      fun sk1 ⟨sv1, hrel1, hsim1⟩ hfr1 =>
      have hrel0 := (instrRel_noCall_nextPc hnc).mp hrel1
      Machine.FallsTo.conseq (ih hsim1 (hrest_pre sv1 sk1 hrel0 hsim1 hfr1))
        fun _ h2 _ => by
          obtain ⟨sv', hex, hsim'⟩ := h2
          exact ⟨sv', .cons_fall hrel0 hex, hsim'⟩).weaken ?_ ?_ hf_sub
    · intro r hr; simp only [List.mem_append, List.flatMap_cons] at hr ⊢
      rcases hr with (h1 | h2) | (h3 | h4)
      · exact Or.inl (Or.inl h1)
      · exact Or.inr h2
      · exact Or.inl (Or.inr h3)
      · exact Or.inr h4
    · intro vr hvr; simpa [List.flatMap_cons] using hvr

/-! ## 4. Control-Flow Simulation (`asmX64_jump`) & Block Simulation (`asmX64Block_run`) -/

theorem asmX64_jmp_run {h : Host} {k : Nat} {fMask : FlagMask} {l : Sym}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.jmp l)).IsInfixAt Host.prog k)
    (hk : Eventually (step1 Host.exe) post ⟨sk, Int64.ofBitVec (hostSymAddr h l)⟩) :
    x64Mach.Run h k sk post := by
  have _ := fMask; have _ := sv
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp, RelRegOrMem.interp]
  rw [show (Labels.label l : Int64) = hostLabel h l from rfl,
    Int64.add_comm, Int64.sub_add_cancel]
  simpa [hostSymAddr, Int64.ofBitVec_toBitVec] using hk

theorem asmX64_jcc_run {h : Host} {k : Nat} {fMask : FlagMask} {cc : CondCode} {l : Sym}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.jcc cc l)).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk)
    (hflg : FlagMask.disjoint (x64CondReads cc) fMask = true)
    (ht : cc.interp sv.flags = true →
      Eventually (step1 Host.exe) post ⟨sk, Int64.ofBitVec (hostSymAddr h l)⟩)
    (hf : cc.interp sv.flags = false → x64Mach.Run h (k + 1) sk post) :
    x64Mach.Run h k sk post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  simp only [t_step_simp]
  have hcc : cc.interp sk.status = cc.interp sv.flags := hsim.2.2.2 cc hflg
  rw [hcc]
  cases hv : cc.interp sv.flags
  · simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]; exact hf hv
  · simp only [↓reduceIte, Effects.All]
    rw [show (Labels.label l : Int64) = hostLabel h l from rfl,
      ← Int64.ofBitVec_toBitVec (hostLabel h l)]
    exact ht hv

theorem asmX64_call_run {h : Host} {k : Nat} {fMask : FlagMask} {sym : Sym}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.call sym)).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk)
    (hst : storeOk sv.mem i64 (sv.gpr .rsp - 8#64))
    (hcont :
      let sp' := sv.gpr .rsp - 8#64
      let nextPc := (Host.addrOf (k + 1)).toBitVec
      let sv' := (sv.setGpr .rsp sp').setMem (storeMem sv.mem i64 sp' nextPc)
      ∀ sk', SimState fMask sv' sk' →
        x64Mach.Frame x64CondReads sk sk' (.rsp :: x64Scratch) [] maskNone →
        Eventually (step1 Host.exe) post ⟨sk', Int64.ofBitVec (hostSymAddr h sym)⟩) :
    x64Mach.Run h k sk post := by
  letI := h
  obtain ⟨iload, hload⟩ := hst
  have hrsp : Reg64.rsp ∉ x64Scratch := by simp [x64Scratch]
  have hload_k : sk.dmem.loadInt (sk.regs.get64 .rsp - 8#64) 8 = some iload := by
    simpa [hsim.2.2.1, hsim.1 .rsp hrsp, Ty.bytes, Ty.size, i64] using hload
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [asmX64, x64Frame, emitClean, x64CallI]
  simp only [t_step_simp, RelRegOrMem.interp, _root_.Width.bits, _root_.Width.bytes,
    _root_.Width.bytesv, MachineData.store, Effects.All_require_write_access, hload_k]
  rw [show (Labels.label sym : Int64) = hostLabel h sym from rfl,
    Int64.add_comm, Int64.sub_add_cancel]
  let sp' := sv.gpr .rsp - 8#64
  let nextPc := (Host.addrOf (k + 1)).toBitVec
  let sv' := (sv.setGpr .rsp sp').setMem (storeMem sv.mem i64 sp' nextPc)
  let sk' : MachineData :=
    { sk with regs := sk.regs.set64 .rsp (sk.regs.get64 .rsp - 8#64),
              dmem := Mem.storeInt sk.dmem (sk.regs.get64 .rsp - 8#64) 8 nextPc.toInt }
  have hsim' : SimState fMask sv' sk' := by
    refine ⟨fun r hr => ?_, hsim.2.1, ?_, hsim.2.2.2⟩
    · by_cases hrr : r = .rsp
      · subst hrr; simp [sk', sv', sp', Reg64s.get64_set64_same, hsim.1 .rsp hrsp]
      · simp [sk', sv', hrr, Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hrr)]
        exact hsim.1 r hr
    · simp only [sk', sv', sp', nextPc, MachSt.mem_setMem]
      rw [hsim.2.2.1, hsim.1 .rsp hrsp,
        ← storeMem_bits_eq sv.mem (Or.inr (Or.inr (Or.inr rfl)))]; try rfl
  have hfr : x64Mach.Frame x64CondReads sk sk' (.rsp :: x64Scratch) [] maskNone :=
    frame_gpr_set (fun r hr => Reg64s.get64_set64_of_ne _ .rsp r _
      (fun e => hr (by simp [e]))) rfl (updFlags_of_status_eq rfl _)
  exact hcont sk' hsim' hfr

theorem asmX64_icall_run {h : Host} {k : Nat} {fMask : FlagMask} {r : Reg64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.icall r)).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk) (hr : r ∉ x64Scratch)
    (hst : storeOk sv.mem i64 (sv.gpr .rsp - 8#64))
    (hcont :
      let sp' := sv.gpr .rsp - 8#64
      let nextPc := (Host.addrOf (k + 1)).toBitVec
      let sv' := (sv.setGpr .rsp sp').setMem (storeMem sv.mem i64 sp' nextPc)
      ∀ sk', SimState fMask sv' sk' →
        x64Mach.Frame x64CondReads sk sk' (.rsp :: x64Scratch) [] maskNone →
        Eventually (step1 Host.exe) post ⟨sk', Int64.ofBitVec (sv.gpr r)⟩) :
    x64Mach.Run h k sk post := by
  letI := h
  obtain ⟨iload, hload⟩ := hst
  have hrsp : Reg64.rsp ∉ x64Scratch := by simp [x64Scratch]
  have hload_k : sk.dmem.loadInt (sk.regs.get64 .rsp - 8#64) 8 = some iload := by
    simpa [hsim.2.2.1, hsim.1 .rsp hrsp, Ty.bytes, Ty.size, i64] using hload
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [asmX64, x64CallReg, emitClean, x64CallRegI]
  simp only [t_step_simp, RelRegOrMem.interp, _root_.Width.bits, _root_.Width.bytes,
    MachineData.store, Effects.All_require_write_access, hload_k, hsim.1 r hr]
  let sp' := sv.gpr .rsp - 8#64
  let nextPc := (Host.addrOf (k + 1)).toBitVec
  let sv' := (sv.setGpr .rsp sp').setMem (storeMem sv.mem i64 sp' nextPc)
  let sk' : MachineData :=
    { sk with regs := sk.regs.set64 .rsp (sk.regs.get64 .rsp - 8#64),
              dmem := Mem.storeInt sk.dmem (sk.regs.get64 .rsp - 8#64) 8 nextPc.toInt }
  have hsim' : SimState fMask sv' sk' := by
    refine ⟨fun q hq => ?_, hsim.2.1, ?_, hsim.2.2.2⟩
    · by_cases hqr : q = .rsp
      · subst hqr; simp [sk', sv', sp', Reg64s.get64_set64_same, hsim.1 .rsp hrsp]
      · simp [sk', sv', hqr, Reg64s.get64_set64_of_ne _ .rsp q _ (Ne.symm hqr)]
        exact hsim.1 q hq
    · simp only [sk', sv', sp', nextPc, MachSt.mem_setMem]
      rw [hsim.2.2.1, hsim.1 .rsp hrsp,
        ← storeMem_bits_eq sv.mem (Or.inr (Or.inr (Or.inr rfl)))]; try rfl
  have hfr : x64Mach.Frame x64CondReads sk sk' (.rsp :: x64Scratch) [] maskNone :=
    frame_gpr_set (fun q hq => Reg64s.get64_set64_of_ne _ .rsp q _
      (fun e => hq (by simp [e]))) rfl (updFlags_of_status_eq rfl _)
  exact hcont sk' hsim' hfr

theorem asmX64_ret_run {h : Host} {k : Nat} {fMask : FlagMask} {ra : BitVec 64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 .ret).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk)
    (hld : loadVal sv.mem i64 (sv.gpr .rsp) = some ra)
    (hcont :
      let sv' := sv.setGpr .rsp (sv.gpr .rsp + 8#64)
      ∀ sk', SimState fMask sv' sk' →
        x64Mach.Frame x64CondReads sk sk' (.rsp :: x64Scratch) [] maskNone →
        Eventually (step1 Host.exe) post ⟨sk', Int64.ofBitVec ra⟩) :
    x64Mach.Run h k sk post := by
  letI := h
  obtain ⟨i, hi, rfl⟩ := loadVal_bits_spec (Or.inr (Or.inr (Or.inr rfl))) hld
  have hrsp : Reg64.rsp ∉ x64Scratch := by simp [x64Scratch]
  have hi_k : sk.dmem.loadInt (sk.regs.get64 .rsp) 8 = some i := by
    simpa [hsim.2.2.1, hsim.1 .rsp hrsp, Ty.bytes, i64] using hi
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [asmX64, x64Frame, emitClean, x64RetI]
  simp only [t_step_simp, MachineData.load, Effects.All_require_read_access,
    _root_.Width.bytes, _root_.Width.bits, hi_k]
  let sv' := sv.setGpr .rsp (sv.gpr .rsp + 8#64)
  let sk' : MachineData := { sk with regs := sk.regs.set64 .rsp (sk.regs.get64 .rsp + 8#64) }
  have hsim' : SimState fMask sv' sk' := by
    refine ⟨fun r hr => ?_, hsim.2.1, hsim.2.2.1, hsim.2.2.2⟩
    by_cases hrr : r = .rsp
    · subst hrr; simp [sk', sv', Reg64s.get64_set64_same, hsim.1 .rsp hrsp]
    · simp [sk', sv', hrr, Reg64s.get64_set64_of_ne _ .rsp r _ (Ne.symm hrr)]
      exact hsim.1 r hr
  have hfr : x64Mach.Frame x64CondReads sk sk' (.rsp :: x64Scratch) [] maskNone :=
    frame_gpr_set (fun r hr => Reg64s.get64_set64_of_ne _ .rsp r _
      (fun e => hr (by simp [e]))) rfl (updFlags_of_status_eq rfl _)
  exact hcont sk' hsim' hfr

theorem asmX64_exitJmp_run {h : Host} {k : Nat} {sym : Sym}
    {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.exitJmp sym)).IsInfixAt Host.prog k)
    (hk : Eventually (step1 Host.exe) post ⟨sk, Int64.ofBitVec (hostSymAddr h sym)⟩) :
    x64Mach.Run h k sk post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [asmX64, x64Frame, emitClean, x64JmpI]
  simp only [t_step_simp, RelRegOrMem.interp]
  rw [show (Labels.label sym : Int64) = hostLabel h sym from rfl,
    Int64.add_comm, Int64.sub_add_cancel]
  simpa [hostSymAddr, Int64.ofBitVec_toBitVec] using hk

theorem asmX64_tailJmpR_run {h : Host} {k : Nat} {fMask : FlagMask} {r : Reg64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.tailJmpR r)).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk) (hr : r ∉ x64Scratch)
    (hk : Eventually (step1 Host.exe) post ⟨sk, Int64.ofBitVec (sv.gpr r)⟩) :
    x64Mach.Run h k sk post := by
  letI := h
  refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hc) ?_
  dsimp only [asmX64, x64JmpReg, emitClean, x64JmpRegI]
  simp only [t_step_simp, RelRegOrMem.interp, hsim.1 r hr]
  exact hk

theorem asmX64_ijmp_run {h : Host} {k : Nat} {fMask : FlagMask} {r : Reg64}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 (.ijmp r)).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk) (hr : r ∉ x64Scratch)
    (hk : Eventually (step1 Host.exe) post ⟨sk, Int64.ofBitVec (sv.gpr r)⟩) :
    x64Mach.Run h k sk post :=
  asmX64_tailJmpR_run hc hsim hr hk

/-- Unified single-instruction control-flow simulation covering all 28 constructors of
`Instr x64Arch`. -/
theorem asmX64_jump {h : Host} {k : Nat} {fMask : FlagMask} {i : Instr x64Arch}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64 i).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk) (hpre : VllStepPre h k fMask sv sk i)
    (hfall : ∀ sv' sk',
      instrRel x64Arch (hostSymAddr h) (Host.addrOf (k + (asmX64 i).length)).toBitVec
        i sv (.fall sv') →
      SimState (nextFlagMask i fMask) sv' sk' →
      x64Mach.Frame x64CondReads sk sk' (i.defs ++ x64Scratch) i.clobVec i.clobFlags →
      x64Mach.Run h (k + (asmX64 i).length) sk' post)
    (hjump : ∀ pc' sv' sk',
      instrRel x64Arch (hostSymAddr h) (Host.addrOf (k + (asmX64 i).length)).toBitVec
        i sv (.jump pc' sv') →
      SimState (nextFlagMask i fMask) sv' sk' →
      x64Mach.Frame x64CondReads sk sk' (i.defs ++ x64Scratch) i.clobVec i.clobFlags →
      Eventually (step1 Host.exe) post ⟨sk', Int64.ofBitVec pc'⟩) :
    x64Mach.Run h k sk post := by
  cases i with
  | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _ | test _ _ _
  | clearFlags | setcc _ _ | load _ _ _ _ | store _ _ _ | slotSt _ _ | slotLd _ _
  | prologue _ | epilogue _ | canonAbi _ _ | symAddr _ _ =>
    refine asmX64_fallsTo hsim ?_ hc fun sk' hres hfr =>
      let ⟨sv', hrel, hsim'⟩ := hres; hfall sv' sk' hrel hsim' hfr
    exact ⟨rfl, hpre⟩
  | native d => exact asmX64_native_jump hc hpre hfall hjump
  | jmp l =>
    exact asmX64_jmp_run (fMask := fMask) (sv := sv) hc
      (hjump (hostSymAddr h l) sv sk rfl hsim (Machine.Frame.refl _ _ _ _ _))
  | jcc cc l =>
    obtain ⟨_, hflg⟩ := hpre
    refine asmX64_jcc_run hc hsim hflg (fun hcc => ?_) (fun hcc => ?_)
    · exact hjump _ sv sk (by simp [instrRel, x64Arch, hcc]) hsim (Machine.Frame.refl _ _ _ _ _)
    · exact hfall sv sk (by simp [instrRel, x64Arch, hcc]) hsim (Machine.Frame.refl _ _ _ _ _)
  | jnzGpr r l =>
    obtain ⟨hreg, _⟩ := hpre
    refine asmX64_jnzGpr_run hc hsim (hreg r (by simp [Instr.uses])) (fun sk' h0 hsim' hfr => ?_)
      (fun sk' h0 hsim' hfr => ?_)
    · have hrel : instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.jnzGpr r l)).length)).toBitVec (.jnzGpr r l) sv
          (.fall (sv.setFlags (x64JnzGprFlags (sv.gpr r) sv.flags))) := by
        simp [instrRel, x64Arch, h0]
      exact hfall _ sk' hrel hsim'
        (hfr.weaken (fun _ hx => by simpa [Instr.defs] using hx) (fun _ hx => by cases hx)
          (by dsimp only [Instr.clobFlags, x64Arch]; exact and_not_maskAll _))
    · have hrel : instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.jnzGpr r l)).length)).toBitVec (.jnzGpr r l) sv
          (.jump (hostSymAddr h l) (sv.setFlags (x64JnzGprFlags (sv.gpr r) sv.flags))) := by
        simp [instrRel, x64Arch, h0]
      exact hjump _ _ sk' hrel hsim'
        (hfr.weaken (fun _ hx => by simpa [Instr.defs] using hx) (fun _ hx => by cases hx)
          (by dsimp only [Instr.clobFlags, x64Arch]; exact and_not_maskAll _))
  | call sym =>
    obtain ⟨_, hst⟩ := hpre
    refine asmX64_call_run hc hsim hst fun sk' hsim' hfr => ?_
    exact hjump _ _ sk' ⟨hst, rfl⟩ hsim'
      (hfr.weaken (fun _ hx => by simpa [Instr.defs, x64Arch, Abi.raRegs, RaKind.raRegs] using hx)
        (fun _ hx => by cases hx) (maskNone_and_not _))
  | icall r =>
    obtain ⟨hreg, hst⟩ := hpre
    refine asmX64_icall_run hc hsim (hreg r (by simp [Instr.uses])) hst fun sk' hsim' hfr => ?_
    exact hjump _ _ sk' ⟨hst, rfl⟩ hsim'
      (hfr.weaken (fun _ hx => by simpa [Instr.defs, x64Arch, Abi.raRegs, RaKind.raRegs] using hx)
        (fun _ hx => by cases hx) (maskNone_and_not _))
  | ret =>
    obtain ⟨_, ra, hld⟩ := hpre
    refine asmX64_ret_run hc hsim hld fun sk' hsim' hfr => ?_
    exact hjump _ _ sk' ⟨ra, hld, rfl⟩ hsim'
      (hfr.weaken (fun _ hx => by simpa [Instr.defs, x64Arch] using hx)
        (fun _ hx => by cases hx) (maskNone_and_not _))
  | exitJmp sym =>
    exact asmX64_exitJmp_run hc
      (hjump (hostSymAddr h sym) sv sk rfl hsim (Machine.Frame.refl _ _ _ _ _))
  | tailJmpR r =>
    obtain ⟨hreg, _⟩ := hpre
    exact asmX64_tailJmpR_run hc hsim (hreg r (by simp [Instr.uses]))
      (hjump (sv.gpr r) sv sk rfl hsim (Machine.Frame.refl _ _ _ _ _))
  | ijmp r =>
    obtain ⟨hreg, _⟩ := hpre
    exact asmX64_ijmp_run hc hsim (hreg r (by simp [Instr.uses]))
      (hjump (sv.gpr r) sv sk rfl hsim (Machine.Frame.refl _ _ _ _ _))

/-- Straight-line body simulation for basic block `b` starting at label + optional pad. -/
theorem asmX64Block_body_fallsTo {h : Host} {k : Nat} {fMask : FlagMask}
    (b : Block x64Arch) {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk)
    (hbody : let pfx := .label b.label :: match b.pad? with | some pk => [.pad pk] | none => []
      VllListPre h (k + (asmX64List pfx).length) fMask sv sk b.body) :
    let pfx : List (Instr x64Arch) :=
    .label b.label :: match b.pad? with | some pk => [.pad pk] | none => []
    x64Mach.FallsTo x64CondReads h k (asmX64List (pfx ++ b.body))
      (b.body.flatMap Instr.defs ++ x64Scratch)
      (b.body.flatMap Instr.clobVec)
      (b.body.foldl (fun m i => m ||| i.clobFlags) FlagMask.none) sk
      (fun sk' => ∃ sv', ExecBody x64Arch (hostSymAddr h) b.body sv (.fall sv') ∧
        SimState (nextFlagMaskList b.body fMask) sv' sk') post := by
  intro pfx
  have hlab : x64Mach.FallsTo x64CondReads h k (asmX64 (.label b.label)) [] [] maskNone sk
      (· = sk) post :=
    dir_to_x64FallsTo (fun {_} _ _ _ _ hk => by simp only [Directive.interp]; exact hk sk rfl)
      fun (sk' : MachineData) (h : sk' = sk) => by
        subst h; exact ⟨rfl, Machine.Frame.refl _ _ _ _ _⟩
  cases hb : b.pad? with
  | none =>
    rw [show pfx = [.label b.label] by simp [pfx, hb], asmX64List_append,
      show asmX64List [.label b.label] = asmX64 (.label b.label) by simp [asmX64List]]
    have hcomp := Machine.FallsTo.comp hlab fun sk1 hsk1 _ => by
      subst hsk1
      exact asmX64List_fallsTo hsim (by simpa [pfx, hb, asmX64List] using hbody)
    refine hcomp.weaken (fun _ hx => hx) (fun _ hx => hx) (maskNone_or_and_not _)
  | some pk =>
    rw [show pfx = [.label b.label, .pad pk] by simp [pfx, hb], asmX64List_append,
      show asmX64List [.label b.label, .pad pk] =
        asmX64 (.label b.label) ++ asmX64 (.pad pk) by simp [asmX64List]]
    have hpad : x64Mach.FallsTo x64CondReads h (k + (asmX64 (.label b.label)).length)
        (asmX64 (.pad pk)) [] [] maskNone sk (· = sk) post :=
      dir_to_x64FallsTo
        (fun {_} _ _ _ _ hk => by simp only [t_step_simp]; exact hk sk rfl)
        fun (sk' : MachineData) (h : sk' = sk) => by
          subst h; exact ⟨rfl, Machine.Frame.refl _ _ _ _ _⟩
    have hpfx : x64Mach.FallsTo x64CondReads h k
        (asmX64 (.label b.label) ++ asmX64 (.pad pk)) [] [] maskNone sk (· = sk) post :=
      (Machine.FallsTo.comp hlab fun sk1 hsk1 _ => by subst hsk1; exact hpad).weaken
        (fun _ hx => hx) (fun _ hx => hx) (maskNone_and_not _)
    have hcomp := Machine.FallsTo.comp hpfx fun sk1 hsk1 _ => by
      subst hsk1
      exact asmX64List_fallsTo hsim
        (by simpa [pfx, hb, asmX64List, asmX64, Nat.add_assoc] using hbody)
    refine hcomp.weaken (fun _ hx => hx) (fun _ hx => hx) (maskNone_or_and_not _)

/-- Compose straight-line block body simulation with terminator execution for
`asmX64Block next? b`. -/
theorem asmX64Block_run {h : Host} {k : Nat} {fMask : FlagMask} (next? : Option Sym)
    (b : Block x64Arch) {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hc : (asmX64Block next? b).IsInfixAt Host.prog k)
    (hsim : SimState fMask sv sk)
    (hbody : let pfx := .label b.label :: match b.pad? with | some pk => [.pad pk] | none => []
      VllListPre h (k + (asmX64List pfx).length) fMask sv sk b.body)
    (hterm : let pfx := .label b.label :: match b.pad? with | some pk => [.pad pk] | none => []
      let kt := k + (asmX64List (pfx ++ b.body)).length
      ∀ sv' sk', ExecBody x64Arch (hostSymAddr h) b.body sv (.fall sv') →
        SimState (nextFlagMaskList b.body fMask) sv' sk' →
        x64Mach.Frame x64CondReads sk sk' (b.body.flatMap Instr.defs ++ x64Scratch)
          (b.body.flatMap Instr.clobVec)
          (b.body.foldl (fun m i => m ||| i.clobFlags) FlagMask.none) →
        (asmX64List (b.term.toInstrs next?)).IsInfixAt Host.prog kt →
        x64Mach.Run h kt sk' post) :
    x64Mach.Run h k sk post := by
  let pfx : List (Instr x64Arch) :=
    .label b.label :: match b.pad? with | some pk => [.pad pk] | none => []
  have hsplit :
      asmX64Block next? b = asmX64List (pfx ++ b.body) ++ asmX64List (b.term.toInstrs next?) := by
    dsimp only [asmX64Block, Block.toInstrs, pfx]
    exact asmX64List_append _ _
  have hc' := hsplit ▸ hc
  refine asmX64Block_body_fallsTo b hsim hbody hc'.append.1 fun sk' ⟨sv', hex, hsim'⟩ hfr => ?_
  exact hterm sv' sk' hex hsim' hfr hc'.append.2

end LeanQbe.T.Amd64

end
