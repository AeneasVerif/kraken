module

public import LeanQbe.Arm64.TargLemmas
public import LeanQbe.Arm64.IselLemmas
public import LeanQbe.Arm64.FrameLemmas
import all Kraken.Separation
import all Kraken.Mem

/-!
# Kraken AArch64 as a `Target` (QBE `arm64/abi.c` in spirit)

The AAPCS64 conventions of version 0: the return address is in `x30` (`raReg`), it occupies no stack
memory (`raBytes = 0`, `RetAddr` is the empty region), and the stack pointer is 16-byte aligned on
entry (`spEntry`). Every snippet lemma comes from `TargLemmas.lean` or `IselLemmas.lean`.

`step`, `labelAddr`, `get`, `mem` unfold to Kraken's `step1 Host.exe`, `Labels.label`,
`Reg64s.getRegOrSp64` and `MachineData.dmem`.
-/

@[expose] public section

namespace LeanQbe.Arm64

/-- One step of the laid-out host program `h`. -/
def hostStep (h : Host) : MachineState → (MachineState → Prop) → Prop :=
  letI := h; step1 Host.exe

/-- The address label `l` resolves to in host `h`. -/
def hostLabel (h : Host) (l : Label) : Int64 :=
  letI := h; Labels.label l

/-- `x30` is neither allocatable nor scratch. -/
theorem x30_not_allocatable : (XRegOrSp.reg .X30 : Reg) ∉ allocatable := by simp [allocatable]
theorem x30_not_scratch : (XRegOrSp.reg .X30 : Reg) ∉ scratch := by simp [scratch]

/-- Kraken AArch64 as a `Target`. -/
@[reducible] def target : Target where
  toIsa := isa
  MData := MachineData
  Addr := Int64
  State := MachineState
  Host := Host
  get := get
  mem s := s.dmem
  mkState s a := ⟨s, a⟩
  pc st := st.pc
  data st := st.data
  pc_mk _ _ := rfl
  data_mk _ _ := rfl
  mk_eta _ := rfl
  prog h := @Host.prog h
  addrOf h k := @Host.addrOf h k
  labelAddr := hostLabel
  step := hostStep
  raBytes := 0
  RetAddr sp _ := region sp 0
  raReg s ra := s.regs.X30 = ra.toUInt64
  spEntry sp := sp.toNat % 16 = 0
  Saved := Saved
  spOk sp := sp.toNat % 16 = 0
  sp_not_scratch := by simp [scratch]
  sp_not_allocatable := by simp [allocatable]
  scratch_not_allocatable := by simp [scratch, allocatable]
  calleeSaved_not_scratch := by simp [calleeSaved, scratch]
  calleeSaved_not_allocatable := by simp [calleeSaved, allocatable]
  sp_not_calleeSaved := by simp [calleeSaved]
  argRegs_not_scratch := by simp [argRegs, scratch]
  retRegs_not_scratch := by simp [retRegs, scratch]
  sp_not_retRegs := by simp [retRegs]
  sp_not_argRegs := by simp [argRegs]
  calleeSaved_not_argRegs := by simp [calleeSaved, argRegs]
  calleeSaved_not_retRegs := by simp [calleeSaved, retRegs]
  retAddr_region _ _ _ h := h
  raReg_of_raRegs s s' _ hkeep hra := by
    have h : get s' (.reg .X30) = get s (.reg .X30) := hkeep (.reg .X30) (by simp)
    rw [get_reg, get_reg] at h
    show s'.regs.X30 = _
    rw [← hra]
    exact UInt64.toBitVec_inj.mp h
  raRegs_not_allocatable := by simp [allocatable]
  raRegs_not_scratch := by simp [scratch]
  raRegs_not_calleeSaved := by simp [calleeSaved]
  raRegs_not_argRegs := by simp [argRegs]
  raRegs_not_retRegs := by simp [retRegs]
  sp_not_raRegs := by simp
  slots_le_frameSize ns := by show 8 * ns ≤ frameSize ns; have := frameSize_ge ns; omega
  spOk_frame sp ns h := aligned_sub sp _ h (frameSize_mod ns)
  spEntry_call sp ns h := by
    simp only [BitVec.sub_zero]
    exact aligned_sub sp _ h (frameSize_mod ns)
  raReg_congr s s' _ hkeep hra := by
    have h : get s' (.reg .X30) = get s (.reg .X30) :=
      hkeep (.reg .X30) x30_not_allocatable x30_not_scratch
    rw [get_reg, get_reg] at h
    show s'.regs.X30 = _
    rw [← hra]
    exact UInt64.toBitVec_inj.mp h
  labelAddr_eq {h} {_} {_} hk hfirst := letI := h; Host.label_eq_addrOf hk hfirst
  label_spec {h} {_} {_} {_} {_} hi hrun := letI := h; Host.eventually_label hi hrun
  mov_spec {h} {_} {rd} {rs} {s} {_} hc hk := letI := h; Runs.spec (mov_runs rd rs s) hc
    fun _ ⟨h1, h2, h3⟩ => hk _ h1 h2 h3
  movi_spec {h} {_} {rd} {c} {s} {_} hc hk := letI := h; Runs.spec (movi_runs rd c s) hc
    fun _ ⟨h1, h2, h3⟩ => hk _ h1 h2 h3
  op_spec {h} {_} {_} {rd} {_} {_} {_} {_} hop hc hvars hv hk := by
    letI := h
    cases rd with
    | SP => simp [isa, op] at hop
    | reg d => exact Runs.spec (op_runs hop hvars hv) hc fun _ ⟨h1, h2, h3⟩ => hk _ h1 h2 h3
  load_spec {h} {_} {_} {_} {_} {rd} {_} {_} {_} {_} {_} hop hc _ hv hk := by
    letI := h
    cases rd with
    | SP => simp [isa, load] at hop
    | reg d => exact Runs.spec (load_runs hop hv) hc fun _ ⟨h1, h2, h3⟩ => hk _ h1 h2 h3
  store_spec {h} {_} {_} {_} {_} {_} {_} {_} hop hc hvars hok hk :=
    letI := h; Runs.spec (store_runs hop hvars hok) hc fun _ ⟨h1, h2⟩ => hk _ h1 h2
  jmp_spec {h} {_} {_} {_} {s} {_} hc hj hk :=
    letI := h; eventually_jmp hc hj (hk s (fun _ _ => rfl) rfl)
  jnzCmp_spec {h} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} hop hc hj hvars hv hk :=
    letI := h; eventually_jnzCmp hop hc hj hvars hv hk
  prologue_spec {h} {_} {_} {_} {_} {_} {_} hc hra hsp hF hmem hk := by
    letI := h
    exact eventually_prologue hc hra hsp (by simpa using hF) hmem hk
  epilogue_spec {h} {_} {_} {_} {_} {_} {_} hc hsp hF hmem hk := by
    letI := h
    exact eventually_epilogue hc hsp (by simpa using hF) hmem hk
  slotSt_spec {h} {_} {_} {_} {_} {_} {_} hc hr hsp hmem hk := by
    letI := h
    exact eventually_slotSt hc hr hsp hmem hk
  slotLd_spec {h} {_} {_} {_} {_} {_} {_} {_} hc hsp hmem hk := by
    letI := h
    exact eventually_slotLd hc hsp hmem hk
  call_spec {h} {k} {_} {s} {_} {_} hc hmem hk := by
    letI := h
    refine eventually_call hc (hk _ (by simp) (fun r hr => get_wr_of_ne _ _ _ _ ?_) rfl ?_)
    · intro e; subst e; simp at hr
    · simp only [region_zero, BitVec.sub_zero] at hmem ⊢
      exact hmem
  tailJmp_spec {h} {_} {_} {s} {_} hc hk := by
    letI := h
    exact eventually_tailJmp hc (hk s (fun _ _ => rfl) rfl)
  ret_spec {h} {_} {s} {_} {_} {_} hc hra _ hk := by
    letI := h
    exact eventually_ret hc hra (hk s (fun _ _ => rfl) (by simp) rfl)

/-- Labels of size 0, every other directive of size 4, from `0x1000`. -/
@[instance_reducible] def layoutOf (p : Program) : Layout :=
  { start := 0x1000, size := fun i => match p[i]? with | some (.label _) => 0 | _ => 4 }

theorem layoutOf_zero (p : Program) :
    ∀ i d, p[i]? = some d → @Kraken.Layout.size _ (layoutOf p) i = 0 → ∃ l, d = .label l := by
  intro i d hd hz
  cases d
  case label l => exact ⟨l, rfl⟩
  all_goals
    have hz' : (match p[i]? with | some (.label _) => 0 | _ => 4) = 0 := hz
    grind

private theorem sum_sized_mapIdx_le_four (sz : Nat → Nat) (hsz : ∀ i, sz i ≤ 4) :
    ∀ (xs : List Directive) (k : Nat),
      (List.map (·.size)
        (List.mapIdx (fun i d => ({ directive := d, size := sz (k + i) } : Kraken.Sized Directive)) xs)).sum ≤
        4 * xs.length
  | [], _ => by simp
  | _ :: xs, k => by
    rw [List.mapIdx_cons, List.map_cons, List.sum_cons, List.length_cons]
    have h0 : sz (k + 0) ≤ 4 := hsz (k + 0)
    have ih := sum_sized_mapIdx_le_four sz hsz xs (k + 1)
    grind

theorem layoutOf_small (p : Program) (h : 4 * p.length < 2 ^ 64) :
    (@Kraken.Layout.apply _ (layoutOf p) p).sizeBefore p.length < 2 ^ 64 := by
  refine Nat.lt_of_le_of_lt ?_ h
  simp only [Kraken.Executable.sizeBefore, Kraken.Layout.apply]
  rw [List.take_of_length_le (by simp)]
  simpa using sum_sized_mapIdx_le_four (fun i => @Kraken.Layout.size _ (layoutOf p) i)
    (fun i => by
      show (match p[i]? with | some (.label _) => 0 | _ => 4) ≤ 4
      split <;> decide) p 0

def labelsNodup (p : Program) : Bool :=
  stringsNodup (p.filterMap fun | .label l => some l | _ => none)

def targetLayout : TargetLayout target where
  labelsNodup := labelsNodup
  layoutOf prog h := .ofLayout prog (layoutOf prog) (layoutOf_zero prog) (layoutOf_small prog h)
  prog_layoutOf _ _ := rfl
  labelsUnique_layoutOf {prog} h hnd :=
    letI : Host := .ofLayout prog (layoutOf prog) (layoutOf_zero prog) (layoutOf_small prog h)
    Host.labelsUnique_of_nodup (stringsNodup_nodup hnd)

/-- `n`-byte zero stack below `sp = 0x1000`, and payload `bs` at `0x1000`. -/
def initMem (n : Nat) (bs : List UInt8) : Mem 64 :=
  (stackZeros n ++ bs).At (0x1000#64 - BitVec.ofNat 64 n)

theorem initMem_entry (n : Nat) (bs : List UInt8)
    (hn : n ≤ 2048) (hbs : bs.length ≤ 8192) :
    initMem n bs =⋆
      Eq (bs.At 0x1000#64) ⋆
      (fun f => ∃ zs : List UInt8, zs.length = n ∧ f = zs.At (0x1000#64 - BitVec.ofNat 64 n)) ⋆
      Std.ExtHashMap.emp := by
  have hzs : (stackZeros n).length = n := stackZeros_length n
  rw [Std.ExtHashMap.sep_emp, Std.ExtHashMap.sep_comm]
  have h1 := Mem.At_append_sep (stackZeros n) bs (0x1000#64 - BitVec.ofNat 64 n)
    (by simp only [hzs]; omega)
  have e1 : 0x1000#64 - BitVec.ofNat 64 n + BitVec.ofNat 64 (stackZeros n).length = 0x1000#64 := by
    rw [hzs, BitVec.sub_add_cancel]
  rw [e1] at h1
  have h0 : (Eq ((stackZeros n ++ bs).At (0x1000#64 - BitVec.ofNat 64 n))) (initMem n bs) := rfl
  rw [h1] at h0
  exact sep_mono (fun f hf => ⟨stackZeros n, hzs, hf.symm⟩) h0

/-- Concrete initial machine state with stack bound `n`, return address `0x1234` in `x30`,
payload `bs` at `0x1000`, and up to 6 arguments in `x0..x5`. -/
def initState (n : Nat) (bs : List UInt8) (args : List Val) : MachineData :=
  { regs :=
      { X0  := UInt64.ofBitVec (args.getD 0 0)
        X1  := UInt64.ofBitVec (args.getD 1 0)
        X2  := UInt64.ofBitVec (args.getD 2 0)
        X3  := UInt64.ofBitVec (args.getD 3 0)
        X4  := UInt64.ofBitVec (args.getD 4 0)
        X5  := UInt64.ofBitVec (args.getD 5 0)
        SP  := 0x1000
        X30 := (0x1234 : Int64).toUInt64 }
    dmem := initMem n bs }

theorem initState_argsIn (n : Nat) (bs : List UInt8) (args : List Val) (h : args.length ≤ 6) :
    target.ArgsIn args (initState n bs args) := by
  rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | args⟩⟩⟩⟩⟩⟩ <;>
    first | rfl | simp at h

@[reducible] def targetInit : TargetInit target where
  sp0 := 0x1000#64
  ra0 := 0x1234
  ret0 := .reg .X0
  arg0 := .reg .X0
  initState := initState
  get_sp _ _ _ := rfl
  argsIn := initState_argsIn
  raReg _ _ _ := rfl
  spEntry := by decide
  mem_entry n bs _ hn hbs :=
    sep_mono (fun _ => sep_mono_r fun _ hf => by
      simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp]; exact hf)
      (initMem_entry n bs hn hbs)
  retsIn_singleton _ _ := List.head_eq_of_cons_eq
  argsIn_singleton _ _ := List.head_eq_of_cons_eq

private theorem arm64_entry_mem {s : MachineData} {ra : Int64} {b : Nat} {P R : Mem 64 → Prop}
    (hmem : s.dmem =⋆ P ⋆
      (fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R) :
    target.mem s =⋆ P ⋆ target.Entry (target.get s target.sp) ra b ⋆ R := by
  obtain ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, hP, hentry⟩, hrest⟩ := hmem
  refine ⟨f_ab, f_rest, hu1, hd1, ⟨m, f_entry, hu2, hd2, hP, ?_⟩, hrest⟩
  simp only [Target.Entry, region_zero, Std.ExtHashMap.sep_emp, get_sp]
  exact hentry

/-- Translates `Arm64.target.Call` into the concrete Kraken-AArch64 machine statement. -/
theorem arm64_of_call_emp [hh : Host] {sym : String} {b nX : Nat} {args : List Val}
    {P : Mem 64 → Prop} {Q : Post} {X : XPost}
    (hcall : target.Call hh sym b nX args P Q X)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : target.ArgsIn args s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ P ⋆
      (fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧
          (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
            st.data.regs.getXReg r = s.regs.getXReg r) ∧
          st.data.regs.SP = s.regs.SP ∧
          ∃ rets, target.RetsIn rets st.data ∧
            (st.data.dmem =⋆ Q rets ⋆
              (fun f => ∃ bs : List UInt8, bs.length = b ∧
                f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R)) ∨
        (∃ sym' as, target.Defined hh sym' ∧ st.pc = Labels.label sym' ∧
          target.ArgsIn as st.data ∧ st.data.regs.SP.toNat % 16 = 0 ∧
          ∃ m', X sym' as m'))
      ⟨s, Labels.label sym⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (hcall s ra R hargs hra hsp (arm64_entry_mem hmem))
  rintro st (⟨hpc, ⟨hcs, hsp'⟩, rets, hrets, hm'⟩ |
    ⟨sym', as, hdef, hpc, has, hspE, _, _, _, _, _, _, m1, _, _, _, hX1, _⟩)
  · refine Or.inl ⟨hpc, fun r hr => ?_, ?_, rets, hrets, ?_⟩
    · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
      exact UInt64.toBitVec_inj.mp this
    · have : get st.data .SP = get s .SP := by simpa using hsp'
      exact UInt64.toBitVec_inj.mp this
    · simp only [Target.Exit, get_sp, Nat.add_zero] at hm'; exact hm'
  · obtain ⟨m2, _, _, _, hX2, _⟩ := hX1
    obtain ⟨m3, _, _, _, hX3, _⟩ := hX2
    exact Or.inr ⟨sym', as, hdef, hpc, has, hspE, m3, hX3⟩

/-- Translates `Arm64.target.Returns` into the concrete Kraken-AArch64 statement. -/
theorem arm64_of_returns [hh : Host] {sym : String} {b : Nat} {args : List Val}
    {P : Mem 64 → Prop} {Q : Post}
    (hret : target.Returns hh sym b args P Q)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : target.ArgsIn args s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ P ⋆
      (fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ rets, target.RetsIn rets st.data ∧
          (st.data.dmem =⋆ Q rets ⋆
            (fun f => ∃ bs : List UInt8, bs.length = b ∧
              f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (hret s ra R hargs hra hsp (arm64_entry_mem hmem))
  rintro st ⟨hpc, ⟨hcs, hsp'⟩, rets, hrets, hm'⟩
  refine ⟨hpc, fun r hr => ?_, ?_, rets, hrets, ?_⟩
  · have := hcs (.reg r) (by simp [calleeSaved] at hr ⊢; omega)
    exact UInt64.toBitVec_inj.mp this
  · have : get st.data .SP = get s .SP := by simpa using hsp'
    exact UInt64.toBitVec_inj.mp this
  · simp only [Target.Exit, get_sp, Nat.add_zero] at hm'; exact hm'

/-- Empty-heap specialization of `arm64_of_returns`. -/
theorem arm64_of_returns_emp [hh : Host] {sym : String} {b : Nat} {args : List Val}
    {Q' : List Val → Prop}
    (hret : target.Returns hh sym b args Std.ExtHashMap.emp
      (fun rets m' => Q' rets ∧ Std.ExtHashMap.emp m'))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : target.ArgsIn args s)
    (hra : s.regs.X30 = ra.toUInt64)
    (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        ∃ rets, target.RetsIn rets st.data ∧ Q' rets ∧
          (st.data.dmem =⋆
            (fun f => ∃ bs : List UInt8, bs.length = b ∧
              f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  have hmem' : s.dmem =⋆ Std.ExtHashMap.emp ⋆
      (fun f => ∃ bs : List UInt8, bs.length = b ∧
          f = bs.At (s.regs.SP.toBitVec - BitVec.ofNat 64 b)) ⋆ R := by
    rw [Std.ExtHashMap.emp_sep]; exact hmem
  refine eventually_weaken _ _ _ _ ?_ (arm64_of_returns hret s ra R hargs hra hsp hmem')
  rintro st ⟨hpc, hcs, hsp', rets, hrets, hm'⟩
  have hQ : Q' rets := by
    obtain ⟨_, _, _, _, ⟨_, _, _, _, ⟨hQ, _⟩, _⟩, _⟩ := hm'; exact hQ
  exact ⟨hpc, hcs, hsp', rets, hrets, hQ,
    sep_mono (fun x hf1 => (congrFun (Std.ExtHashMap.emp_sep _) x).mp
      (sep_mono (fun _ h => h.2) hf1)) hm'⟩

end LeanQbe.Arm64
