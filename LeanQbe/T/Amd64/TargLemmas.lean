module

public import LeanQbe.T.Amd64.Targ
public import LeanQbe.T.MainLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.IselLemmas5
import LeanQbe.T.Amd64.IselVecLemmas3
import LeanQbe.T.Amd64.FrameLemmas

/-!
# SysV x64 `LabelClean`, `TargetLayout`, `TargetInit`, & Concrete Lifting (`T12i`)

* `x64LabelClean : Rega.LabelClean x64Target.toIsa`: discharges compiler-side label uniqueness
  structurally via all verified `NoLab` theorems from `Amd64/{Isel,IselVec,Frame}Lemmas*`.
* `x64Layout : TargetLayout x64Target`: concrete `Host.ofLayout` using 4-byte uniform layout
  starting at `0x1000`.
* `x64Init : TargetInit x64Target 2048 8192`: concrete SysV ABI initial machine state across
  arbitrary legal argument signatures (`bool`, `bits`, and `128`-bit SIMD vectors) with stack
  below `sp0 = 0x0ff8#64`, `ra0 = 0x1234` at `0x0ff8#64`, and payload bytes at `0x1000#64`.
* `x64_of_call`, `x64_of_call_emp`, `x64_of_returns`, `x64_of_returns_emp`: project
  `x64Target.FnSpec` to concrete `Kraken.X64` `step1 Host.exe` postconditions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std Std.ExtHashMap
open LeanQbe.T

/-! ## 1. Structural `Rega.LabelClean x64Target.toIsa` -/

/-- No x64 instruction-selection or frame snippet ever emits a `.label` directive, and
`Kraken.Directive.label` is injective. -/
theorem x64LabelClean : Rega.LabelClean x64Target.toIsa where
  label_inj _ _ h := Kraken.Directive.label.inj h
  mov d s l := x64Gpr_mov_noLab d s l
  movi d bv l := x64Gpr_movi_noLab d bv l
  setcc d cc l := x64Gpr_setcc_noLab d cc l
  jmp tgt l := x64Gpr_jmp_noLab tgt l
  jcc cc tgt l := x64Gpr_jcc_noLab cc tgt l
  jnzGpr r tgt l := x64Gpr_jnzGpr_noLab r tgt l
  op _ _ _ _ _ _ h l := x64Gpr_op_noLab h l
  testOp _ _ _ _ _ _ _ h l := x64Gpr_testOp_noLab h l
  cmpMem _ _ _ _ _ _ _ h l := x64Gpr_cmpMem_noLab h l
  testMem _ _ _ _ _ _ _ h l := x64Gpr_testMem_noLab h l
  loadSext _ _ _ _ _ _ h l := x64Gpr_loadSext_noLab h l
  aluMem _ _ _ _ _ _ _ _ h l := x64Gpr_aluMem_noLab h l
  jnzMem _ _ _ _ _ h l := x64Gpr_jnzMem_noLab h l
  rmwMem _ _ _ _ _ _ h l := x64Gpr_rmwMem_noLab h l
  load _ _ _ _ _ h l := x64Gpr_load_noLab h l
  store _ _ _ _ _ h l := x64Gpr_store_noLab h l
  clearFlags l := x64Gpr_clearFlags_noLab l
  vmov w d s l := x64Vmov_noLab w d s l
  vmovi _ _ _ _ h l := x64Vmovi_noLab h l
  vslotSt w i s l := x64VslotSt_noLab w i s l
  vslotLd w d i l := x64VslotLd_noLab w d i l
  vop _ _ _ vh _ _ h l := x64Vop_noLab (vh := vh) h l
  vload _ _ _ _ _ h l := x64Vload_noLab h l
  vstore _ _ _ _ _ h l := x64Vstore_noLab h l
  prologue := x64Prologue_noLab
  epilogue := x64Epilogue_noLab
  slotSt := x64SlotSt_noLab
  slotLd := x64SlotLd_noLab
  canonAbi := x64CanonAbi_noLab
  call := x64Call_noLab
  exitJmp := x64ExitJmp_noLab
  ret := x64Ret_noLab

/-! ## 2. Concrete Kraken x64 `TargetLayout` -/

/-- Uniform x64 layout: 4 bytes per instruction, 0 bytes per label, base address `0x1000`. -/
@[expose, instance_reducible] def x64UniformLayout : Layout where
  start := 0x1000
  instrSize _ := 4
  instrSize_pos _ := by decide

/-- Size per x64 directive under `x64UniformLayout`. -/
@[expose, reducible] def x64DirSize : Directive → Nat
  | .instr _ => 4
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes

/-- Kernel-reducible check that laying out `p` under `x64UniformLayout` fits in `2 ^ 64` bytes. -/
@[expose] def x64ProgSmall (p : List Directive) : Bool :=
  decide ((p.map x64DirSize).sum < 2 ^ 64)

private theorem size_map_x64UniformLayout :
    ∀ (xs : List Directive) (k : Nat),
      ((xs.mapIdx fun i d =>
          ({ directive := d, size := x64UniformLayout.size d (k + i) } :
            Kraken.Sized Directive)).map (·.size)) =
        xs.map x64DirSize
  | [], _ => rfl
  | d :: xs, k => by
    rw [List.mapIdx_cons, List.map_cons, List.map_cons]
    have hd : x64UniformLayout.size d (k + 0) = x64DirSize d := by cases d <;> rfl
    have hrest :
        (xs.mapIdx fun i d' =>
          ({ directive := d', size := x64UniformLayout.size d' (k + (i + 1)) } :
            Kraken.Sized Directive)) =
        xs.mapIdx fun i d' =>
          ({ directive := d', size := x64UniformLayout.size d' ((k + 1) + i) } :
            Kraken.Sized Directive) := by
      congr 1; funext i d'; rw [show k + (i + 1) = (k + 1) + i from by omega]
    rw [hd, hrest, size_map_x64UniformLayout xs (k + 1)]

theorem x64UniformLayout_small (p : List Directive) (h : x64ProgSmall p = true) :
    (x64UniformLayout.apply p).sizeBefore p.length < 2 ^ 64 := by
  have hs : (x64UniformLayout.apply p).sizeBefore p.length = (p.map x64DirSize).sum := by
    simp only [Kraken.Executable.sizeBefore, Kraken.Layout.apply]
    rw [List.take_of_length_le (by simp)]
    simpa using congrArg List.sum (size_map_x64UniformLayout p 0)
  rw [hs]
  exact of_decide_eq_true h

@[expose] def x64LabelOf? : Directive → Option String
  | .label l => some l
  | _ => none

/-- Concrete x64 host layout (`Host.ofLayout` with `x64UniformLayout` and `labelsNodupBy`). -/
@[expose] def x64Layout : TargetLayout x64Target where
  labelsNodup := labelsNodupBy x64LabelOf?
  progSmall := x64ProgSmall
  layoutOf prog h := .ofLayout prog x64UniformLayout (x64UniformLayout_small prog h)
  prog_layoutOf _ _ := rfl
  labelsUnique_layoutOf {prog} h hnd :=
    letI : Host := .ofLayout prog x64UniformLayout (x64UniformLayout_small prog h)
    Host.labelsUnique_of_nodup (labelsNodupBy_nodup x64LabelOf? hnd)

/-! ## 3. Concrete Initial Machine State (`x64Init : TargetInit x64Target 2048 8192`) -/

/-- `n`-byte zero stack below `rsp = 0x0ff8`, return address `ra` at `0x0ff8`, and payload `bs`
at `0x1000`. -/
@[expose] def x64InitMem (n : Nat) (ra : Int64) (bs : List UInt8) : Mem 64 :=
  ((stackZeros n ++ Int.toBytes 8 ra.toBitVec.toInt) ++ bs).At (0x0ff8#64 - BitVec.ofNat 64 n)

theorem x64InitMem_entry (n : Nat) (ra : Int64) (bs : List UInt8)
    (hn : n ≤ 2048) (hbs : bs.length ≤ 8192) :
    x64InitMem n ra bs =⋆
      Eq (bs.At 0x1000#64) ⋆ x64Target.Entry 0x0ff8#64 ra n ⋆ Std.ExtHashMap.emp := by
  let raBytes : List UInt8 := Int.toBytes 8 ra.toBitVec.toInt
  have hra : raBytes.length = 8 := Int.toBytes_length 8 _
  have hzs : (stackZeros n).length = n := stackZeros_length n
  have hsp : (0x0ff8#64 - BitVec.ofNat 64 n) + BitVec.ofNat 64 n = 0x0ff8#64 :=
    BitVec.sub_add_cancel _ _
  have h1000 : (0x0ff8#64 : BitVec 64) + BitVec.ofNat 64 8 = 0x1000#64 := by decide
  have hlen1 : (stackZeros n).length + (raBytes ++ bs).length ≤ 2 ^ 64 := by
    rw [hzs, List.length_append, hra]
    exact Nat.le_trans (Nat.add_le_add hn (Nat.add_le_add_left hbs 8)) (by decide)
  have hlen2 : raBytes.length + bs.length ≤ 2 ^ 64 := by
    rw [hra]
    exact Nat.le_trans (Nat.add_le_add_left hbs 8) (by decide)
  have h1 : Eq ((stackZeros n ++ (raBytes ++ bs)).At (0x0ff8#64 - BitVec.ofNat 64 n)) =
      (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆
        Eq ((raBytes ++ bs).At 0x0ff8#64)) := by
    have e := Mem.At_append_sep (stackZeros n) (raBytes ++ bs) (0x0ff8#64 - BitVec.ofNat 64 n) hlen1
    rwa [hzs, hsp] at e
  have h2 : Eq ((raBytes ++ bs).At 0x0ff8#64) =
      (Eq (raBytes.At 0x0ff8#64) ⋆ Eq (bs.At 0x1000#64)) := by
    have e := Mem.At_append_sep raBytes bs 0x0ff8#64 hlen2
    rwa [hra, h1000] at e
  have hmem : (Eq (bs.At 0x1000#64) ⋆
      (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆ Eq (raBytes.At 0x0ff8#64)) ⋆
      Std.ExtHashMap.emp) (x64InitMem n ra bs) := by
    rw [Std.ExtHashMap.sep_emp]
    refine sep_cast (show Eq (x64InitMem n ra bs) (x64InitMem n ra bs) from rfl) ?_
    change Eq ((stackZeros n ++ raBytes ++ bs).At (0x0ff8#64 - BitVec.ofNat 64 n)) = _
    rw [List.append_assoc, h1, h2]
    ac_rfl
  have hsub : ∀ m, (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆
      Eq (raBytes.At 0x0ff8#64)) m → x64Target.Entry 0x0ff8#64 ra n m := by
    intro m hm
    dsimp only [Target.Entry, x64Target, x64FrameTarget, x64FramePreds]
    exact sep_mono (fun _ hm' => ⟨stackZeros n, hzs, hm'.symm⟩) hm
  exact sep_mono_mid hsub hmem

/-- Encode typed ABI scalar argument value into a 64-bit register word. -/
@[expose] def valToGpr : (t : Ty) → Val t → BitVec 64
  | .bool, b => BitVec.ofNat 64 b.toNat
  | .bits _, v => v.setWidth 64
  | _, _ => 0

/-- Populate SysV x64 GPR and vector argument registers with `rsp = 0x0ff8`. -/
@[expose] def setX64AbiRegs :
    {ts : List Ty} → Tup (AbiReg Reg64 RegMm) ts → Tup Val ts → Reg64s × RegZmms
  | [], _, _ => ({ rsp := 0x0ff8 }, {})
  | t :: _, (loc, locs), (v, vs) =>
    let p := setX64AbiRegs locs vs
    match loc with
    | .gpr r => (p.1.set64 r (valToGpr t v), p.2)
    | .vec vr => (p.1, p.2.set512 vr ((toBits t v).setWidth 512))

private theorem x64AbiVec_size_le_512 {a b : Ty} (h : x64Vec.isAbiVec (.pair a b) = true) :
    (Ty.pair a b).size ≤ 512 := by
  simp only [x64IsAbiVec, Bool.and_eq_true, beq_iff_eq] at h
  omega

private theorem x64SetWidth_512_cancel {n : Nat} (hn : n ≤ 512) (x : BitVec n) :
    (x.setWidth 512).setWidth n = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [show (i : Nat) < 512 by omega, hi]

private theorem x64AssignSig_cons {t : Ty} {ts : List Ty} {loc : AbiReg Reg64 RegMm t}
    {locs : Tup (AbiReg Reg64 RegMm) ts} {gs : List Reg64} {vs : List RegMm}
    (h : x64Target.toIsa.assignSig (t :: ts) gs vs = some (loc, locs)) :
    match loc with
    | .gpr r => ∃ gs', gs = r :: gs' ∧ x64Target.toIsa.assignSig ts gs' vs = some locs ∧
        (t = .bool ∨ ∃ n, t = .bits n ∧ n ≤ 64)
    | .vec vr => ∃ vs' a b, t = .pair a b ∧ vs = vr :: vs' ∧
        x64Target.toIsa.assignSig ts gs vs' = some locs ∧ (Ty.pair a b).size ≤ 512 := by
  cases t with
  | bool =>
    cases gs with
    | nil => simp [Isa.assignSig] at h
    | cons r0 gs' =>
      simp only [Isa.assignSig, Option.map_eq_some_iff] at h
      obtain ⟨locs', h', hloc⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
      exact ⟨gs', rfl, h', Or.inl rfl⟩
  | bits n =>
    cases gs with
    | nil => simp [Isa.assignSig] at h
    | cons r0 gs' =>
      simp only [Isa.assignSig] at h
      cases hbw : [8, 16, 32, 64].contains n
      · simp only [hbw, Bool.false_eq_true, ↓reduceIte] at h; cases h
      · simp only [hbw, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨locs', h', hloc⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
        have hle : n ≤ 64 := by
          simp only [List.contains_eq_mem, List.mem_cons,
            List.not_mem_nil, or_false, decide_eq_true_eq] at hbw
          rcases hbw with rfl | rfl | rfl | rfl <;> decide
        exact ⟨gs', rfl, h', Or.inr ⟨n, rfl, hle⟩⟩
  | float _ => simp [Isa.assignSig] at h
  | pair a b =>
    cases vs with
    | nil => simp [Isa.assignSig] at h
    | cons vr0 vs' =>
      dsimp only [Isa.assignSig] at h
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨locs', h', hloc⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
        exact ⟨vs', a, b, rfl, rfl, h', x64AbiVec_size_le_512 ‹_›⟩
      · cases h

private theorem setX64AbiRegs_get_rsp :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg64 RegMm) ts} {args : Tup Val ts}
      {gs : List Reg64} {vs : List RegMm},
      .rsp ∉ gs → x64Target.toIsa.assignSig ts gs vs = some locs →
      (setX64AbiRegs locs args).1.get64 .rsp = 0x0ff8#64
  | [], (), (), _, _, _, _ => rfl
  | t :: ts, (loc, locs), (v, vs), gs, vs', hrsp, h => by
    have hc := x64AssignSig_cons h
    cases loc with
    | gpr r =>
      obtain ⟨gs', rfl, h', _⟩ := hc
      have hne : r ≠ .rsp := fun e => hrsp (e ▸ List.mem_cons_self)
      dsimp only [setX64AbiRegs]
      rw [Reg64s.get64_set64_of_ne _ _ _ _ hne]
      exact setX64AbiRegs_get_rsp (fun hm => hrsp (List.mem_cons_of_mem _ hm)) h'
    | vec vr =>
      obtain ⟨vs'', _, _, rfl, rfl, h', _⟩ := hc
      dsimp only [setX64AbiRegs]
      exact setX64AbiRegs_get_rsp hrsp h'

private theorem x64Abi_frame {g g' : Reg64s} {vf vf' : RegZmms} :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg64 RegMm) ts} {args : Tup Val ts}
      {gs : List Reg64} {vs : List RegMm},
      (∀ r ∈ gs, g'.get64 r = g.get64 r) → (∀ vr ∈ vs, vf'.get512 vr = vf.get512 vr) →
      x64Target.toIsa.assignSig ts gs vs = some locs →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds (g.get64 r) t val
        | .vec vr => VecHolds (vf.get512 vr) t val) locs args →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds (g'.get64 r) t val
        | .vec vr => VecHolds (vf'.get512 vr) t val) locs args
  | [], (), (), _, _, _, _, _, _ => .nil
  | _ :: _, (loc, _), (_, _), _, _, hg, hv, h, hrel => by
    cases hrel with
    | cons h1 h2 =>
      have hc := x64AssignSig_cons h
      cases loc with
      | gpr r =>
        obtain ⟨_, rfl, h', _⟩ := hc
        exact .cons (by simpa [hg r List.mem_cons_self] using h1)
          (x64Abi_frame (fun x hm => hg x (List.mem_cons_of_mem _ hm)) hv h' h2)
      | vec vr =>
        obtain ⟨_, _, _, rfl, rfl, h', _⟩ := hc
        exact .cons (by simpa [hv vr List.mem_cons_self] using h1)
          (x64Abi_frame hg (fun x hm => hv x (List.mem_cons_of_mem _ hm)) h' h2)

private theorem setX64AbiRegs_holds :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg64 RegMm) ts} {args : Tup Val ts}
      {gs : List Reg64} {vs : List RegMm},
      gs.Nodup → vs.Nodup → x64Target.toIsa.assignSig ts gs vs = some locs →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds ((setX64AbiRegs locs args).1.get64 r) t val
        | .vec vr => VecHolds ((setX64AbiRegs locs args).2.get512 vr) t val) locs args
  | [], (), (), _, _, _, _, _ => .nil
  | t :: ts, (loc, locs), (v, vs), gs, vs', hgs, hvs, h => by
    have hc := x64AssignSig_cons h
    cases loc with
    | gpr r =>
      obtain ⟨gs', rfl, h', hty⟩ := hc
      obtain ⟨hnmem, hgs'⟩ := List.nodup_cons.mp hgs
      have hhead :
          AbiGprHolds
            ((setX64AbiRegs (ts := t :: ts) (AbiReg.gpr r, locs) (v, vs)).1.get64 r) t v := by
        rcases hty with rfl | ⟨n, rfl, hn⟩
        · dsimp only [setX64AbiRegs, valToGpr, AbiGprHolds]
          simp
        · dsimp only [setX64AbiRegs, valToGpr, AbiGprHolds]
          simp [hn]
      refine .cons hhead (x64Abi_frame ?_ (fun _ _ => rfl) h' (setX64AbiRegs_holds hgs' hvs h'))
      intro x hx
      dsimp only [setX64AbiRegs]
      exact Reg64s.get64_set64_of_ne _ _ _ _ (fun e => hnmem (e ▸ hx))
    | vec vr =>
      obtain ⟨vs'', a, b, rfl, rfl, h', hsz⟩ := hc
      obtain ⟨hnmem, hvs'⟩ := List.nodup_cons.mp hvs
      have hhead :
          VecHolds
            ((setX64AbiRegs (ts := .pair a b :: ts)
              (AbiReg.vec vr, locs) (v, vs)).2.get512 vr)
            (.pair a b) v := by
        dsimp only [setX64AbiRegs, VecHolds]
        simp only [RegZmms.get512_set512_same, hsz, true_and]
        exact x64SetWidth_512_cancel hsz (toBits (.pair a b) v)
      refine .cons hhead (x64Abi_frame (fun _ _ => rfl) ?_ h' (setX64AbiRegs_holds hgs hvs' h'))
      intro x hx
      dsimp only [setX64AbiRegs]
      exact RegZmms.get512_set512_of_ne _ (fun (e : vr = x) => hnmem (e ▸ hx)) _

/-- Concrete initial `MachineData` with `n`-byte stack, return address `0x1234` at `0x0ff8#64`,
payload `bs` at `0x1000#64`, and SysV ABI argument registers populated from `args`. -/
@[expose] def x64InitState (n : Nat) (bs : List UInt8) {as : List Ty} (args : Tup Val as) :
    MachineData :=
  let rv :=
    match x64Target.toIsa.assignArgs as with
    | some locs => setX64AbiRegs locs args
    | none => ({ rsp := 0x0ff8 }, {})
  { regs := rv.1, zmms := rv.2, dmem := x64InitMem n 0x1234 bs }

private theorem trel_x64_imp {P Q : ∀ t, AbiReg Reg64 RegMm t → Val t → Prop}
    (h : ∀ t a v, P t a v → Q t a v) :
    ∀ {ts : List Ty} {xs : Tup (AbiReg Reg64 RegMm) ts} {ys : Tup Val ts},
      TRel P xs ys → TRel Q xs ys
  | [], _, _, .nil => .nil
  | _ :: _, _, _, .cons hx hxs => .cons (h _ _ _ hx) (trel_x64_imp h hxs)

/-- Closed concrete execution harness for `x64Target` (`sp0 = 0x0ff8#64`, `ra0 = 0x1234`). -/
@[expose] def x64Init : TargetInit x64Target 2048 8192 where
  sp0 := 0x0ff8#64
  ra0 := 0x1234
  ret0 := .rax
  arg0 := .rdi
  initState := x64InitState
  get_sp := fun n bs {as} args => by
    dsimp only [x64Target, x64Mach, x64InitState]
    cases h : x64Target.toIsa.assignArgs as with
    | none => rfl
    | some locs =>
      exact setX64AbiRegs_get_rsp (by simp) h
  argsIn := fun n bs {as} args his => by
    obtain ⟨locs, hlocs⟩ := Option.isSome_iff_exists.mp his
    refine ⟨locs, hlocs, ?_⟩
    dsimp only [x64InitState]; rw [hlocs]; dsimp only
    exact trel_x64_imp (fun t loc v h => by cases loc <;> exact h)
      (setX64AbiRegs_holds (by simp) (by simp) hlocs)
  raReg _ _ := by intros; trivial
  spEntry := by dsimp only [x64Target, x64FrameTarget, x64FramePreds]; decide
  mem_entry n bs {_} _ hn hbs := x64InitMem_entry n 0x1234 bs hn hbs
  retsIn_singleton v s h := by
    obtain ⟨locs, hlocs, hrel⟩ := h
    change some (AbiReg.gpr .rax, ()) = some locs at hlocs
    injection hlocs with hlocs; subst hlocs
    cases hrel with
    | cons h1 _ => exact h1.2.trans (by simp)
  argsIn_singleton v s h := by
    obtain ⟨locs, hlocs, hrel⟩ := h
    change some (AbiReg.gpr .rdi, ()) = some locs at hlocs
    injection hlocs with hlocs; subst hlocs
    cases hrel with
    | cons h1 _ => exact h1.2.trans (by simp)

/-! ## 4. Concrete Kraken-x64 Lifting Lemmas (`x64_of_*`) -/

/-- Translates `x64Target.FnSpec` into the concrete Kraken-x64 `step1 Host.exe` statement. -/
theorem x64_of_call [hh : Host] {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : x64Target.FnSpec hh sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost} (hspec : spec args m Q X)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : x64Target.ArgsIn args s)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
            st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
          ∃ rets m', Q rets m' ∧ x64Target.RetsIn rets st.data ∧
            (st.data.dmem =⋆ Eq m' ⋆
              region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R)) ∨
        (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
          X sym' cs xs m' ∧ x64Target.Defined hh sym' ∧ st.pc = Labels.label sym' ∧
          x64Target.ArgsIn xs st.data ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧
          ∃ (ra' : Int64) (n' : Nat) (F : Mem 64 → Prop), nX ≤ n' ∧
            (st.data.dmem =⋆ Eq m' ⋆
              x64Target.Entry (st.data.regs.get64 .rsp) ra' n' ⋆ F ⋆ R)))
      ⟨s, Labels.label sym⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (hfn args m Q X hspec s ra R hargs trivial hsp hmem)
  rintro st (⟨hpc, rets, m', hQ, hrets, ⟨hcs, hsp'⟩, hm'⟩ |
    ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE, ra', n', F, hnX, _, _, hm'⟩)
  · exact Or.inl ⟨hpc, fun r hr => hcs r hr, hsp', rets, m', hQ, hrets, hm'⟩
  · exact Or.inr ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE, ra', n', F, hnX, hm'⟩

/-- Simplified `x64_of_call` erasing exit stack/frame details down to `∃ m', X sym' cs xs m'`. -/
theorem x64_of_call_emp [hh : Host] {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : x64Target.FnSpec hh sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost} (hspec : spec args m Q X)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : x64Target.ArgsIn args s)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st =>
        (st.pc = ra ∧
          (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
            st.data.regs.get64 r = s.regs.get64 r) ∧
          st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
          ∃ rets m', Q rets m' ∧ x64Target.RetsIn rets st.data ∧
            (st.data.dmem =⋆ Eq m' ⋆
              region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R)) ∨
        (∃ (sym' : Sym) (cs : List Ty) (xs : Tup Val cs) (m' : Mem 64),
          X sym' cs xs m' ∧ x64Target.Defined hh sym' ∧ st.pc = Labels.label sym' ∧
          x64Target.ArgsIn xs st.data ∧
          (st.data.regs.get64 .rsp + 8#64).toNat % 16 = 0))
      ⟨s, Labels.label sym⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (x64_of_call hfn hspec s ra R hargs hsp hmem)
  rintro st (hret | ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE, _⟩)
  · exact Or.inl hret
  · exact Or.inr ⟨sym', cs, xs, m', hX, hdef, hpc, has, hspE⟩

/-- Non-exiting specialization of `x64_of_call` (`X = fun _ _ _ _ => False`). -/
theorem x64_of_returns [hh : Host] {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : x64Target.FnSpec hh sym spec b nX)
    {args : Tup Val as} {m : Mem 64} {Q : Post bs}
    (hspec : spec args m Q (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : x64Target.ArgsIn args s)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ Eq m ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ rets m', Q rets m' ∧ x64Target.RetsIn rets st.data ∧
          (st.data.dmem =⋆ Eq m' ⋆
            region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  refine eventually_weaken _ _ _ _ ?_ (x64_of_call hfn hspec s ra R hargs hsp hmem)
  rintro st (hret | ⟨_, _, _, _, hX, _⟩)
  · exact hret
  · exact hX.elim

/-- Empty-heap specialization of `x64_of_returns`. -/
theorem x64_of_returns_emp [hh : Host] {sym : Sym} {b nX : Nat} {as bs : List Ty}
    {spec : Spec as bs} (hfn : x64Target.FnSpec hh sym spec b nX)
    {args : Tup Val as} {Q' : Tup Val bs → Prop}
    (hspec : spec args ∅ (fun rets m' => Q' rets ∧ Std.ExtHashMap.emp m')
      (fun _ _ _ _ => False))
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hargs : x64Target.ArgsIn args s)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        ∃ rets, x64Target.RetsIn rets st.data ∧ Q' rets ∧
          (st.data.dmem =⋆
            region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))
      ⟨s, Labels.label sym⟩ := by
  have hmem' : s.dmem =⋆ Eq (∅ : Mem 64) ⋆
      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R := by
    rw [eq_empty_eq_emp, Std.ExtHashMap.emp_sep]; exact hmem
  refine eventually_weaken _ _ _ _ ?_ (x64_of_returns hfn hspec s ra R hargs hsp hmem')
  rintro st ⟨hpc, hcs, hsp', rets, m', ⟨hQ, hm0⟩, hrets, hm'⟩
  rw [← eq_empty_eq_emp] at hm0
  subst hm0
  rw [eq_empty_eq_emp, Std.ExtHashMap.emp_sep] at hm'
  exact ⟨hpc, hcs, hsp', rets, hrets, hQ, hm'⟩

end LeanQbe.T.Amd64
