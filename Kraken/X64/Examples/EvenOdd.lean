module

import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken
import all Kraken.Separation
import all Kraken.Mem

public meta import Lean

local instance : Coe Label RelRegOrMem where
  coe l := .rel (.sub (.label l) .after_current_instruction)

macro addr:term " ↦ " val:term : term => `(Eq (UInt64.At $val $addr))


def even : Program := ⸨prog|
even:
  test %rdi, %rdi
  jz even_zero
  dec %rdi
  call odd
  ret
even_zero:
  mov $1, %rax
  ret
⸩

def odd : Program := ⸨prog|
odd:
  test %rdi, %rdi
  jz odd_zero
  dec %rdi
  call even
  ret
odd_zero:
  mov $0, %rax
  ret
⸩

-- section testing

-- variable [layout : Kraken.Layout (even ++ odd)]

-- set_option maxHeartbeats 4000000 in
-- set_option trace.profiler true in
-- example :
--   letI := layout.take even
--   (even ++ odd).toExecutable.addrOf 3 = even.toExecutable.addrOf 3 := by
--     dsimp [List.toExecutable, Kraken.Layout.take, Kraken.Executable.addrOf, Kraken.Layout.apply,
--       Kraken.Layout.start, Kraken.Layout.instrSize]
--     refine congrArg (fun x => layout.start + Int64.ofNat x) ?_
--     dsimp [Kraken.Executable.sizeBefore]
--     rfl

-- example :
--   letI := layout.drop even
--   (even ++ odd).toExecutable.addrOf 3 = odd.toExecutable.addrOf 3 := by
--     rfl -- FAILS!

-- end testing

def body (succLabel zeroLabel otherLabel: Label) (ret : Int64) : Program := ⸨prog|
❰.label succLabel❱
  test %rdi, %rdi
  jz ❰zeroLabel❱
  dec %rdi
  call ❰otherLabel❱
  ret
❰.label zeroLabel❱
  mov ❰ret❱, %rax
  ret
⸩

theorem even_body : even = body "even" "even_zero" "odd" 1:= rfl

theorem odd_body : odd = body "odd" "odd_zero" "even" 0 := rfl

open Kraken (WellFormedLayout Layout)
open Labels (label!)
open Std.ExtHashMap

section DelabStructureWith
open Lean Meta PrettyPrinter Delaborator SubExpr

public meta section

private def extractStructBase? (env : Environment) (structName : Name) (numParams : Nat)
    (fieldName : Name) (idx : Nat) (arg : Expr) : Option Expr := do
  let info ← Lean.getFieldInfo? env structName fieldName
  if arg.isAppOfArity info.projFn (numParams + 1) then
    return arg.appArg!
  else if let .proj s i base := arg then
    if s == structName && i == idx then
      return base
  failure

/-- Delaborate structure constructors whose fields predominantly project from a common base
    expression `base` using `{ base with ... }` notation. -/
@[delab app]
def delabStructureWith : Delab := do
  let env ← getEnv
  let e ← getExpr
  let some s ← isConstructorApp? e | failure
  guard <| isStructure env s.induct
  guard <| ← getPPOption getPPStructureInstances
  guard <| !(← read).inPattern
  let fieldNames := getStructureFields env s.induct
  let args := e.getAppArgs
  guard <| args.size == s.numParams + fieldNames.size
  let mut counts : Array (Expr × Nat × Nat) := #[]
  for i in [:fieldNames.size] do
    let arg := args[s.numParams + i]!
    if let some base := extractStructBase? env s.induct s.numParams fieldNames[i]! i arg then
      if let some idx := counts.findIdx? (fun (b, _, _) => b == base) then
        let (b, c, firstIdx) := counts[idx]!
        counts := counts.set! idx (b, c + 1, firstIdx)
      else
        counts := counts.push (base, 1, i)
  let some (bestBase, bestCount, bestIdx) :=
    counts.foldl (fun acc cur =>
      match acc with
      | none => some cur
      | some (_, c, _) => if cur.2.1 > c then some cur else acc) none
    | failure
  guard <| bestCount ≥ 2
  let baseStx ← withNaryArg (s.numParams + bestIdx) do
    if (← getExpr).isProj then
      withProj delab
    else
      withAppArg delab
  let mut fields : Array (TSyntax ``Parser.Term.structInstField) := #[]
  for i in [:fieldNames.size] do
    let arg := args[s.numParams + i]!
    let matchesBase := match extractStructBase? env s.induct s.numParams fieldNames[i]! i arg with
      | some b => b == bestBase
      | none => false
    if !matchesBase then
      let fieldName := fieldNames[i]!
      let some fieldInfo := Lean.getFieldInfo? env s.induct fieldName | failure
      let value ← withNaryArg (s.numParams + i) delab
      let fieldPos ← nextExtraPos
      let fieldId : Ident := ⟨annotatePos fieldPos (mkIdent fieldName)⟩
      addFieldInfo fieldPos fieldInfo.projFn fieldName fieldId arg
      let lctx ← getLCtx
      let isSameVar : Bool := match arg with
        | .fvar fvarId =>
          match lctx.find? fvarId with
          | some d =>
            value.raw.isIdent && value.raw.getId == fieldName &&
            !d.userName.hasMacroScopes && d.userName == fieldName
          | none => false
        | _ => false
      let fieldStx ←
        if isSameVar then
          `(Parser.Term.structInstField| $fieldId:ident)
        else
          `(Parser.Term.structInstField| $fieldId:ident := $value)
      fields := fields.push fieldStx
  if fields.isEmpty then
    return baseStx
  `({ $baseStx with $fields,* })

end
end DelabStructureWith

attribute [local kstep] RelRegOrMem.interp


theorem body.spec
  (succLabel zeroLabel otherLabel: Label) (ret : Int64)
  [layout : WellFormedLayout (body succLabel zeroLabel otherLabel ret)]
  (st : MachineData)
  (n : UInt64)
  (hd : st.regs.rdi = n) :
    letI e : Executable := (body succLabel zeroLabel otherLabel ret).toExecutable
    letI := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ => ∃ status,
        match n.toNat with
        | 0 =>  st' = {st with
            regs.rax := ret.toUInt64
            status
          } ∧
          pc = e.addrOf 8
        | n' + 1 => st' = {st with
            regs.rdi := UInt64.ofNat n'
            status
          } ∧
          pc = e.addrOf 4
      )
      ⟨st, label! succLabel⟩ := by
  let e : Executable := (body succLabel zeroLabel otherLabel ret).toExecutable
  let labels := Executable.labels e
  have addrOf_0 : label! succLabel = e.addrOf 0 := by
    rw [Labels.label!_of_label? (label?_eq_some_addrOf (p := body succLabel zeroLabel otherLabel ret)
      (lbl := succLabel) (k := 0) (by simp [body, List.findIdx?_cons]))]
  rw [addrOf_0]
  change (Eventually (step1 (Kraken.Layout.apply (body succLabel zeroLabel otherLabel ret) _)) _
    ⟨st, e.addrOf 0⟩)
  dsimp at *
  sym => kstep; tactic =>
  rename_i v _
  if h : v = 0#64 then
    simp [h]
    simp [Effects.All]
    have : label? zeroLabel = some (e.addrOf 6) := by
      have hne : succLabel ≠ zeroLabel := by
        simpa [body, Kraken.Program.labels] using layout.unique_labels
      exact label?_eq_some_addrOf (p := body succLabel zeroLabel otherLabel ret)
        (by simp [body, List.findIdx?_cons, hne])
    rw [this]
    dsimp
    sym => kstep 1; tactic =>
    apply Eventually.done
    simp
    have : n.toNat = 0 := by grind
    rw [this]
    dsimp
    simp
  else
    simp [h]
    simp [Effects.All]
    sym => kstep 1; tactic =>
    apply Eventually.done
    have ⟨_, this⟩ : ∃ n', n.toNat = n' + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by grind)
    rw [this]
    simp
    grind

private theorem addrOf_take_le {p₁ p₂ : Program} [l : Layout (p₁ ++ p₂)] {k : Nat} (hk : k ≤ p₁.length) :
    letI := l.take p₁
    (p₁ ++ p₂).toExecutable.addrOf k = p₁.toExecutable.addrOf k := by
  letI := l.take p₁
  simp only [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore, Kraken.Layout.apply,
    List.mapIdx_append]
  rw [List.take_append_of_le_length (by simpa using hk)]
  congr 3
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < min k p₁.length
  · have hi₁ : i < p₁.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hik : i < k := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    simp [List.getElem?_map, List.getElem?_mapIdx,
      List.getElem?_eq_getElem hi₁, hik, Kraken.Layout.size_take p₁ hi₁]
  · by_cases hik : i < k
    · have hi₁ : p₁.length ≤ i := by omega
      simp [List.getElem?_map, List.getElem?_mapIdx, hik, List.getElem?_eq_none hi₁]
    · simp [List.getElem?_take, hik]

private theorem addrOf_drop {p₁ p₂ : Program} [l : Layout (p₁ ++ p₂)] (k : Nat) :
    letI := l.drop p₁
    (p₁ ++ p₂).toExecutable.addrOf (k + p₁.length) = p₂.toExecutable.addrOf k := by
  letI := l.drop p₁
  simp only [Kraken.Executable.addrOf]
  have hdrop : (((p₁ ++ p₂).toExecutable.program.drop p₁.length).take k).map (·.size) =
      (p₂.toExecutable.program.take k).map (·.size) := by
    simp only [Kraken.Layout.apply, List.mapIdx_append,
      List.drop_left' (by simp : (p₁.mapIdx _).length = p₁.length), List.map_take]
    congr 1
    refine List.ext_getElem? fun i => ?_
    by_cases hi : i < p₂.length
    · simp [List.getElem?_map, List.getElem?_mapIdx, List.getElem?_eq_getElem hi,
        Kraken.Layout.size_drop]
    · simp [List.getElem?_map, List.getElem?_mapIdx, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
  have hpre : (((p₁ ++ p₂).toExecutable.program.take p₁.length).map (·.size)).sum =
      (p₁.mapIdx fun i _ => l.size i).sum := by
    simp only [Kraken.Layout.apply, List.mapIdx_append,
      List.take_left' (by simp : (p₁.mapIdx _).length = p₁.length)]
    congr 1
    refine List.ext_getElem? fun i => ?_
    by_cases hi : i < p₁.length
    · simp [List.getElem?_map, List.getElem?_mapIdx, List.getElem?_eq_getElem hi]
    · simp [List.getElem?_map, List.getElem?_mapIdx, List.getElem?_eq_none (Nat.le_of_not_lt hi)]
  rw [Nat.add_comm k p₁.length, Kraken.Executable.sizeBefore_add, Kraken.Executable.sizeBefore,
    Kraken.Executable.sizeBefore, hpre, hdrop]
  change l.start + .ofNat (_ + _) = (l.start + .ofNat _) + .ofNat _
  grind

private theorem Int64.ofBitVec_ofBytes_toBytes (x : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 x.toInt))) = x := by
  apply Int64.toBitVec.inj
  rw [ofBytes_toBytes, Int.take, show 8 * 8 = 64 from rfl, Int64.toInt,
    Int64.toBitVec_ofBitVec]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toInt_eq_toNat_cond]
  split <;> omega

private theorem step_ret (e_prog : Program) [layout : WellFormedLayout e_prog]
    {k : Nat} (hk : e_prog[k]? = some (.instr (.regular .W64 .W64 .ret)))
    (st : MachineData) (ra : Int64) (R : DataMem → Prop)
    (h_mem : st.dmem =⋆ (st.regs.rsp ↦ ra.toUInt64) ⋆ R)
    (post : MachineState → Prop)
    (h_post : post ⟨{ st with regs := { st.regs with rsp := st.regs.rsp + 8 } }, ra⟩) :
    Eventually (step1 e_prog.toExecutable) post ⟨st, e_prog.toExecutable.addrOf k⟩ := by
  refine step_at hk ?_
  have hload := Mem.loadInt_sep (Int.toBytes 8 ra.toInt) st.regs.rsp.toBitVec 8 R st.dmem
    h_mem (Int.toBytes_length 8 _) (by decide)
  dsimp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load,
    require_access, require_read_access, Effects.All, Reg64s.get64, Reg64s.set64]
  split
  · simp only [Effects.All]
    rw [hload]
    dsimp only [Effects.All]
    rw [Int64.ofBitVec_ofBytes_toBytes]
    exact .done _ h_post
  · simp only [Effects.All]
    rw [hload]
    dsimp only [Effects.All]
    rw [Int64.ofBitVec_ofBytes_toBytes]
    exact .done _ h_post

private theorem step_call (e_prog : Program) [layout : WellFormedLayout e_prog]
    {k : Nat} {tgt : Label}
    (hk : e_prog[k]? = some (.instr (.regular .W64 .W64 (.call (.rel (.sub (.label tgt) .after_current_instruction))))))
    (st : MachineData) (tgt_addr : Int64)
    (htgt : @Labels.label? (Executable.labels e_prog.toExecutable) tgt = some tgt_addr)
    (old : List UInt8) (h_len : old.length = 8) (R : DataMem → Prop)
    (h_mem : st.dmem =⋆ Eq (old.At (st.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (post : MachineState → Prop)
    (h_post : post ⟨{ st with
        regs := { st.regs with rsp := st.regs.rsp - 8 },
        dmem := st.dmem.storeInt (st.regs.rsp.toBitVec - 8#64) 8 (e_prog.toExecutable.addrOf (k + 1)).toInt },
      tgt_addr⟩) :
    Eventually (step1 e_prog.toExecutable) post ⟨st, e_prog.toExecutable.addrOf k⟩ := by
  letI := Executable.labels e_prog.toExecutable
  refine step_at hk ?_
  have h_load := Mem.loadInt_sep old (st.regs.rsp.toBitVec - 8#64) 8 R st.dmem h_mem h_len (by decide)
  dsimp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, require_access, require_write_access, Effects.All,
    Reg64s.get64, Reg64s.set64, Width.bytes, Width.bytesv, Width.bits]
  rw [Effects.All_resolve_label, htgt]
  dsimp only
  try simp only [Int64.add_sub_cancel_left]
  rw [h_load]
  dsimp only
  by_cases h_wrap : ↑(st.regs.rsp.toBitVec - 8#64).toFin.castSucc + (UInt64.ofNat 8).toNat ≤ UInt64.size
  · simp only [dite_eq_left h_wrap, Effects.All]; exact .done _ h_post
  · simp only [dite_eq_right h_wrap, Effects.All]; exact .done _ h_post

private theorem stack_split_sep (s₁ s₂ : List UInt8) (rsp : BitVec 64) (k : Nat) (R : DataMem → Prop)
    (hbound : s₁.length + s₂.length ≤ 2 ^ 64) (hs₁ : s₁.length = 8 * k) :
    (Eq ((s₁ ++ s₂).At (rsp - BitVec.ofNat 64 (8 * (k + 1)))) ⋆ R) =
    (Eq (s₂.At (rsp - 8#64)) ⋆ (Eq (s₁.At ((rsp - 8#64) - BitVec.ofNat 64 (8 * k))) ⋆ R)) := by
  rw [Mem.At_append_sep (w := 64) s₁ s₂ _ hbound]
  have h_ofNat : BitVec.ofNat 64 (8 * (k + 1)) = BitVec.ofNat 64 (8 * k) + 8#64 := by
    rw [Nat.mul_succ, BitVec.ofNat_add]
  have h_addr1 : rsp - BitVec.ofNat 64 (8 * (k + 1)) + BitVec.ofNat 64 s₁.length = rsp - 8#64 := by
    rw [hs₁, h_ofNat]
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add]
    rw [show rsp + (-BitVec.ofNat 64 (8 * k) + -8#64) + BitVec.ofNat 64 (8 * k) =
      rsp + -8#64 + (BitVec.ofNat 64 (8 * k) + -BitVec.ofNat 64 (8 * k)) by ac_rfl]
    simp only [← BitVec.sub_eq_add_neg, BitVec.sub_self, BitVec.add_zero]
  have h_addr2 : rsp - BitVec.ofNat 64 (8 * (k + 1)) = (rsp - 8#64) - BitVec.ofNat 64 (8 * k) := by
    rw [h_ofNat]; simp only [BitVec.sub_eq_add_neg, BitVec.neg_add]; ac_rfl
  rw [h_addr1, h_addr2]
  ac_rfl

private theorem even_body.spec [layout : WellFormedLayout (even ++ odd)]
    (st : MachineData) (n : UInt64) (hd : st.regs.rdi = n) :
    letI e : Executable := (even ++ odd).toExecutable
    letI := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ => ∃ status,
        match n.toNat with
        | 0 => st' = { st with regs.rax := 1, status } ∧ pc = e.addrOf 8
        | n' + 1 => st' = { st with regs.rdi := UInt64.ofNat n', status } ∧ pc = e.addrOf 4)
      ⟨st, label! "even"⟩ := by
  letI e : Executable := (even ++ odd).toExecutable
  letI := e.labels
  letI l_even := layout.take even
  have h_spec := body.spec "even" "even_zero" "odd" 1 (layout := even_body ▸ l_even) st n hd
  simp only [← even_body] at h_spec
  have h_lbl_eq : @Labels.label! e.labels "even" =
      @Labels.label! (Executable.labels even.toExecutable) "even" := by
    rw [Labels.label!_of_label? (label?_eq_some_addrOf (p := even ++ odd) (k := 0) (by simp [even, List.findIdx?_cons])),
        Labels.label!_of_label? (label?_eq_some_addrOf (p := even) (k := 0) (by simp [even, List.findIdx?_cons])),
        addrOf_take_le (by decide)]
    rfl
  rw [h_lbl_eq]
  refine eventually_weaken _ _ _ _ ?_ (Eventually.append_left even odd _ _ h_spec)
  rintro ⟨st', pc⟩ ⟨status, hs⟩
  refine ⟨status, ?_⟩
  cases hn : n.toNat with
  | zero =>
    simp only [hn] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨rfl, (addrOf_take_le (by decide)).symm⟩
  | succ n' =>
    simp only [hn] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨rfl, (addrOf_take_le (by decide)).symm⟩

private theorem odd_body.spec [layout : WellFormedLayout (even ++ odd)]
    (st : MachineData) (n : UInt64) (hd : st.regs.rdi = n) :
    letI e : Executable := (even ++ odd).toExecutable
    letI := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ => ∃ status,
        match n.toNat with
        | 0 => st' = { st with regs.rax := 0, status } ∧ pc = e.addrOf (8 + even.length)
        | n' + 1 => st' = { st with regs.rdi := UInt64.ofNat n', status } ∧ pc = e.addrOf (4 + even.length))
      ⟨st, label! "odd"⟩ := by
  letI e : Executable := (even ++ odd).toExecutable
  letI := e.labels
  letI l_odd := layout.drop even
  have h_spec := body.spec "odd" "odd_zero" "even" 0 (layout := odd_body ▸ l_odd) st n hd
  simp only [← odd_body] at h_spec
  have h_lbl_eq : @Labels.label! e.labels "odd" =
      @Labels.label! (Executable.labels odd.toExecutable) "odd" := by
    rw [Labels.label!_of_label? (label?_eq_some_addrOf (p := even ++ odd) (k := 0 + even.length) (by simp [even, odd, List.findIdx?_cons])),
        Labels.label!_of_label? (label?_eq_some_addrOf (p := odd) (k := 0) (by simp [odd, List.findIdx?_cons])),
        addrOf_drop]
    rfl
  rw [h_lbl_eq]
  refine eventually_weaken _ _ _ _ ?_ (Eventually.append_right even odd _ _ h_spec)
  rintro ⟨st', pc⟩ ⟨status, hs⟩
  refine ⟨status, ?_⟩
  cases hn : n.toNat with
  | zero =>
    simp only [hn] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨rfl, (addrOf_drop 8).symm⟩
  | succ n' =>
    simp only [hn] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨rfl, (addrOf_drop 4).symm⟩

private theorem body_in_even_odd.spec [layout : WellFormedLayout (even ++ odd)]
    (isEven : Bool) (st : MachineData) (n : UInt64) (hd : st.regs.rdi = n) :
    letI e : Executable := (even ++ odd).toExecutable
    letI := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ => ∃ status,
        match n.toNat with
        | 0 => st' = { st with regs.rax := (if isEven then (1 : Int64) else 0).toUInt64, status } ∧
               pc = e.addrOf (if isEven then 8 else 8 + even.length)
        | n' + 1 => st' = { st with regs.rdi := UInt64.ofNat n', status } ∧
                    pc = e.addrOf (if isEven then 4 else 4 + even.length))
      ⟨st, if isEven then label! "even" else label! "odd"⟩ := by
  cases isEven
  · exact odd_body.spec st n hd
  · exact even_body.spec st n hd

private theorem even_odd.base [layout : WellFormedLayout (even ++ odd)]
    (isEven : Bool) (n : UInt64) (st : MachineData) (ra : Int64)
    (stack : List UInt8) (R : DataMem → Prop)
    (hn0 : n.toNat = 0) (hlen : stack.length = 8 * 0) (hd : st.regs.rdi = n)
    (hmem : st.dmem =⋆
      Eq (stack.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * 0))) ⋆
      Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) :
    letI e : Executable := (even ++ odd).toExecutable
    letI := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ =>
        ∃ stack' : List UInt8, stack'.length = 8 * 0 ∧
        st'.regs.rax = (if (0 % 2 == 0) == isEven then 1 else 0) ∧
        st'.regs.rsp = st.regs.rsp + 8 ∧
        (st'.dmem =⋆
          Eq (stack'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * 0))) ⋆
          Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) ∧
        pc = ra)
      ⟨st, if isEven then label! "even" else label! "odd"⟩ := by
  refine eventually_trans _ _ _ _ (body_in_even_odd.spec isEven st n hd) ?_
  rintro ⟨st₁, pc₁⟩ ⟨status, h1⟩
  simp only [hn0] at h1
  rcases h1 with ⟨rfl, rfl⟩
  have hk_ret : (even ++ odd)[if isEven then 8 else 8 + even.length]? =
      some (.instr (.regular .W64 .W64 .ret)) := by
    cases isEven <;> decide
  refine step_ret (even ++ odd) hk_ret _ ra
    (Eq (stack.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * 0))) ⋆ R)
    (cast (congrFun (by ac_rfl) _) hmem) _
    ⟨stack, hlen, ?_, rfl, cast (congrFun (by ac_rfl) _) hmem, rfl⟩
  dsimp only
  cases isEven <;> rfl

private theorem even_odd.step [layout : WellFormedLayout (even ++ odd)]
    (k' : Nat) (isEven : Bool)
    (h_rec : ∀ (n : UInt64) (st : MachineData) (ra : Int64) (stack : List UInt8) (R : DataMem → Prop),
      n.toNat = k' → 8 * k' ≤ 2 ^ 64 → stack.length = 8 * k' → st.regs.rdi = n →
      (st.dmem =⋆
        Eq (stack.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * k'))) ⋆
        Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) →
      letI e : Executable := (even ++ odd).toExecutable
      letI := e.labels
      Eventually (step1 e)
        (post := fun ⟨st', pc⟩ =>
          ∃ stack' : List UInt8, stack'.length = 8 * k' ∧
          st'.regs.rax = (if (k' % 2 == 0) == !isEven then 1 else 0) ∧
          st'.regs.rsp = st.regs.rsp + 8 ∧
          (st'.dmem =⋆
            Eq (stack'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * k'))) ⋆
            Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) ∧
          pc = ra)
        ⟨st, if !isEven then label! "even" else label! "odd"⟩)
    (n : UInt64) (st : MachineData) (ra : Int64)
    (stack : List UInt8) (R : DataMem → Prop)
    (hnk : n.toNat = k' + 1) (hbound : 8 * (k' + 1) ≤ 2 ^ 64)
    (hlen : stack.length = 8 * (k' + 1)) (hd : st.regs.rdi = n)
    (hmem : st.dmem =⋆
      Eq (stack.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * (k' + 1)))) ⋆
      Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) :
    letI e : Executable := (even ++ odd).toExecutable
    letI := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ =>
        ∃ stack' : List UInt8, stack'.length = 8 * (k' + 1) ∧
        st'.regs.rax = (if ((k' + 1) % 2 == 0) == isEven then 1 else 0) ∧
        st'.regs.rsp = st.regs.rsp + 8 ∧
        (st'.dmem =⋆
          Eq (stack'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * (k' + 1)))) ⋆
          Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) ∧
        pc = ra)
      ⟨st, if isEven then label! "even" else label! "odd"⟩ := by
  letI e : Executable := (even ++ odd).toExecutable
  letI := e.labels
  refine eventually_trans _ _ _ _ (body_in_even_odd.spec isEven st n hd) ?_
  rintro ⟨st₁, pc₁⟩ ⟨status, h1⟩
  simp only [hnk] at h1
  rcases h1 with ⟨rfl, rfl⟩
  have h_len_take : (stack.take (8 * k')).length = 8 * k' := by simp [hlen]
  have h_len_drop : (stack.drop (8 * k')).length = 8 := by simp [hlen]; omega
  have hmem_split :
      (st.dmem =⋆
        Eq ((stack.drop (8 * k')).At (st.regs.rsp.toBitVec - 8#64)) ⋆
        (Eq ((stack.take (8 * k')).At ((st.regs.rsp.toBitVec - 8#64) - BitVec.ofNat 64 (8 * k'))) ⋆
        (Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R))) := by
    have hsplit := stack_split_sep (stack.take (8 * k')) (stack.drop (8 * k')) st.regs.rsp.toBitVec k'
      (Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) (by omega) h_len_take
    rw [List.take_append_drop] at hsplit
    rw [← hsplit]
    exact cast (congrFun (by ac_rfl) _) hmem
  have hk_call : (even ++ odd)[if isEven then 4 else 4 + even.length]? =
      some (.instr (.regular .W64 .W64 (.call (.rel (.sub (.label (if isEven then "odd" else "even")) .after_current_instruction))))) := by
    cases isEven <;> decide
  have htgt_lbl : @Labels.label? e.labels (if isEven then "odd" else "even") =
      some (if !isEven then label! "even" else label! "odd") := by
    have h_even_lbl : @Labels.label? e.labels "even" = some (e.addrOf 0) :=
      label?_eq_some_addrOf (p := even ++ odd) (by simp [even, List.findIdx?_cons])
    have h_odd_lbl : @Labels.label? e.labels "odd" = some (e.addrOf (0 + even.length)) :=
      label?_eq_some_addrOf (p := even ++ odd) (by simp [even, odd, List.findIdx?_cons])
    cases isEven
    · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      rw [Labels.label!_of_label? h_even_lbl, h_even_lbl]
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [Labels.label!_of_label? h_odd_lbl, h_odd_lbl]
  let call_idx := if isEven then 4 else 4 + even.length
  let ret_pc := e.addrOf (call_idx + 1)
  refine eventually_trans _ _ _ _ (step_call (even ++ odd) hk_call
    { st with regs := { st.regs with rdi := UInt64.ofNat k' }, status }
    (if !isEven then label! "even" else label! "odd")
    htgt_lbl (stack.drop (8 * k')) h_len_drop
    (Eq ((stack.take (8 * k')).At ((st.regs.rsp.toBitVec - 8#64) - BitVec.ofNat 64 (8 * k'))) ⋆
     (Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R))
    hmem_split (fun x => x = _) rfl) ?_
  rintro _ rfl
  have h_store := Mem.storeInt_sep (st.regs.rsp.toBitVec - 8#64) 8 (stack.drop (8 * k'))
    (Eq ((stack.take (8 * k')).At ((st.regs.rsp.toBitVec - 8#64) - BitVec.ofNat 64 (8 * k'))) ⋆
     (Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R))
    st.dmem ⟨hmem_split, h_len_drop⟩ ret_pc.toInt
  have h_ih := h_rec (UInt64.ofNat k')
    { st with
      regs := { st.regs with rdi := UInt64.ofNat k', rsp := st.regs.rsp - 8 }
      status
      dmem := st.dmem.storeInt (st.regs.rsp.toBitVec - 8#64) 8 ret_pc.toInt }
    ret_pc (stack.take (8 * k'))
    (Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R)
    (by dsimp only [UInt64.ofNat, UInt64.toNat]; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := n.toBitVec.isLt; omega))
    (by omega) h_len_take rfl (by simp only [UInt64.toBitVec_sub]; exact cast (congrFun (by ac_rfl) _) h_store)
  dsimp only
  refine eventually_trans _ _ _ _ h_ih ?_
  rintro ⟨st₂, pc₂⟩ ⟨stack_rec, h_len_rec, h_rax, h_rsp, h_mem₂, rfl⟩
  have h_rsp_eq : st₂.regs.rsp = st.regs.rsp := by
    rw [h_rsp, ← UInt64.toBitVec_inj]
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub, BitVec.sub_add_cancel]
  have h_ret_idx : (even ++ odd)[call_idx + 1]? = some (.instr (.regular .W64 .W64 .ret)) := by
    dsimp only [call_idx]; cases isEven <;> decide
  refine step_ret (even ++ odd) h_ret_idx st₂ ra
    (Eq (stack_rec.At ((st.regs.rsp.toBitVec - 8#64) - BitVec.ofNat 64 (8 * k'))) ⋆
     Eq ((Int.toBytes 8 ret_pc.toInt).At (st.regs.rsp.toBitVec - 8#64)) ⋆ R)
    ?_ _ ?_
  · rw [h_rsp_eq, ← sep_assoc,
      sep_comm _ (Eq (stack_rec.At _) ⋆ Eq ((Int.toBytes 8 ret_pc.toInt).At _)), sep_assoc]
    dsimp only at h_mem₂
    simp only [UInt64.toBitVec_sub] at h_mem₂
    exact h_mem₂
  · refine ⟨stack_rec ++ Int.toBytes 8 ret_pc.toInt,
      by rw [List.length_append, h_len_rec, Int.toBytes_length]; omega, ?_, by rw [h_rsp_eq], ?_, rfl⟩
    · rw [h_rax]; cases isEven <;> grind
    · rw [sep_assoc, stack_split_sep stack_rec (Int.toBytes 8 ret_pc.toInt) st.regs.rsp.toBitVec k'
        (Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R)
        (by rw [h_len_rec, Int.toBytes_length]; omega) h_len_rec]
      dsimp only at h_mem₂
      simp only [UInt64.toBitVec_sub] at h_mem₂
      exact cast (congrFun (by ac_rfl) _) h_mem₂

theorem even_odd.spec [layout : WellFormedLayout (even ++ odd)] :
    ∀ (k : Nat) (isEven : Bool) (n : UInt64) (st : MachineData) (ra : Int64)
      (stack : List UInt8) (R : DataMem → Prop),
      n.toNat = k →
      8 * k ≤ 2 ^ 64 →
      stack.length = 8 * k →
      st.regs.rdi = n →
      (st.dmem =⋆
        Eq (stack.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * k))) ⋆
        Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) →
      letI e : Executable := (even ++ odd).toExecutable
      letI := e.labels
      Eventually (step1 e)
        (post := fun ⟨st', pc⟩ =>
          ∃ stack' : List UInt8, stack'.length = 8 * k ∧
          st'.regs.rax = (if (k % 2 == 0) == isEven then 1 else 0) ∧
          st'.regs.rsp = st.regs.rsp + 8 ∧
          (st'.dmem =⋆
            Eq (stack'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * k))) ⋆
            Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) ∧
          pc = ra)
        ⟨st, if isEven then label! "even" else label! "odd"⟩ := by
  intro k
  induction k with
  | zero => exact fun isEven n st ra stack R hn0 _ hlen hd hmem => even_odd.base isEven n st ra stack R hn0 hlen hd hmem
  | succ k' ih => exact fun isEven => even_odd.step k' isEven (ih (!isEven))

theorem even.spec [layout : WellFormedLayout (even ++ odd)]
    (n : UInt64) (st : MachineData) (ra : Int64)
    (stack : List UInt8) (h_bound : 8 * n.toNat ≤ 2 ^ 64) (h_len : stack.length = 8 * n.toNat)
    (R : DataMem → Prop)
    (h_mem : st.dmem =⋆
      Eq (stack.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * n.toNat))) ⋆
      Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R)
    (hd : st.regs.rdi = n) :
    letI e : Executable := (even ++ odd).toExecutable
    letI := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ =>
        ∃ stack' : List UInt8, stack'.length = 8 * n.toNat ∧
        st'.regs.rax = (if n % 2 == 0 then 1 else 0) ∧
        st'.regs.rsp = st.regs.rsp + 8 ∧
        (st'.dmem =⋆
          Eq (stack'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * n.toNat))) ⋆
          Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) ∧
        pc = ra)
      ⟨st, label! "even"⟩ := by
  have hspec := even_odd.spec n.toNat true n st ra stack R rfl h_bound h_len hd h_mem
  have hmod : (n % 2 == 0) = (n.toNat % 2 == 0) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mod]
    simp
  simpa [hmod] using hspec

theorem odd.spec [layout : WellFormedLayout (even ++ odd)]
    (n : UInt64) (st : MachineData) (ra : Int64)
    (stack : List UInt8) (h_bound : 8 * n.toNat ≤ 2 ^ 64) (h_len : stack.length = 8 * n.toNat)
    (R : DataMem → Prop)
    (h_mem : st.dmem =⋆
      Eq (stack.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * n.toNat))) ⋆
      Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R)
    (hd : st.regs.rdi = n) :
    letI e : Executable := (even ++ odd).toExecutable
    letI := e.labels
    Eventually (step1 e)
      (post := fun ⟨st', pc⟩ =>
        ∃ stack' : List UInt8, stack'.length = 8 * n.toNat ∧
        st'.regs.rax = (if n % 2 == 1 then 1 else 0) ∧
        st'.regs.rsp = st.regs.rsp + 8 ∧
        (st'.dmem =⋆
          Eq (stack'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 (8 * n.toNat))) ⋆
          Eq ((Int.toBytes 8 ra.toInt).At st.regs.rsp.toBitVec) ⋆ R) ∧
        pc = ra)
      ⟨st, label! "odd"⟩ := by
  have hspec := even_odd.spec n.toNat false n st ra stack R rfl h_bound h_len hd h_mem
  have hmod : (n % 2 == 1) = (n.toNat % 2 == 1) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mod]
    simp
  have hbool : (n.toNat % 2 == 1) = ((n.toNat % 2 == 0) == false) := by
    cases Nat.mod_two_eq_zero_or_one n.toNat <;> simp_all
  simpa [hmod, hbool] using hspec
