module

public import Kraken.X64.WP
import all Kraken.Mem
import all Kraken.X64.WP.Def
import Kraken.X64.Parser

open Kraken.X64.Parser Std ExtHashMap

namespace State.EvenOdd

def even : Program := parse("
even:
  test %rdi, %rdi
  jz even_zero
  dec %rdi
  call odd
  ret
even_zero:
  mov $1, %rax
  ret
")

def odd : Program := parse("
odd:
  test %rdi, %rdi
  jz odd_zero
  dec %rdi
  call even
  ret
odd_zero:
  mov $0, %rax
  ret
")

def _root_.MachineData.pushRa (s : MachineData) (ra : Int64) : MachineData :=
  { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
           dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt }

def Mapped (b : BitVec 64) (n : Nat) (m : Mem 64) : Prop := ∀ a, (a - b).toNat < n → m[a]?.isSome

def UnchangedOutside (b : BitVec 64) (n : Nat) (m m' : Mem 64) : Prop :=
  ∀ a, n ≤ (a - b).toNat → m'[a]? = m[a]?

abbrev Pre (base : BitVec 64) (sz : Nat) (s : MachineData) : Prop :=
  8 * ((s.regs.get64 .rdi).toNat + 1) ≤ (s.regs.get64 .rsp - base).toNat
    ∧ (s.regs.get64 .rsp - base).toNat ≤ sz ∧ Mapped base sz s.dmem

abbrev Post (base : BitVec 64) (sz r : Nat) (s t : MachineData) : Prop :=
  (t.regs.get64 .rax).toNat = ((s.regs.get64 .rdi).toNat + r) % 2 ∧ Mapped base sz t.dmem

abbrev Agree (base : BitVec 64) (s t : MachineData) : Prop :=
  (∀ r, r ∉ [Reg64.rax, .rdi] → t.regs.get64 r = s.regs.get64 r)
    ∧ UnchangedOutside base (s.regs.get64 .rsp - base).toNat s.dmem t.dmem

abbrev Spec [Host] [FunDecls] (p : Program) (base : BitVec 64) (sz r : Nat) (s : MachineData) (ra : Int64) :=
  Pre base sz s → p.wp (fun _ => False)
    (fun st => st.pc = ra ∧ Post base sz r s st.data ∧ Agree base s st.data) (s.pushRa ra)

local macro "bv" : tactic => `(tactic| ((try simp -implicitDefEqProofs only [bitvec_to_nat,
  show 2 ^ Width.W64.bits = 2 ^ 64 from rfl] at *) <;> (have : 2 ^ Width.W64.bits = 2 ^ 64 := rfl) <;> omega))

@[simp] theorem get64_set64 (s : Reg64s) (r r' : Reg64) (v : BitVec 64) :
    (s.set64 r v).get64 r' = if r' = r then v else s.get64 r' := by
  cases r <;> cases r' <;> simp [Reg64s.set64, Reg64s.get64]

@[simp] theorem get_low64 (s : Reg64s) (r : Reg64) : s.get (.low r .W64) = s.get64 r := by
  simp [Reg64s.get, Reg.base, Reg.offset, BitVec.take, BitVec.drop]

local macro "rs" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [MachineData.pushRa, get64_set64, reduceCtorEq, ↓reduceIte] $[$loc]?)
local macro "stk" : tactic => `(tactic| (simp only [MachineData.StackAtOrBelow, MachineData.StackBelow,
  MachineData.pushRa, get64_set64, reduceCtorEq, ↓reduceIte] at *; rw [BitVec.toInt_eq_toNat_cond]; split <;> bv))

theorem get?_storeInt (m : Mem 64) (a x : BitVec 64) (v : Int) :
    (m.storeInt a 8 v)[x]? = ((Int.toBytes 8 v)[(x - a).toNat]?).or m[x]? := by
  rw [Mem.storeInt, Mem.storeBytes, union_eq, getElem?_union, get?_At _ _ _ (by simp [Int.toBytes_length])]

theorem loadInt_congr {m m' : Mem 64} {a : BitVec 64} (h : ∀ i < 8, m'[a + .ofNat 64 i]? = m[a + .ofNat 64 i]?) :
    m'.loadInt a 8 = m.loadInt a 8 := by
  simp only [Mem.loadInt, Mem.loadBytes, get?_eq_getElem?, List.map_congr_left fun i hi => h i (List.mem_range.mp hi)]

theorem loadInt_storeInt (m : Mem 64) (a : BitVec 64) (v : Int) :
    (m.storeInt a 8 v).loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 v)) := by
  have hs : ∀ i : BitVec 64, a + i - a = i := fun i => by bv_omega
  simp [Mem.loadInt, Mem.loadBytes, get?_storeInt, hs, List.range_succ, Int.toBytes, List.allSome, -BitVec.toNat_sub]

theorem loadInt_isSome {m : Mem 64} {b a : BitVec 64} {n : Nat} (h : Mapped b n m) (ha : (a - b).toNat + 8 ≤ n) :
    (m.loadInt a 8).isSome := by
  rw [Mem.loadInt, Mem.loadBytes, List.map_congr_left fun i hi => (Option.some_get! _ (by
    rw [get?_eq_getElem?]; exact h (a + .ofNat 64 i) (by have := List.mem_range.mp hi; bv_omega))).symm]
  simp [List.allSome, ← Option.pure_def, List.mapM_pure]; rfl

theorem mapped_storeInt {b a : BitVec 64} {n : Nat} {m : Mem 64} (h : Mapped b n m) (v : Int) :
    Mapped b n (m.storeInt a 8 v) := fun x hx => by simp [get?_storeInt, h x hx]

theorem uo_push {s : MachineData} {base : BitVec 64} (ra : Int64) (h : 8 ≤ (s.regs.get64 .rsp - base).toNat) :
    UnchangedOutside base (s.regs.get64 .rsp - base).toNat s.dmem (s.pushRa ra).dmem := fun x hx => by
  rw [MachineData.pushRa, get?_storeInt, List.getElem?_eq_none (by rw [Int.toBytes_length]; bv)]; rfl

section
variable [Host]

theorem prog_at {p : Program} {H : Embedding p} {i : Nat} {d : Directive} (hi : p[i]? = some d) :
    Host.prog[H.start + i]? = some d := by
  obtain ⟨hlt, hpi⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.isInfixAt_iff_getElem?.mp H.isInfixAt i hlt, hpi]

theorem addrOf_label {p : Program} {H : Embedding p} {i : Nat} {l : Label} (hi : p[i]? = some (.label l)) :
    Host.addrOf (H.start + (i + 1)) = Host.addrOf (H.start + i) := by
  rw [← Nat.add_assoc, Host.addrOf_succ (prog_at hi), Host.label_size _ _ (prog_at hi)]; simp

theorem stepOut_of_not_below {pc a : Int64} {t t' : MachineData} {funs} {next jump : MachineState → Prop}
    (hb : ¬ t'.StackBelow t) (h : jump ⟨t', a⟩) : Host.exe.StepOut funs ⟨t, pc⟩ next jump ⟨t', a⟩ := by
  unfold Executable.StepOut; split <;> simp_all

variable [FunDecls] (hpos : ∀ i ins, Host.prog[i]? = some (.instr ins) → 0 < Kraken.Layout.size Directive i)

abbrev Loop (p : Program) (H : Embedding p) (done exit : MachineState → Prop) (s₀ : MachineData) :=
  While (·.pc ≠ H.endAddr) (fun c => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f =>
    f.prog.wp (fun _ => False)) c (p.ContinueAtOwnLabel s₀ c exit)) done

include hpos

theorem loop_step {p : Program} {H : Embedding p} {done exit : MachineState → Prop} {s₀ t : MachineData}
    {i : Nat} {ins : Instr} (hi : p[i]? = some (.instr ins))
    (h : ∀ (P : MachineState → Prop) (n : MachineData → Effects) (jmp : Int64 → MachineData → Effects),
      (∀ t', Loop p H done exit s₀ ⟨t', Host.addrOf (H.start + (i + 1))⟩ → (n t').All P) →
      (∀ a t', Host.exe.StepOut (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
        ⟨t, Host.addrOf (H.start + i)⟩ (Loop p H done exit s₀)
          (p.ContinueAtOwnLabel s₀ (Loop p H done exit s₀) exit) ⟨t', a⟩ → (jmp a t').All P) →
      ((Directive.instr ins).interp t ⟨Host.addrOf (H.start + i), Host.addrOf (H.start + (i + 1))⟩ n jmp).All P) :
    Loop p H done exit s₀ ⟨t, Host.addrOf (H.start + i)⟩ := by
  have hk := prog_at (H := H) hi
  have := Host.sizeBefore_mono (show H.start + i + 1 ≤ H.start + p.length by
    have := (List.getElem?_eq_some_iff.mp hi).1; omega)
  refine While.step (fun he => ?_) (Host.stepIn_addrOf hk (hpos _ _ hk) h) fun _ h => h
  have := Host.sizeBefore_eq_of_addrOf_eq he; have := Host.sizeBefore_succ hk; have := hpos _ _ hk; omega

theorem ret_exit {p : Program} {H : Embedding p} {done exit : MachineState → Prop} {s₀ t : MachineData}
    {i : Nat} (hi : p[i]? = some (.instr (.regular .W64 .W64 .ret))) {ra : Int64}
    (hload : ∃ v, Mem.loadInt t.dmem (t.regs.get64 .rsp) 8 = some v ∧ Int64.ofBitVec (BitVec.ofInt 64 v) = ra)
    (ht : t.regs.get64 .rsp = s₀.regs.get64 .rsp)
    (hexit : exit ⟨{ t with regs := t.regs.set64 .rsp (t.regs.get64 .rsp + 8) }, ra⟩) :
    Loop p H done exit s₀ ⟨t, Host.addrOf (H.start + i)⟩ := by
  refine loop_step hpos hi fun P n j _ hj => ?_
  obtain ⟨v, hv, hra⟩ := hload
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.load, hv, Effects.All, hra]
  refine hj ra _ (stepOut_of_not_below (by stk) ?_)
  rwa [Program.ContinueAtOwnLabel, ite_eq_right fun h => h.2 (by stk)]

open Classical in
theorem call_step {p q : Program} {H : Embedding p} {Hq : Embedding q} {done exit : MachineState → Prop}
    {s₀ t : MachineData} {i : Nat} {g : Label}
    (hi : p[i]? = some (.instr (.regular .W64 .W64 (.call (.rel (.sub (.label g) .after_current_instruction))))))
    (hq : FunDecls.at (label g) = some ⟨q, Hq⟩)
    (hmapped : (Mem.loadInt t.dmem (t.regs.get64 .rsp - 8#64) 8).isSome)
    (hw : q.wp (fun _ => False) (fun st => if st.pc = Host.addrOf (H.start + (i + 1)) ∧ ¬ st.data.StackBelow t
        then Loop p H done exit s₀ st else p.ContinueAtOwnLabel s₀ (Loop p H done exit s₀) exit st)
      (t.pushRa (Host.addrOf (H.start + (i + 1))))) :
    Loop p H done exit s₀ ⟨t, Host.addrOf (H.start + i)⟩ := by
  refine loop_step hpos hi fun P n j _ hj => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hmapped
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp,
    MachineData.store, hv, Effects.All]
  rw [Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  refine hj (label g) (t.pushRa _) ?_
  have hk := prog_at (H := H) hi
  simp only [Executable.StepOut, hq, Option.map_some, Host.nextAddr_addrOf hk (hpos _ _ hk)]
  rwa [ite_eq_left (by stk)]

def body (f z g : Label) (c : Int64) : Program :=
  [.label f, .instr (.regular .W64 .W64 (.test (.reg (.low .rdi .W64)) (.regOrMem (.reg (.low .rdi .W64))))),
   .instr (.regular .W64 .W64 (.jcc .z z)), .instr (.regular .W64 .W64 (.dec (.reg (.low .rdi .W64)))),
   .instr (.regular .W64 .W64 (.call (.rel (.sub (.label g) .after_current_instruction)))),
   .instr (.regular .W64 .W64 .ret), .label z,
   .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.imm (.int64 c)))), .instr (.regular .W64 .W64 .ret)]

local macro "run_step" : tactic =>
  `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
      ConstExpr.interp, MachineData.set, MachineData.setReg, get_low64, Reg64s.set, Effects.All, ite_true])

theorem body_spec (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    {f z g : Label} {c : Int64} {r rq : Nat} {q : Program} {Hq : Embedding q}
    (hq : FunDecls.at (label g) = some ⟨q, Hq⟩) (hc : c.toBitVec.toNat = r) (hr : r < 2)
    (hrq : (rq + 1) % 2 = r) (base : BitVec 64) (sz n : Nat)
    (ih : ∀ s ra, (s.regs.get64 .rdi).toNat < n → Spec q base sz rq s ra)
    (s : MachineData) (ra : Int64) (hn : (s.regs.get64 .rdi).toNat = n) : Spec (body f z g c) base sz r s ra := by
  rintro ⟨hsz, hsz', hmap⟩; rw [Program.wp]; intro H
  have hload0 : ∃ v, Mem.loadInt (s.pushRa ra).dmem ((s.pushRa ra).regs.get64 .rsp) 8 = some v ∧
      Int64.ofBitVec (BitVec.ofInt 64 v) = ra := by
    rs; exact ⟨_, loadInt_storeInt .., by rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]⟩
  change Loop _ H _ _ _ ⟨_, Host.addrOf (H.start + 0)⟩; rw [← addrOf_label (i := 0) rfl]
  refine loop_step hpos (i := 1) rfl fun P n j hn' hj' => ?_; run_step; intro af
  refine hn' _ (loop_step hpos (i := 2) rfl fun P n j hn' hj' => ?_); run_step; rs
  simp only [BitVec.and_self, CondCode.interp, StatusFlags.from_result]
  by_cases hz0 : s.regs.get64 .rdi = 0
  · simp only [hz0]; refine hj' _ _ (stepOut_of_not_below (by stk) ?_)
    rw [Program.ContinueAtOwnLabel, ite_eq_left ⟨⟨z, by simp [body, Program.labels, Directive.label?], rfl⟩,
      by stk⟩, hlab _ _ (prog_at (H := H) (i := 6) rfl), ← addrOf_label (i := 6) rfl]
    refine loop_step hpos (i := 7) rfl fun P n j hn' hj' => ?_; run_step
    refine hn' _ (ret_exit hpos (ra := ra) (i := 8) rfl (by rs; exact hload0) (by rs) ?_)
    refine ⟨rfl, ⟨?_, mapped_storeInt hmap _⟩, fun r' hr' => ?_, uo_push ra (by omega)⟩
    · simp [hz0, Width.bits, hc]; omega
    · cases r' <;> simp_all [MachineData.pushRa, BitVec.sub_add_cancel]
  rw [ite_eq_right (by simpa [Width.bits] using hz0)]
  refine hn' _ (loop_step hpos (i := 3) rfl fun P n j hn' hj' => ?_); run_step
  refine hn' _ (call_step hpos (i := 4) rfl hq (by rs; exact loadInt_isSome (mapped_storeInt hmap _) (by bv)) ?_)
  refine Program.wp_mono (fun _ h => h.elim) ?_ ((ih _ _ (by rs; bv)) ⟨by rs; bv, by rs; bv, mapped_storeInt hmap _⟩)
  rintro ⟨d5, pc5⟩ ⟨rfl, ⟨hpost, hmap5⟩, hag₁, hag₂⟩
  rs at hpost hag₁ hag₂
  have hsp5 : d5.regs.get64 .rsp = s.regs.get64 .rsp - 8#64 := by simpa using hag₁ .rsp (by simp)
  rw [ite_eq_left ⟨rfl, by stk⟩]
  refine ret_exit hpos (ra := ra) (i := 5) rfl ?_ (by rs; exact hsp5)
    ⟨rfl, ⟨?_, hmap5⟩, fun r' hr' => ?_, fun x hx => (hag₂ x (by bv)).trans (uo_push ra (by omega) x hx)⟩
  · rw [hsp5, loadInt_congr fun i hi => hag₂ _ (by bv)]; rs at hload0; exact hload0
  · have : (s.regs.get64 .rdi - 1).toNat + 1 = (s.regs.get64 .rdi).toNat := by bv
    simp only [get64_set64, reduceCtorEq, ↓reduceIte, hpost]; omega
  · have := hag₁ r' hr'
    cases r' <;> simp only [get64_set64, reduceCtorEq, ↓reduceIte] at this ⊢ <;>
      first | exact this | (simp at hr'; done) | (rw [hsp5]; bv)

theorem evenOdd_spec (hlab : ∀ i l, Host.prog[i]? = some (.label l) → label l = Host.addrOf i)
    {He : Embedding even} {Ho : Embedding odd}
    (he : FunDecls.at (label "even") = some ⟨even, He⟩) (ho : FunDecls.at (label "odd") = some ⟨odd, Ho⟩)
    (base : BitVec 64) (sz : Nat) (s : MachineData) (ra : Int64) :
    Spec even base sz 1 s ra ∧ Spec odd base sz 0 s ra := by
  induction h : (s.regs.get64 .rdi).toNat using Nat.strongRecOn generalizing s ra with | _ n ih =>
  exact ⟨body_spec hpos hlab ho rfl (by decide) rfl base sz n (fun t ra hlt => (ih _ hlt t ra rfl).2) s ra h,
    body_spec hpos hlab he rfl (by decide) rfl base sz n (fun t ra hlt => (ih _ hlt t ra rfl).1) s ra h⟩

end

end State.EvenOdd
