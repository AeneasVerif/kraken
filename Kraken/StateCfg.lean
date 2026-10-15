module

/-
The control-flow rule of the state wp. A program with labels is a list of
basic blocks (`Program.blockAt`). `Program.WP.cfg` proves a triple for a program
from one triple per block: a table `T` gives the assertion at
each label, and a variant `var` orders the jumps. A block falls
into the next block, and a jump reaches the cell of its label. A call steps by
the callee's `CallSpec`, which `callSpec_of_triple` derives from its body.
-/
public import Kraken.X64.WP.Instance
public import Kraken.Blocks

@[expose] public section

open Std.WP
open Lean.Order

/-! ## The text of a block -/

/-- The text from a block's label: the label cell, the block's body, and the
text from the label the block falls into. -/
theorem Program.fromLabel_block {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.fromLabel p l
      = Directive.label l :: (blk.body ++ blk.next.elim [] (Program.fromLabel p)) := by
  obtain ⟨-, i, hi, hnext⟩ := Program.blockAtAux_spec h
  rw [Program.fromLabel_view hnd hi, Program.drop_flatMap_cons hi]
  congr 2
  cases hj : (Program.view p).2[i + 1]? with
  | none =>
    rw [hj] at hnext
    rw [hnext, List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp hj)]
    rfl
  | some lb =>
    obtain ⟨l', b'⟩ := lb
    rw [hj] at hnext
    rw [hnext]
    exact (Program.fromLabel_view hnd hj).symm

/-- The text from a label is a suffix of the program. -/
theorem Program.drop_fromLabel (p : Program) (l : Label) :
    p.drop (p.length - (Program.fromLabel p l).length) = Program.fromLabel p l := by
  obtain ⟨t, ht⟩ := Program.fromLabel_suffix p l
  have hlen := congrArg List.length ht
  rw [List.length_append] at hlen
  rw [show p.length - (Program.fromLabel p l).length = t.length by omega]
  calc p.drop t.length = (t ++ Program.fromLabel p l).drop t.length := by rw [ht]
    _ = Program.fromLabel p l := List.drop_left

/-! ## Calls -/

def MachineData.pushRa (s : MachineData) (ra : Int64) : MachineData :=
  { s with regs := s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64),
           dmem := Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt }

@[grind =] theorem MachineData.regs_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).regs = s.regs.set64 .rsp (s.regs.get64 .rsp - 8#64) := rfl

@[grind =] theorem MachineData.dmem_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).dmem = Mem.storeInt s.dmem (s.regs.get64 .rsp - 8#64) 8 ra.toBitVec.toInt := rfl

@[grind =] theorem Mem.loadInt_storeInt_64 (m : DataMem) (a : BitVec 64) (v : Int) :
    (m.storeInt a 8 v).loadInt a 8 = some (Int.ofBytes (Int.toBytes 8 v)) :=
  Mem.loadInt_storeInt m a _ v (by decide)

@[grind =] theorem Int64.ofBitVec_ofBytes_toBytes (ra : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt))) = ra := by
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

@[grind =] theorem MachineData.retAddr_pushRa (s : MachineData) (ra : Int64) :
    (s.pushRa ra).retAddr = some ra := by
  simp only [MachineData.retAddr, MachineData.pushRa, Reg64s.get64_set64, reduceIte,
    Mem.loadInt_storeInt _ _ _ _ (by decide : 8 ≤ 2 ^ 64), Option.map_some,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]

/-- The registers a callee may change. -/
structure Modifies where
  regs : List Reg64

/-- `s'` agrees with `s` on the registers outside `m`. -/
def Modifies.Agree (m : Modifies) (s s' : MachineData) : Prop :=
  ∀ r, r ∉ m.regs → s'.regs.get64 r = s.regs.get64 r

theorem Modifies.Agree.reg {m : Modifies} {s s' : MachineData} (h : m.Agree s s') (r : Reg64)
    (hr : r ∉ m.regs) : s'.regs.get64 r = s.regs.get64 r := h r hr
grind_pattern Modifies.Agree.reg => m.Agree s s', s'.regs.get64 r

@[grind =] theorem Modifies.agree_iff (m : Modifies) (s s' : MachineData) :
    m.Agree s s' ↔
      (.rax ∈ m.regs ∨ s'.regs.get64 .rax = s.regs.get64 .rax)
      ∧ (.rbx ∈ m.regs ∨ s'.regs.get64 .rbx = s.regs.get64 .rbx)
      ∧ (.rcx ∈ m.regs ∨ s'.regs.get64 .rcx = s.regs.get64 .rcx)
      ∧ (.rdx ∈ m.regs ∨ s'.regs.get64 .rdx = s.regs.get64 .rdx)
      ∧ (.rsi ∈ m.regs ∨ s'.regs.get64 .rsi = s.regs.get64 .rsi)
      ∧ (.rdi ∈ m.regs ∨ s'.regs.get64 .rdi = s.regs.get64 .rdi)
      ∧ (.rsp ∈ m.regs ∨ s'.regs.get64 .rsp = s.regs.get64 .rsp)
      ∧ (.rbp ∈ m.regs ∨ s'.regs.get64 .rbp = s.regs.get64 .rbp)
      ∧ (.r8 ∈ m.regs ∨ s'.regs.get64 .r8 = s.regs.get64 .r8)
      ∧ (.r9 ∈ m.regs ∨ s'.regs.get64 .r9 = s.regs.get64 .r9)
      ∧ (.r10 ∈ m.regs ∨ s'.regs.get64 .r10 = s.regs.get64 .r10)
      ∧ (.r11 ∈ m.regs ∨ s'.regs.get64 .r11 = s.regs.get64 .r11)
      ∧ (.r12 ∈ m.regs ∨ s'.regs.get64 .r12 = s.regs.get64 .r12)
      ∧ (.r13 ∈ m.regs ∨ s'.regs.get64 .r13 = s.regs.get64 .r13)
      ∧ (.r14 ∈ m.regs ∨ s'.regs.get64 .r14 = s.regs.get64 .r14)
      ∧ (.r15 ∈ m.regs ∨ s'.regs.get64 .r15 = s.regs.get64 .r15) := by
  constructor
  · intro h
    exact ⟨Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _)⟩
  · intro h r hr
    cases r <;> simp_all

open Program.WP in
/-- Calling `f` from a state that satisfies `Pre` returns with `Post`, and keeps the registers
outside `m`. -/
abbrev CallSpec [Host] (f : Label) (Pre : MachineData → Prop)
    (Post : MachineData → MachineData → Prop) (m : Modifies) : Prop :=
  ∀ asz osz (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => ((Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true) ⊓ Pre s
        ⊓ (∀ s', Post s s' → m.Agree s s' → Q () s') ⦄
      Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction))))
    ⦃ Q; E ⦄

namespace Program.WP

/- A jump exit of `cfg` asks where its target sits in the list of labels of the program,
`["start", ".loop", …]`. With `Program.WP` open, `grind`'s normalizer answers by evaluation. -/
attribute [scoped grind norm] List.idxOf_cons List.contains_cons

variable [Host]

/-- A callee's body triple, linked in the program, is its call spec. -/
theorem callSpec_of_triple {P body rest : Program} {k : Nat} (hP : P.IsInfixAt Host.prog k)
    {f : Label} {Pre : MachineData → Prop} {Post : MachineData → MachineData → Prop}
    {m : Modifies} (hat : Program.fromLabel P f = Directive.label f :: (body ++ rest))
    (hbody : ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ Pre s ⦄ (Directive.label f :: body)
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ Post s t ∧ m.Agree s t ⦄) :
    CallSpec f Pre Post m := by
  intro asz osz Q E
  have hl := Program.drop_fromLabel P f ▸ hP.drop (P.length - (Program.fromLabel P f).length)
  generalize k + (P.length - (Program.fromLabel P f).length) = j at hl
  rw [hat] at hl
  obtain ⟨hbody', -⟩ := List.IsInfixAt.append (a := Directive.label f :: body) hl
  refine triple_directive.mpr ⟨fun s hpre => ?_⟩
  simp only [meet_prop_eq_and] at hpre
  obtain ⟨⟨hmapped, hpre⟩, hcont⟩ := hpre
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  intro k' hs
  refine eventually_trans _
    (fun st => st = ⟨s.pushRa (Host.addrOf (k' + 1)), Host.addrOf j⟩) _ _
    (Host.eventually_of_interp hs ?_) ?_
  · simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
      ConstExpr.interp, MachineData.store, hload, Effects.All]
    rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left, Host.label_eq (i := 0) hl rfl, Nat.add_zero]
    rfl
  · rintro _ rfl
    refine eventually_trans _ _ _ _ ((hbody s _).1 _ ⟨rfl, hpre⟩ j hbody') ?_
    rintro ⟨t, a⟩ (⟨_, h⟩ | ⟨ha, hpost, hagree⟩)
    · exact h.elim
    · exact Eventually.done _ (Or.inl ⟨ha, hcont t hpost hagree⟩)

/-! ## The control-flow rule -/

/-- The control-flow rule: one table `T`, one variant `var`, one triple per block of
`Program.blockAt`. Each block is entered with its table entry and the variant snapshotted as
`n`. It falls into the next block with the entry there and the variant not increased, or, as the
last block, falls through the end of `p` with `Qend`. A jump either reaches a block of `p` along
`Program.EdgeLt`, or leaves `p` with `Ext`. -/
theorem cfg {p p' : Program} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (Qend : MachineData → Prop) (Ext : Int64 → MachineData → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat, ∀ k, p.IsInfixAt Host.prog k →
      ⦃ fun s => T l s ∧ var l s = n ⦄
        blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ s => Qend s);
        fun a s => (∃ l', label l' = a
          ∧ (Program.blockAt p l').isSome ∧ T l' s ∧ Program.EdgeLt p var l n l' s) ∨ Ext a s ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl) (hnd : (Program.labels p).Nodup := by decide) :
    ⦃ fun s => T l₀ s ⦄ p ⦃ fun _ s => Qend s; Ext ⦄ := by
  refine ⟨fun s hT k hlink => ?_⟩
  let B := fun st : MachineState =>
    (st.pc = Host.addrOf (k + p.length) ∧ Qend st.data) ∨ Ext st.pc st.data
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  have hcellOf : ∀ l, Program.fromLabel p l ≠ [] →
      p[p.length - (Program.fromLabel p l).length]? = some (Directive.label l) := by
    intro l hne
    have hdrop := Program.drop_fromLabel p l
    obtain ⟨t, rest, -, hfl, -, -⟩ := Program.fromLabel_split hnd hne
    conv at hdrop => rhs; rw [hfl]
    simpa [List.head?_drop] using congrArg List.head? hdrop
  have key : ∀ x : Label × MachineData, (Program.blockAt p x.1).isSome → T x.1 x.2 →
      Eventually (step1 Host.exe) B
        ⟨x.2, Host.addrOf (k + (p.length - (Program.fromLabel p x.1).length))⟩ := by
    intro x
    induction x using (measure (Program.cfgMeasure p var)).wf.induction with
    | _ x ih =>
      obtain ⟨l, s⟩ := x
      intro hsome hT
      dsimp only at hsome hT ⊢
      obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hsome
      have htext := Program.fromLabel_block hnd hblk
      have hlen := congrArg List.length htext
      simp only [List.length_cons, List.length_append] at hlen
      have hdrop := Program.drop_fromLabel p l
      have hsuf : (Program.fromLabel p l).length ≤ p.length := by
        have := congrArg List.length hdrop
        simp only [List.length_drop] at this
        omega
      have hl := hdrop ▸ hlink.drop (p.length - (Program.fromLabel p l).length)
      generalize hi : p.length - (Program.fromLabel p l).length = i at hdrop hl
      rw [htext] at hl
      obtain ⟨hlab, hrest⟩ := List.IsInfixAt.append (a := [Directive.label l]) hl
      obtain ⟨hbody, -⟩ := List.IsInfixAt.append hrest
      refine eventually_trans _ (fun st => st = ⟨s, Host.addrOf (k + i + 1)⟩) _ _
        (Host.eventually_of_interp hlab (by simp only [Directive.interp, Effects.All])) ?_
      rintro _ rfl
      refine eventually_trans _ _ _ _ ((hblocks l blk hblk (var l s) k hlink).1 s ⟨hT, rfl⟩
        (k + i + 1) hbody) ?_
      rintro ⟨s', a⟩ (⟨hend, hq⟩ | hE)
      · dsimp only at hend hq
        subst hend
        cases hn : blk.next with
        | none =>
          rw [hn] at hq hlen
          refine Eventually.done _ (Or.inl ⟨?_, hq⟩)
          simp only [Option.elim, List.length_nil] at hlen
          show Host.addrOf (k + i + 1 + blk.body.length) = _
          rw [show k + i + 1 + blk.body.length = k + p.length by omega]
        | some l' =>
          rw [hn] at hq hlen
          obtain ⟨hT', hvar⟩ := hq
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hblk hn
          simp only [Option.elim] at hlen
          rw [show k + i + 1 + blk.body.length
            = k + (p.length - (Program.fromLabel p l').length) by omega]
          refine ih (l', s') ?_ hsome' hT'
          have hK' := hK l'
          show Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s)
          unfold Program.cfgMeasure
          dsimp only
          have hmul : var l' s' * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          omega
      · rcases hE with ⟨l', hlab', hsome', hT', hedge⟩ | hext
        · dsimp only at hlab'
          subst hlab'
          have hne : Program.fromLabel p l' ≠ [] := by
            obtain ⟨blk', hblk'⟩ := Option.isSome_iff_exists.mp hsome'
            rw [Program.fromLabel_block hnd hblk']
            exact List.cons_ne_nil _ _
          rw [Host.label_eq hlink (hcellOf l' hne)]
          refine ih (l', s') ?_ hsome' hT'
          have hK' := hK l'
          show Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s)
          unfold Program.cfgMeasure
          dsimp only
          rcases hedge with hlt | ⟨heq, hij⟩
          · have hmul : (var l' s' + 1) * ((Program.view p).2.length + 1)
                ≤ var l s * ((Program.view p).2.length + 1) :=
              Nat.mul_le_mul_right _ hlt
            have hsucc : (var l' s' + 1) * ((Program.view p).2.length + 1)
                = var l' s' * ((Program.view p).2.length + 1)
                  + ((Program.view p).2.length + 1) := Nat.succ_mul _ _
            omega
          · rw [heq]
            omega
        · exact Eventually.done _ (Or.inr hext)
  have h0 : (Program.blockAt p l₀).isSome := by
    rw [hp]
    show (Program.blockAtAux (Program.view (Directive.label l₀ :: p')).2 l₀).isSome = true
    simp [Program.view, Program.blockAtAux]
  have hfl : Program.fromLabel p l₀ = p := by
    have hnot : Program.fromLabel p' l₀ = [] := Classical.byContradiction fun hne => by
      have hmem := Program.mem_labels.mpr (Program.fromLabel_mem hne)
      have hnd' := hnd
      rw [hp] at hnd'
      simp only [Program.labels_cons_label] at hnd'
      exact (List.nodup_cons.mp hnd').1 hmem
    rw [hp]
    simp [hnot]
  have := key (l₀, s) h0 hT
  rwa [hfl, Nat.sub_self, Nat.add_zero] at this

/-- `cfg` at one state, in the goal form of `vcgen`. -/
theorem cfg_wp {p p' : Program} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (Qend : MachineData → Prop) (Ext : Int64 → MachineData → Prop)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat, ∀ k, p.IsInfixAt Host.prog k →
      ⦃ fun s => T l s ∧ var l s = n ⦄
        blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T l' s ∧ var l' s ≤ n
         | none => fun _ s => Qend s);
        fun a s => (∃ l', label l' = a
          ∧ (Program.blockAt p l').isSome ∧ T l' s ∧ Program.EdgeLt p var l n l' s) ∨ Ext a s ⦄)
    (s : MachineData) (hT : T l₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl) (hnd : (Program.labels p).Nodup := by decide) :
    ⊤ ⊑ WP.wp p (fun _ s => Qend s) Ext s :=
  fun _ => (cfg T var Qend Ext hblocks hp hnd).1 s hT

end Program.WP
