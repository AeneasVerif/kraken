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

namespace Program.WP

/- A jump exit of `cfg` asks where its target sits in the list of labels of the program,
`["start", ".loop", …]`. With `Program.WP` open, `grind`'s normalizer answers by evaluation. -/
attribute [scoped grind norm] List.idxOf_cons List.contains_cons

variable [Host] [BlockEntries] [FunDecls]

abbrev CallSpec (f : Label) (Pre : MachineData → Prop) (Post : MachineData → MachineData → Prop)
    (m : Modifies) : Prop :=
  ∀ asz osz (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true ∧ Pre s
        ∧ (∀ s', Post s s' → m.Agree s s' → Q () s') ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ Q; E ⦄

theorem MachineData.stackBelow_pushRa (s : MachineData) (ra : Int64) : (s.pushRa ra).StackBelow s := by
  simp only [MachineData.StackBelow, MachineData.pushRa, Reg64s.set64_rsp, Reg64s.get64_rsp,
    Int64.toBitVec_ofBitVec]
  generalize s.regs.rsp.toBitVec = x
  rw [show x - (x - 8#64) = 8#64 by bv_omega]
  decide

theorem callSpec_of_triple {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g)
    {Pre : MachineData → Prop} {Post : MachineData → MachineData → Prop} {m : Modifies}
    (hbody : ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ Pre s ⦄ g.prog
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ Post s t ∧ m.Agree s t ⦄) :
    CallSpec f Pre Post m := by
  intro asz osz Q E
  refine ⟨fun s ⟨hmapped, hpre, hcont⟩ => Program.wp_single fun h _ _ _ _ hj => ?_⟩
  obtain ⟨i, hload⟩ := Option.isSome_iff_exists.mp hmapped
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hload, Effects.All]
  rw [Int64.ofBitVec_toBitVec, Int64.add_sub_self_left]
  refine hj (label f) (s.pushRa h.embedding.endAddr) ?_
  unfold Executable.StepOut
  simp only [hg, Option.map_some, MachineData.stackBelow_pushRa, ite_true]
  have hk := h.embedding.isInfixAt
  have hd := Host.exe_getElem? h.embedding.start
  rw [hk.cons.1, Option.map_some] at hd
  have hz : 0 < Kraken.Layout.size Directive h.embedding.start :=
    Host.instr_size_pos _ _ hk.cons.1 (by rintro ⟨⟩)
  have hft : Host.exe.fallthrough h.embedding.startAddr = h.embedding.endAddr :=
    Host.fallthrough_addrOf hd hz
  rw [hft]
  refine Program.wp_mono (fun _ h => h) ?_ ((hbody s h.embedding.endAddr).1 _ ⟨rfl, hpre⟩)
  rintro u ⟨hpc, hpost, hagree⟩
  simp only [hpc, ite_true]
  exact ⟨by trivial, hcont _ hpost hagree⟩

/-! ## The control-flow rule -/

theorem Program.blockAt_noInternal {p : Program} {l : Label} {blk : Program.Block}
    (h : Program.blockAt p l = some blk) (a : Int64) : ¬ blk.body.InternalTarget a := by
  rintro ⟨l', -, hl', -⟩
  obtain ⟨-, i, hi, -⟩ := Program.blockAtAux_spec h
  have hfree := (Program.view_free p).2 _ (List.mem_of_getElem? hi) (.label l') (Program.mem_labels.mp hl')
  simp [Directive.isLabel] at hfree

/-- The control-flow rule: one table `T`, one variant `var`, one triple per block of
`Program.blockAt`. Each block is entered with its table entry and the variant snapshotted as
`n`. It falls into the next block with the entry there and the variant not increased, or, as the
last block, falls through the end of `p` with `Qend`. A jump either reaches a block of `p` along
`Program.EdgeLt`, or leaves `p` with `Ext`; a jump to a label of `p` leaves only once the stack
shrank below the start. Every table entry keeps the stack at or below the start. -/
theorem cfg {p p' : Program} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (Qend : MachineData → Prop) (Ext : Int64 → MachineData → Prop)
    (hentries : ∀ l ∈ Program.labels p, l ∈ BlockEntries.labels)
    (hstack : ∀ s₀ l s, T l₀ s₀ → T l s → s.StackAtOrBelow s₀)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄
        blk.body
      ⦃ fun _ s => match blk.next with
          | some l' => T l' s ∧ var l' s ≤ n
          | none => Qend s;
        fun a s => Program.JumpTo p T var l n a s ∨
          (Ext a s ∧ ∀ l' ∈ Program.labels p, label l' = a → ∀ s₀, T l₀ s₀ → s₀.StackBelow s) ⦄)
    (hp : p = Directive.label l₀ :: p' := by rfl) (hnd : (Program.labels p).Nodup := by decide) :
    ⦃ fun s => T l₀ s ⦄ p ⦃ fun _ s => Qend s; Ext ⦄ := by
  refine ⟨fun s₀ hT₀ => ?_⟩
  show Program.wp p (fun st => Qend st.data) (fun st => Ext st.pc st.data) s₀
  rw [Program.wp_eq]
  intro H
  have hlink := H.embedding.isInfixAt
  have hK : ∀ l, Program.blockIdx p l ≤ (Program.view p).2.length := Program.blockIdx_le p
  have hcellOf : ∀ l, Program.fromLabel p l ≠ [] →
      p[p.length - (Program.fromLabel p l).length]? = some (Directive.label l) := by
    intro l hne
    have hdrop := Program.drop_fromLabel p l
    obtain ⟨t, rest, -, hfl, -, -⟩ := Program.fromLabel_split hnd hne
    conv at hdrop => rhs; rw [hfl]
    simpa [List.head?_drop] using congrArg List.head? hdrop
  have hne_of : ∀ l', (Program.blockAt p l').isSome → Program.fromLabel p l' ≠ [] := by
    intro l' hsome'
    obtain ⟨blk', hblk'⟩ := Option.isSome_iff_exists.mp hsome'
    rw [Program.fromLabel_block hnd hblk']
    exact List.cons_ne_nil _ _
  have hentry : ∀ l', (Program.blockAt p l').isSome → p.InternalTarget (label l') := fun l' hsome' =>
    ⟨l', hentries l' (Program.mem_labels.mpr (List.mem_of_getElem? (hcellOf l' (hne_of l' hsome')))),
      Program.mem_labels.mpr (List.mem_of_getElem? (hcellOf l' (hne_of l' hsome'))), rfl⟩
  have key : ∀ x : Label × MachineData, (Program.blockAt p x.1).isSome → T x.1 x.2 →
      While (·.pc ≠ H.embedding.endAddr)
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» fun st => Ext st.pc st.data))
        (fun st => Qend st.data)
        ⟨x.2, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p x.1).length))⟩ := by
    intro x
    induction x using (measure (Program.cfgMeasure p var)).wf.induction with
    | _ x ih =>
      obtain ⟨l, s⟩ := x
      intro hsome hT
      dsimp only at hsome hT ⊢
      have jump : ∀ l' s', (Program.blockAt p l').isSome → T l' s' →
          Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s) →
          While (·.pc ≠ H.embedding.endAddr)
            (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
              «continue» (p.ContinueOnInternalExit s₀ «continue» fun st => Ext st.pc st.data))
            (fun st => Qend st.data) ⟨s', label l'⟩ := by
        intro l' s' hsome' hT' hlt
        rw [Host.label_eq hlink (hcellOf l' (hne_of l' hsome'))]
        exact ih (l', s') hlt hsome' hT'
      have edge : ∀ l' s', Program.EdgeLt p var l (var l s) l' s' →
          Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s) := by
        intro l' s' hedge
        have hK' := hK l'
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
      obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hsome
      have htext := Program.fromLabel_block hnd hblk
      have hlen := congrArg List.length htext
      simp only [List.length_cons, List.length_append] at hlen
      have hdrop := Program.drop_fromLabel p l
      have hsuf : (Program.fromLabel p l).length ≤ p.length := by
        have := congrArg List.length hdrop
        simp only [List.length_drop] at this
        omega
      generalize hi : p.length - (Program.fromLabel p l).length = i at hdrop ⊢
      rw [htext] at hdrop
      have hbody : blk.body.IsInfixAt p (i + 1) :=
        ⟨blk.next.elim [] (Program.fromLabel p), by rw [← List.drop_drop, hdrop]; rfl⟩
      have hpi : p[i]? = some (.label l) := by
        have h0 := congrArg (·[0]?) hdrop
        simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using h0
      have hlab : Host.prog[H.embedding.start + i]? = some (.label l) := by
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hpi
        rw [List.isInfixAt_iff_getElem?.mp hlink i hlt, heq]
      have haddr : Host.addrOf (H.embedding.start + (i + 1)) = Host.addrOf (H.embedding.start + i) := by
        rw [← Nat.add_assoc, Host.addrOf_succ hlab, Host.label_size _ _ hlab]; simp
      rw [← haddr]
      refine Program.run_infix (o := i + 1) hbody (by omega) (Program.blockAt_noInternal hblk)
        ((hblocks l blk hblk (var l s)).1 s ⟨hT, rfl⟩) ?_ ?_
      · intro st hpc hnext
        cases hn : blk.next with
        | none =>
          simp only [hn] at hnext hlen
          refine While.stop ?_ hnext
          show ¬ st.pc ≠ Host.addrOf (H.embedding.start + p.length)
          rw [hpc]
          simp only [Option.elim, List.length_nil] at hlen
          intro hne
          exact hne (by congr 1; omega)
        | some l' =>
          simp only [hn] at hnext hlen
          obtain ⟨hT', hvar⟩ := hnext
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hblk hn
          simp only [Option.elim] at hlen
          have hst : st = ⟨st.data, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p l').length))⟩ := by
            cases st
            simp only [MachineState.mk.injEq, true_and] at hpc ⊢
            rw [hpc]
            congr 1
            omega
          rw [hst]
          refine ih (l', st.data) ?_ hsome' hT'
          have hK' := hK l'
          show Program.cfgMeasure p var (l', st.data) < Program.cfgMeasure p var (l, s)
          unfold Program.cfgMeasure
          dsimp only
          have hmul : var l' st.data * ((Program.view p).2.length + 1)
              ≤ var l s * ((Program.view p).2.length + 1) :=
            Nat.mul_le_mul_right _ hvar
          omega
      · rintro ⟨s', a⟩ (⟨l', hl', hsome', hT', hedge⟩ | ⟨hext, hnot⟩)
        · subst hl'
          unfold Program.ContinueOnInternalExit
          rw [if_pos ⟨hentry l' hsome', hstack s₀ l' s' hT₀ hT'⟩]
          exact jump l' s' hsome' hT' (edge l' s' hedge)
        · unfold Program.ContinueOnInternalExit
          rw [if_neg]
          · exact hext
          · rintro ⟨⟨l'', -, hl'', hla⟩, hown⟩
            exact hown (hnot l'' hl'' hla s₀ hT₀)
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
  have := key (l₀, s₀) h0 hT₀
  rwa [hfl, Nat.sub_self, Nat.add_zero] at this

/-- `cfg` at one state, in the goal form of `vcgen`. -/
theorem cfg_wp {p p' : Program} {l₀ : Label}
    (T : Label → MachineData → Prop) (var : Label → MachineData → Nat)
    (Qend : MachineData → Prop) (Ext : Int64 → MachineData → Prop)
    (hentries : ∀ l ∈ Program.labels p, l ∈ BlockEntries.labels)
    (hstack : ∀ s₀ l s, T l₀ s₀ → T l s → s.StackAtOrBelow s₀)
    (hblocks : ∀ l blk, Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T l s ∧ var l s = n ⦄
        blk.body
      ⦃ fun _ s => match blk.next with
          | some l' => T l' s ∧ var l' s ≤ n
          | none => Qend s;
        fun a s => Program.JumpTo p T var l n a s ∨
          (Ext a s ∧ ∀ l' ∈ Program.labels p, label l' = a → ∀ s₀, T l₀ s₀ → s₀.StackBelow s) ⦄)
    (s : MachineData) (hT : T l₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl) (hnd : (Program.labels p).Nodup := by decide) :
    ⊤ ⊑ WP.wp p (fun _ s => Qend s) Ext s :=
  fun _ => (cfg T var Qend Ext hentries hstack hblocks hp hnd).1 s hT

end Program.WP
