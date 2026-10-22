module

/-
The control-flow rule of the state wp. `Program.WP.cfg` proves the wp of a
program from one obligation per block of `Program.ForallBlocks`: an invariant
`I` gives the assertion at each `CfgLabel`, and a variant `var` orders the
edges between labelled blocks. A call steps by the callee's `CallSpec`, which
`callSpec_of_triple` derives from its body.
-/
public import Kraken.X64.WP.Instance
public import Kraken.Blocks
public import Kraken.SeparationMem

@[expose] public section

open Std.WP
open Lean.Order


/-! ## The text of a block -/

def Program.fromCfgLabel (p : Program) : CfgLabel → Program
  | .label l => Program.fromLabel p l
  | _ => []

theorem Program.firstLabel_ne_entry : ∀ bs : List (Label × Program), Program.firstLabel bs ≠ .entry
  | [] => nofun
  | (_, _) :: _ => nofun

theorem Program.flatMap_drop_view {p : Program} (hnd : (Program.labels p).Nodup) (j : Nat) :
    ((Program.view p).2.drop j).flatMap Program.blockCells
      = Program.fromCfgLabel p (Program.firstLabel ((Program.view p).2.drop j)) := by
  rw [Program.firstLabel_drop]
  cases hj : (Program.view p).2[j]? with
  | none =>
    rw [List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp hj)]
    rfl
  | some lb =>
    obtain ⟨l', b'⟩ := lb
    exact (Program.fromLabel_view hnd hj).symm

theorem Program.fromLabel_block {p : Program} (hnd : (Program.labels p).Nodup)
    {l : Label} {blk : Program.Block} (h : Program.blockAt p l = some blk) :
    Program.fromLabel p l = Directive.label l :: (blk.body ++ Program.fromCfgLabel p blk.next) := by
  obtain ⟨-, i, hi, hnext, -⟩ := Program.blockAtAux_spec h
  rw [Program.fromLabel_view hnd hi, Program.drop_flatMap_cons hi, hnext, Program.flatMap_drop_view hnd]

theorem Program.view_eq_entry {p : Program} (hnd : (Program.labels p).Nodup) :
    p = (Program.view p).1 ++ Program.fromCfgLabel p (Program.entryBlock p).next := by
  have h := Program.flatMap_drop_view hnd 0
  simp only [List.drop_zero] at h
  refine (Program.view_eq p).trans ?_
  rw [h]
  rfl

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

/-- The registers and memory blocks a callee may change. -/
structure Modifies where
  regs : List Reg64
  mem : List (BitVec 64 × Nat)

/-- `s'` agrees with `s` on the registers and the memory outside `m`. -/
def Modifies.Agree (m : Modifies) (s s' : MachineData) : Prop :=
  (∀ r, r ∉ m.regs → s'.regs.get64 r = s.regs.get64 r) ∧ Mem.UnchangedOutside m.mem s.dmem s'.dmem

theorem Modifies.Agree.reg {m : Modifies} {s s' : MachineData} (h : m.Agree s s') (r : Reg64)
    (hr : r ∉ m.regs) : s'.regs.get64 r = s.regs.get64 r := h.1 r hr
grind_pattern Modifies.Agree.reg => m.Agree s s', s'.regs.get64 r

@[grind =] theorem Modifies.agree_iff (m : Modifies) (s s' : MachineData) :
    m.Agree s s' ↔
      ((.rax ∈ m.regs ∨ s'.regs.get64 .rax = s.regs.get64 .rax)
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
      ∧ (.r15 ∈ m.regs ∨ s'.regs.get64 .r15 = s.regs.get64 .r15))
      ∧ Mem.UnchangedOutside m.mem s.dmem s'.dmem := by
  refine and_congr_left' ⟨fun h => ?_, fun h r hr => ?_⟩
  ·
    exact ⟨Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _),
      Classical.or_iff_not_imp_left.mpr (h _), Classical.or_iff_not_imp_left.mpr (h _)⟩
  · cases r <;> simp_all

namespace Program.WP

variable [Host] [FunDecls]

abbrev CallSpec (f : Label) (Pre : MachineData → Prop) (Post : MachineData → MachineData → Prop)
    (m : MachineData → Modifies) : Prop :=
  ∀ asz osz (Q : Unit → MachineData → Prop) (E : Int64 → MachineData → Prop),
    ⦃ fun s => (Mem.loadInt s.dmem (s.regs.get64 .rsp - 8#64) 8).isSome = true ∧ Pre s
        ∧ (∀ s', Post s s' → (m s).Agree s s' → Q () s') ⦄
      (Directive.instr (.regular asz osz (.call (.rel (.sub (.label f) .after_current_instruction)))))
    ⦃ Q; E ⦄

theorem MachineData.stackBelow_pushRa (s : MachineData) (ra : Int64) : (s.pushRa ra).StackBelow s := by
  simp only [MachineData.StackBelow, MachineData.pushRa, Reg64s.set64_rsp, Reg64s.get64_rsp,
    Int64.toBitVec_ofBitVec]
  generalize s.regs.rsp.toBitVec = x
  rw [show x - (x - 8#64) = 8#64 by bv_omega]
  decide

theorem callSpec_of_triple {f : Label} {g : Fragment} (hg : FunDecls.at (label f) = some g)
    {Pre : MachineData → Prop} {Post : MachineData → MachineData → Prop} {m : MachineData → Modifies}
    (hbody : ∀ s ra, ⦃ fun t => t = s.pushRa ra ∧ Pre s ⦄ g.prog
      ⦃ (fun _ _ => False); fun a t => a = ra ∧ Post s t ∧ (m s).Agree s t ⦄) :
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


end Program.WP

/-! ## The control-flow rule -/

def Program.Intercept [Host] (ls : List Label) (s₀ : MachineData)
    (I' : CfgLabel → Nat → Unit → MachineData → Prop) (E : Int64 → MachineData → Prop)
    (a : Int64) (s : MachineData) : Prop :=
  (∃ i l, ls[i]? = some l ∧ label l = a ∧ s.StackAtOrBelow s₀ ∧ I' (.label l) (i + 1) () s)
  ∨ (E a s ∧ ∀ l ∈ ls, label l = a → s₀.StackBelow s)

section
variable [Host] {ls : List Label} {s₀ s : MachineData} {I' : CfgLabel → Nat → Unit → MachineData → Prop}
  {E : Int64 → MachineData → Prop} {a : Int64}

theorem Program.Intercept.intro_label {i : Nat} {l : Label} (hl : ls[i]? = some l)
    (h : (s.StackAtOrBelow s₀ ∧ I' (.label l) (i + 1) () s) ∨ (E (label l) s ∧ s₀.StackBelow s)) :
    Program.Intercept ls s₀ I' E (label l) s :=
  h.imp (fun h => ⟨i, l, hl, rfl, h⟩) (fun ⟨hE, hb⟩ => ⟨hE, fun _ _ _ => hb⟩)

theorem Program.Intercept.intro
    (h : (s.StackAtOrBelow s₀ ∧ ∃ l, label l = a ∧ l ∈ ls ∧ I' (.label l) (ls.idxOf l + 1) () s)
      ∨ (E a s ∧ ∀ l ∈ ls, label l = a → s₀.StackBelow s)) :
    Program.Intercept ls s₀ I' E a s := by
  refine h.imp (fun ⟨hs, l, ha, hl, h⟩ => ?_) id
  have hi := List.idxOf_lt_length_of_mem hl
  exact ⟨_, l, by rw [List.getElem?_eq_getElem hi, List.getElem_idxOf hi], ha, hs, h⟩

theorem List.getElem?_cons_succ_of {α} {a b : α} {l : List α} {i : Nat} (h : l[i]? = some b) :
    (a :: l)[i + 1]? = some b :=
  h

macro_rules
  | `(grind| cfg_exit) =>
    `(grind| first
      ((apply Program.Intercept.intro_label);
        (repeat ((fail_if_success (apply List.getElem?_cons_zero)); (apply List.getElem?_cons_succ_of)));
        (apply List.getElem?_cons_zero))
      (apply Program.Intercept.intro)
      (skip))

theorem Program.Intercept.dispatch {p : Program} {C X : MachineState → Prop} {d : MachineData} {a : Int64}
    (h : Program.Intercept (Program.labels p) s₀ I' E a d)
    (hc : ∀ i l, (Program.labels p)[i]? = some l → label l = a → d.StackAtOrBelow s₀ →
      I' (.label l) (i + 1) () d → C ⟨d, a⟩)
    (hx : E a d → X ⟨d, a⟩) :
    p.ContinueOnInternalExit s₀ C X ⟨d, a⟩ := by
  unfold Program.ContinueOnInternalExit
  rcases h with ⟨i, l, hl, hla, hown, hI⟩ | ⟨hE, hext⟩
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨⟨l, List.mem_of_getElem? hl, hla⟩, hown⟩)]
    exact hc i l hl hla hown hI
  · rw [ite_eq_right_of_eq_false _ _ (eq_false fun ⟨⟨l, hl, hla⟩, hown⟩ => hown (hext l hl hla))]
    exact hx hE

theorem Program.labels_nodup_of_embeds {p : Program} [H : Embeds p] : (Program.labels p).Nodup :=
  Host.labels_nodup.sublist (H.embedding.isInfixAt.isInfix.sublist.filterMap _)

theorem Program.blockAt_noInternal {p : Program} {l : Label} {blk : Program.Block}
    (h : Program.blockAt p l = some blk) (a : Int64) : ¬ blk.body.InternalTarget a := by
  rintro ⟨l', hl', -⟩
  obtain ⟨-, i, hi, -, -⟩ := Program.blockAtAux_spec h
  have hfree := (Program.view_free p).2 _ (List.mem_of_getElem? hi) (.label l') (Program.mem_labels.mp hl')
  simp [Directive.isLabel] at hfree

theorem Program.entry_noInternal (p : Program) (a : Int64) : ¬ (Program.view p).1.InternalTarget a := by
  rintro ⟨l', hl', -⟩
  have hfree := (Program.view_free p).1 (.label l') (Program.mem_labels.mp hl')
  simp [Directive.isLabel] at hfree

end

namespace Program.WP

variable [Host] [FunDecls]

theorem cfg {p : Program} {E : Int64 → MachineData → Prop} {s₀ : MachineData}
    (I : CfgLabel → MachineData → Prop) (var : Label → MachineData → Nat)
    (hblocks : p.ForallBlocks fun blk => ∀ t, I blk.label t →
      let I' (b : CfgLabel) (j : Nat) (_ : Unit) (s : MachineData) :=
        I b s ∧ Program.Decreases var blk.label blk.idx t b j s
      WP.wp blk.body (I' blk.next (blk.idx + 1)) (Program.Intercept (Program.labels p) s₀ I' E) t)
    (hentry : I .entry s₀) :
    WP.wp p (fun _ => I .exit) E s₀ := by
  show Program.wp p (fun st => I .exit st.data) (fun st => E st.pc st.data) s₀
  rw [Program.wp_eq]
  intro H
  have hlink := H.embedding.isInfixAt
  have hnd : (Program.labels p).Nodup := Program.labels_nodup_of_embeds
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
  have edge : ∀ l s l' s', Program.Decreases var (.label l) (Program.blockIdx p l + 1) s
      (.label l') (Program.blockIdx p l' + 1) s' →
      Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s) := by
    intro l s l' s' hedge
    have hedge : var l' s' < var l s
        ∨ (var l' s' = var l s ∧ Program.blockIdx p l + 1 < Program.blockIdx p l' + 1) :=
      hedge
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
  have key : ∀ x : Label × MachineData, (Program.blockAt p x.1).isSome → I (.label x.1) x.2 →
      While (·.pc ≠ H.embedding.endAddr)
        (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
          «continue» (p.ContinueOnInternalExit s₀ «continue» fun st => E st.pc st.data))
        (fun st => I .exit st.data)
        ⟨x.2, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p x.1).length))⟩ := by
    intro x
    induction x using (measure (Program.cfgMeasure p var)).wf.induction with
    | _ x ih =>
      obtain ⟨l, s⟩ := x
      intro hsome hI
      dsimp only at hsome hI ⊢
      have jump : ∀ l' s', (Program.blockAt p l').isSome → I (.label l') s' →
          Program.cfgMeasure p var (l', s') < Program.cfgMeasure p var (l, s) →
          While (·.pc ≠ H.embedding.endAddr)
            (fun «continue» => Host.exe.StepOver (fun a => (FunDecls.at a).map fun f => f.prog.wp (fun _ => False))
              «continue» (p.ContinueOnInternalExit s₀ «continue» fun st => E st.pc st.data))
            (fun st => I .exit st.data) ⟨s', label l'⟩ := by
        intro l' s' hsome' hI' hlt
        rw [Host.label_eq hlink (hcellOf l' (hne_of l' hsome'))]
        exact ih (l', s') hlt hsome' hI'
      obtain ⟨blk, hblk⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hlab, i', hi', hnext', hidx⟩ := Program.blockAtAux_spec hblk
      have hbi : blk.idx = Program.blockIdx p l + 1 := by
        rw [hidx, Program.blockIdx_eq hnd hi', Nat.add_comm]
      have hb := hblocks.blockAt hblk
      rw [hlab, hbi] at hb
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
        ⟨Program.fromCfgLabel p blk.next, by rw [← List.drop_drop, hdrop]; rfl⟩
      have hpi : p[i]? = some (.label l) := by
        have h0 := congrArg (·[0]?) hdrop
        simpa only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] using h0
      have hlab' : Host.prog[H.embedding.start + i]? = some (.label l) := by
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hpi
        rw [List.isInfixAt_iff_getElem?.mp hlink i hlt, heq]
      have haddr : Host.addrOf (H.embedding.start + (i + 1)) = Host.addrOf (H.embedding.start + i) := by
        rw [← Nat.add_assoc, Host.addrOf_succ hlab', Host.label_size _ _ hlab']; simp
      rw [← haddr]
      refine Program.run_infix (o := i + 1) hbody (by omega) (Program.blockAt_noInternal hblk)
        (hb s hI) ?_ ?_
      · intro st hpc hnext
        cases hn : blk.next with
        | entry => exact absurd (hnext'.symm.trans hn) (Program.firstLabel_ne_entry _)
        | exit =>
          simp only [hn] at hnext hlen
          refine While.stop ?_ hnext.1
          show ¬ st.pc ≠ Host.addrOf (H.embedding.start + p.length)
          rw [hpc]
          simp only [Program.fromCfgLabel, List.length_nil] at hlen
          intro hne
          exact hne (by congr 1; omega)
        | label l' =>
          simp only [hn] at hnext hlen
          obtain ⟨hI', hdec⟩ := hnext
          obtain ⟨hsome', hidx'⟩ := Program.blockAt_next hnd hblk hn
          simp only [Program.fromCfgLabel] at hlen
          have hst : st = ⟨st.data, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p l').length))⟩ := by
            cases st
            simp only [MachineState.mk.injEq, true_and] at hpc ⊢
            rw [hpc]
            congr 1
            omega
          rw [hst]
          exact ih (l', st.data) (edge l s l' st.data (by rw [hidx']; exact hdec)) hsome' hI'
      · rintro ⟨d, a⟩ hst
        refine Program.Intercept.dispatch hst (fun j l' hl' hla _ hI' => ?_) id
        subst hla
        exact jump l' d (Program.isSome_blockAt_of_mem (List.mem_of_getElem? hl')) hI'.1
          (edge l s l' d (by rw [Program.blockIdx_eq_of_getElem? hnd hl']; exact hI'.2))
  have hq : (Program.view p).1.IsInfixAt p 0 := ⟨_, (Program.view_eq_entry hnd).symm⟩
  have hlen0 := congrArg List.length (Program.view_eq_entry hnd)
  simp only [List.length_append] at hlen0
  refine Program.run_infix (o := 0) hq (by omega) (Program.entry_noInternal p)
    (hblocks.entry s₀ hentry) ?_ ?_
  · intro st hpc hnext
    simp only [Program.entryBlock] at hnext hlen0
    cases hv : (Program.view p).2 with
    | nil =>
      simp only [hv, Program.firstLabel, Program.fromCfgLabel, List.length_nil] at hnext hlen0
      refine While.stop ?_ hnext.1
      show ¬ st.pc ≠ Host.addrOf (H.embedding.start + p.length)
      rw [hpc]
      intro hne
      exact hne (by congr 1; omega)
    | cons lb rest =>
      obtain ⟨l', b'⟩ := lb
      simp only [hv, Program.firstLabel, Program.fromCfgLabel] at hnext hlen0
      have hsome' : (Program.blockAt p l').isSome := by
        have hndv : ((Program.view p).2.map (·.1)).Nodup := by rwa [← Program.labels_view]
        have h0 : (Program.view p).2[0]? = some (l', b') := by rw [hv]; rfl
        show (Program.blockAtAux 1 (Program.view p).2 l').isSome = true
        rw [Program.blockAtAux_of_getElem hndv h0]
        rfl
      have hst : st = ⟨st.data, Host.addrOf (H.embedding.start + (p.length - (Program.fromLabel p l').length))⟩ := by
        cases st
        simp only [MachineState.mk.injEq, true_and] at hpc ⊢
        rw [hpc]
        congr 1
        omega
      rw [hst]
      exact key (l', st.data) hsome' hnext.1
  · rintro ⟨d, a⟩ hst
    refine Program.Intercept.dispatch hst (fun j l' hl' hla _ hI' => ?_) id
    subst hla
    have hsome' := Program.isSome_blockAt_of_mem (List.mem_of_getElem? hl')
    rw [Host.label_eq hlink (hcellOf l' (hne_of l' hsome'))]
    exact key (l', d) hsome' hI'.1

end Program.WP
