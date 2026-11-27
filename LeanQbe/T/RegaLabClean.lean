module

public import LeanQbe.T.RegaLemmas3a
public import LeanQbe.T.RegaLemmasZero
public import LeanQbe.T.RegaLemmasRemat

/-!
# Structural Label-Cleanliness & Label-Bounds Proofs (`T.RegaLabClean`)

* `NoLab` lemmas (`*_clean`) for `execMove`, `stepPre`, `shuffle`, `lowerOp`, `lowerLoad`,
  `lowerStore`, and prologue/epilogue helpers.
* Structural label bounds (`LabelClean`, `lname_inj`, `lowerExpr_labels`/`lowerBlocks_labels`,
  `lowerFn_labelsUnique`, `lowerFn_label_mem`, `lowerExpr_nv_le`, `lowerBlocks_nv_le`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

section Labels
variable {I : Isa}

theorem NoLab.nil : NoLab I [] := fun _ h => nomatch h

theorem NoLab.append {a b : List I.Directive} (ha : NoLab I a) (hb : NoLab I b) :
    NoLab I (a ++ b) := fun l h => (List.mem_append.mp h).elim (ha l) (hb l)

/-! ### Label names -/

private def digF (a : Nat) (c : Char) : Nat := a * 10 + (c.toNat - 48)

private theorem natDigits_fold : ∀ (fuel n : Nat) (acc : List Char), n < fuel →
    (natDigits fuel n acc).foldl digF 0 = acc.foldl digF n
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, n, acc, h => by
    have hc : ∀ d < 10, (Char.ofNat (48 + d)).toNat - 48 = d := by decide
    simp only [natDigits]
    split
    · next h10 =>
      rw [natDigits_fold fuel (n / 10) _ (by have := Nat.le_of_ble_eq_true h10; omega)]
      simp only [List.foldl, digF, hc _ (Nat.mod_lt _ (by decide))]
      rw [Nat.div_add_mod' n 10]
    · next h10 =>
      have : n < 10 := by simpa [Nat.ble_eq] using h10
      simp only [List.foldl, digF, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt this, hc n this]

theorem lname_inj {fn : Sym} {a b : Nat} (h : lname fn a = lname fn b) : a = b := by
  have h' := congrArg String.toList h
  simp only [lname, String.toList_append, String.toList_ofList, List.append_assoc] at h'
  have h'' := List.append_cancel_left (List.append_cancel_left (List.append_cancel_left h'))
  have := congrArg (List.foldl digF 0) h''
  rwa [natDigits_fold _ _ _ (Nat.lt_succ_self a),
    natDigits_fold _ _ _ (Nat.lt_succ_self b)] at this

theorem lname_ne {fn : Sym} {a : Nat} : lname fn a ≠ fn := fun h => by
  have := congrArg String.length h
  simp only [lname, String.length_append] at this
  have : ".L".length = 2 := rfl
  omega

/-- Labels `lname fn j` with `a ≤ j < b`. -/
def lrange (fn : Sym) (a b : Nat) (l : Sym) : Prop := ∃ j, a ≤ j ∧ j < b ∧ l = lname fn j

theorem lrange_disj {fn : Sym} {a b a' b' : Nat} {l : Sym} (h : lrange fn a b l)
    (h' : lrange fn a' b' l) (hd : b ≤ a' ∨ b' ≤ a) : False := by
  obtain ⟨j, h1, h2, rfl⟩ := h; obtain ⟨j', h1', h2', he⟩ := h'
  have := lname_inj he; omega

theorem lrange_mono {fn : Sym} {a b a' b' : Nat} {l : Sym} (h : lrange fn a b l) (ha : a' ≤ a)
    (hb : b ≤ b') : lrange fn a' b' l := by
  obtain ⟨j, h1, h2, rfl⟩ := h; exact ⟨j, by omega, by omega, rfl⟩

/-! ### Label-range invariant -/

/-- Equal labels of `c` sit at equal positions, and all labels satisfy `S`. -/
def LabOk (I : Isa) (S : Sym → Prop) (c : List I.Directive) : Prop :=
  (∀ (i j : Nat) l, c[i]? = some (I.frame.label l) → c[j]? = some (I.frame.label l) → i = j) ∧
  ∀ l, I.frame.label l ∈ c → S l

theorem LabOk.clean {S : Sym → Prop} {c : List I.Directive} (h : NoLab I c) : LabOk I S c :=
  ⟨fun _ _ l hi _ => absurd (List.mem_of_getElem? hi) (h l), fun l hl => absurd hl (h l)⟩

theorem LabOk.mono {S S' : Sym → Prop} {c : List I.Directive} (h : LabOk I S c)
    (hs : ∀ l, S l → S' l) : LabOk I S' c := ⟨h.1, fun l hl => hs l (h.2 l hl)⟩

theorem LabOk.single (hcl : LabelClean I) (l : Sym) : LabOk I (· = l) [I.frame.label l] := by
  refine ⟨fun i j l' hi hj => ?_, fun l' hl => hcl.label_inj _ _ (List.mem_singleton.mp hl)⟩
  cases i <;> cases j <;> simp_all

theorem LabOk.append {S₁ S₂ S : Sym → Prop} {c₁ c₂ : List I.Directive} (h₁ : LabOk I S₁ c₁)
    (h₂ : LabOk I S₂ c₂) (hd : ∀ l, S₁ l → S₂ l → False) (hs : ∀ l, S₁ l ∨ S₂ l → S l) :
    LabOk I S (c₁ ++ c₂) := by
  refine ⟨fun i j l hi hj => ?_, fun l hl => hs l ((List.mem_append.mp hl).imp (h₁.2 l) (h₂.2 l))⟩
  rw [List.getElem?_append] at hi hj
  split at hi <;> split at hj
  · exact h₁.1 i j l hi hj
  · exact (hd l (h₁.2 l (List.mem_of_getElem? hi)) (h₂.2 l (List.mem_of_getElem? hj))).elim
  · exact (hd l (h₁.2 l (List.mem_of_getElem? hj)) (h₂.2 l (List.mem_of_getElem? hi))).elim
  · have := h₂.1 _ _ l hi hj; omega

theorem LabOk.pre {S : Sym → Prop} {a c : List I.Directive} (ha : NoLab I a) (h : LabOk I S c) :
    LabOk I S (a ++ c) :=
  (LabOk.clean (S := fun _ => False) ha).append h
    (fun _ h _ => h) (fun _ h => h.elim False.elim id)

variable (hcl : LabelClean I)
include hcl

private theorem execMovi_clean (st : SymState I) (deadHint : Bool) (d : I.Reg) (c : BitVec 64) :
    NoLab I (execMovi I st deadHint d c).1 := by
  unfold execMovi
  split
  · rename_i fn hmd
    split
    · exact hcl.moviDeadFlags fn d c hmd
    · exact hcl.movi d c
  · exact hcl.movi d c

theorem execMove_clean {nslots : Nat} {saved : List I.Reg} {mv : I.Move} {st st' : SymState I}
    {deadHint : Bool} {c : List I.Directive}
    (h : execMove I nslots saved mv st deadHint = some (c, st')) : NoLab I c := by
  cases mv <;> simp only [execMove] at h <;> (repeat' split at h) <;>
    first | (simp at h; done) | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl,
      -⟩ := h)
  all_goals first
    | exact hcl.mov _ _
    | exact execMovi_clean hcl _ _ _ _
    | exact hcl.slotLd _ _
    | exact hcl.slotSt _ _
    | exact hcl.setcc _ _
    | exact hcl.vmov _ _ _
    | exact hcl.vslotLd _ _ _
    | exact hcl.vslotSt _ _ _
    | exact hcl.vmovi _ _ _ _ ‹_›

theorem execMoves_clean {nslots : Nat} {saved : List I.Reg} {deadHint : Bool} :
    ∀ {mvs : List I.Move} {st st' : SymState I} {c : List I.Directive},
    execMoves I nslots saved mvs st deadHint = some (c, st') → NoLab I c
  | [], _, _, _, h => by
    simp only [execMoves, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact NoLab.nil
  | _ :: _, _, _, _, h => by
    simp only [execMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨c1, st1⟩, h1, ⟨c2, st2⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he; rw [← he.1]
    exact (execMove_clean hcl h1).append (execMoves_clean h2)

theorem stepPre_clean {h : I.Hints} {ip : Nat} {st st' : SymState I} {c : List I.Directive}
    (hs : stepPre I h ip st = some (c, st')) : NoLab I c := by
  simp only [stepPre] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact NoLab.nil
  · obtain ⟨⟨mc, st1⟩, h1, he⟩ := Option.map_eq_some_iff.mp hs
    split at he <;> simp only [Prod.mk.injEq] at he <;> rw [← he.1]
    · exact (execMoves_clean hcl h1).append hcl.clearFlags
    · exact execMoves_clean hcl h1

theorem execShufMoves_clean {nslots : Nat} {saved : List I.Reg} {deadHint : Bool} :
    ∀ {mvs : List (ShufMove I.Reg I.VReg I.Cond)} {st st' : SymState I} {c : List I.Directive},
    execShufMoves I nslots saved mvs st deadHint = some (c, st') → NoLab I c
  | [], _, _, _, h => by
    simp only [execShufMoves, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact NoLab.nil
  | mv :: _, _, _, _, h => by
    simp only [execShufMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨c1, st1⟩, h1, ⟨c2, st2⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he; rw [← he.1]
    refine NoLab.append ?_ (execShufMoves_clean h2)
    cases mv with
    | base _ => exact execMove_clean hcl h1
    | rematAdd _ _ _ _ =>
      simp only [execShufMove] at h1
      repeat' (split at h1 <;> try (simp at h1; done))
      obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨_, hrm, hp⟩ := Option.map_eq_some_iff.mp h1
      simp only [Prod.mk.injEq] at hp; rw [← hp.1]; exact rematAddImm64_clean hcl hrm

theorem shuffle_clean {nslots : Nat} {saved : List I.Reg} {st st' : SymState I}
    {tgts : List (SymArg × I.Loc)} {deadHint : Bool} {c : List I.Directive}
    (hs : shuffle I nslots saved st tgts deadHint = some (c, st')) : NoLab I c := by
  simp only [shuffle] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact NoLab.nil
  · split at hs
    · simp at hs
    · split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rw [← hs.1]; exact execShufMoves_clean hcl ‹_›
      · simp at hs

theorem canonAbiCode_clean : ∀ {ts : List Ty} (locs : Tup (AbiReg I.Reg I.VReg) ts)
    (sk : List Bool), NoLab I (canonAbiCode I locs sk)
  | [], (), _ => NoLab.nil
  | _ :: _, (.gpr _, locs), sk => by
    refine NoLab.append ?_ (canonAbiCode_clean locs sk.tail)
    split
    · exact NoLab.nil
    · exact hcl.canonAbi _ _
  | _ :: _, (.vec _, locs), sk => canonAbiCode_clean locs sk.tail

theorem restoreCsList_clean : ∀ (base : Nat) (rs : List I.Reg), NoLab I (restoreCsList I base rs)
  | _, [] => NoLab.nil
  | _, _ :: rs => (hcl.slotLd _ _).append (restoreCsList_clean _ rs)

theorem saveCsList_clean : ∀ (base : Nat) (rs : List I.Reg), NoLab I (saveCsList I base rs)
  | _, [] => NoLab.nil
  | _, _ :: rs => (hcl.slotSt _ _).append (saveCsList_clean _ rs)

theorem restoreCs_clean (base : Nat) (rs : List I.Reg) : NoLab I (restoreCs I base rs) := by
  cases rs with
  | nil => exact NoLab.nil
  | cons r rs' =>
    dsimp only [restoreCs]
    cases hfn : I.frame.restoreRegs? with
    | none => exact restoreCsList_clean hcl base (r :: rs')
    | some fn => exact hcl.restoreRegs fn base (r :: rs') hfn

theorem saveCs_clean (base : Nat) (rs : List I.Reg) : NoLab I (saveCs I base rs) := by
  cases rs with
  | nil => exact NoLab.nil
  | cons r rs' =>
    dsimp only [saveCs]
    cases hfn : I.frame.saveRegs? with
    | none => exact saveCsList_clean hcl base (r :: rs')
    | some fn => exact hcl.saveRegs fn base (r :: rs') hfn

omit hcl in
private theorem tryGpr_some {st : SymState I} {α : Type} {sa : SymArg}
    {k : I.Reg → Option α} {res : α} (h : tryGpr I st.regs sa k = some res) :
    ∃ r, k r = some res := by
  obtain ⟨⟨_, rl⟩, -, hb⟩ := List.exists_of_findSome?_eq_some h
  cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb

private theorem tryTestMemVar_clean {st : SymState I} {neg : Bool} {w x : Nat}
    {other : Arg VNat (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive}
    {cl : FlagMask} (h : tryTestMemVar I st neg w x other pd = some (c, cl)) : NoLab I c := by
  unfold tryTestMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩; cases tm with
    | bits _ =>
      simp only [hmd] at h; split at h <;> try (simp at h; done)
      obtain ⟨_, h1⟩ := tryAddr_some h; obtain ⟨_, h2⟩ := tryArg_some h1
      exact hcl.testMem _ _ _ _ _ _ _ h2
    | _ => simp [hmd] at h

private theorem tryCmpMemVar_clean {st : SymState I} {co : CmpOp} {w x : Nat}
    {other : Arg VNat (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive}
    {cl : FlagMask} (h : tryCmpMemVar I st co w x other pd = some (c, cl)) : NoLab I c := by
  unfold tryCmpMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩; cases tm with
    | bits _ =>
      simp only [hmd] at h; split at h <;> try (simp at h; done)
      obtain ⟨_, h1⟩ := tryAddr_some h; obtain ⟨_, h2⟩ := tryArg_some h1
      exact hcl.cmpMem _ _ _ _ _ _ _ h2
    | _ => simp [hmd] at h

private theorem tryTestFuse_clean {st : SymState I} {neg : Bool} {w t : Nat}
    {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    (h : tryTestFuse I st neg w t pd = some (c, cl)) : NoLab I c := by
  unfold tryTestFuse at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | andVarImm _ _ _ =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h2
      · exact tryTestMemVar_clean hcl h1
      · obtain ⟨_, hk⟩ := tryArg_some h2; exact hcl.testOp _ _ _ _ _ _ _ hk
    | andVarVar _ _ _ =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h
      · exact tryTestMemVar_clean hcl h1
      rcases orElse_eq_some h with h2 | h3
      · exact tryTestMemVar_clean hcl h2
      · obtain ⟨_, hk1⟩ := tryArg_some h3
        obtain ⟨_, hk2⟩ := tryArg_some hk1
        exact hcl.testOp _ _ _ _ _ _ _ hk2
    | _ => simp [hdef] at h

omit hcl in
private theorem cmpMemRes_fst {st : SymState I} {co : CmpOp} {w : Nat}
    {a b : SymArg} {pd : PDst I.Reg I.VReg I.Cond .bool} {d c : List I.Directive}
    {cl cl' : FlagMask} {fl : Option FlagFact} {ex : Option I.Cond}
    (h : cmpMemRes I st co w a b pd d cl = (c, cl', fl, ex)) : d = c := by
  unfold cmpMemRes at h; split at h <;> (simp only [Prod.mk.injEq] at h; exact h.1)

private theorem cmpOpEmptyScr_clean {vh : VariantHint} {co : CmpOp} {w : Nat}
    {pa pb : PArg I.Reg I.VReg I.Cond (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool}
    {c : List I.Directive} {cl : FlagMask}
    (h : cmpOpEmptyScr I vh co w pa pb pd = some (c, cl)) : NoLab I c := by
  unfold cmpOpEmptyScr at h
  cases hfn : I.gpr.opScr? with
  | some fn =>
    rw [hfn] at h; dsimp only at h
    obtain ⟨⟨_, _, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp h
    cases he; exact hcl.opScr fn _ _ _ _ _ _ _ _ hfn hop
  | none => rw [hfn] at h; exact hcl.op _ _ _ _ _ _ h

private theorem tryWidenZextCmp_clean {st : SymState I} {vh : VariantHint} {co : CmpOp}
    {w : Nat} {a b : Arg VNat (.bits w)} {pd : PDst I.Reg I.VReg I.Cond .bool}
    {c : List I.Directive} {cl : FlagMask} {fl : Option FlagFact} {ex : Option I.Cond}
    {iz : Bool} (h : tryWidenZextCmp I st vh co w a b pd = some (c, cl, fl, ex, iz)) :
    NoLab I c := by
  unfold tryWidenZextCmp at h; split at h; · simp at h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp h
  simp only [Prod.mk.injEq] at he; rw [← he.1]; exact cmpOpEmptyScr_clean hcl hop

private theorem shiftCmpGo_clean {st : SymState I} {co : CmpOp} {w x y : Nat}
    {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask} {ls : Bool}
    (h : shiftCmpGo I st co w x y pd = some (c, cl, ls)) : NoLab I c := by
  unfold shiftCmpGo at h
  rcases orElse_eq_some h with h' | h' <;>
  · obtain ⟨_, -, h'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨_, -, h'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨_, -, h'⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨⟨_, _⟩, hsc, he⟩ := Option.map_eq_some_iff.mp h'
    rcases he with ⟨rfl, rfl, rfl⟩; exact hcl.shiftCmp _ _ _ _ _ _ _ _ _ _ hsc

private theorem tryExtCmp_clean {st : SymState I} {vh : VariantHint} {co : CmpOp} {w t : Nat}
    {ci : BitVec w} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    {fl : Option FlagFact} {ex : Option I.Cond} {iz : Bool}
    (h : tryExtCmp I st vh co w t ci pd = some (c, cl, fl, ex, iz)) : NoLab I c := by
  unfold tryExtCmp at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | sextVar mw _ x | zextVar mw _ x =>
      simp only [hdef] at h; split at h; · simp at h
      rcases orElse_eq_some h with h1 | h2
      · cases hmd : st.memDefs.find? x with
        | none => simp [hmd] at h1
        | some p =>
          rcases p with ⟨tm, addr⟩
          cases tm with
          | bits _ =>
            simp only [hmd] at h1; split at h1 <;> try (simp at h1; done)
            obtain ⟨_, hk⟩ := tryAddr_some h1
            obtain ⟨⟨c0, cl0⟩, hcm, he⟩ := Option.map_eq_some_iff.mp hk
            simp only [Prod.mk.injEq] at he
            have hce : c0 = c := by rw [← he.1]; exact cmpMemRes_fst rfl
            rw [← hce]; exact hcl.cmpMem _ _ _ _ _ _ _ hcm
          | _ => simp [hmd] at h1
      · split at h2 <;> try (simp at h2; done)
        rcases orElse_eq_some h2 with hwz | h2
        · exact tryWidenZextCmp_clean hcl hwz
        · obtain ⟨_, hk⟩ := tryGpr_some h2
          obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk
          simp only [Prod.mk.injEq] at he; rw [← he.1]; exact cmpOpEmptyScr_clean hcl hop
    | _ => simp [hdef] at h

private theorem tryFuseCmp_clean {st : SymState I} {vh : VariantHint} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts}
    {c : List I.Directive} {cl : FlagMask} {fl : Option FlagFact} {ex : Option I.Cond} {iz : Bool}
    (h : tryFuseCmp I st vh code args dsts = some (c, cl, fl, ex, iz)) : NoLab I c := by
  cases code with
  | cmp _ ty mty _ =>
    cases ty with
    | bits _ =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
        unfold tryFuseCmp at h; dsimp only at h
        split at h; · simp at h
        rcases orElse_eq_some h with ht | h
        · split at ht
          · obtain ⟨⟨_, _⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
            simp only [Prod.mk.injEq] at he; rw [← he.1]
            cases a with
            | var _ =>
              cases b with
              | imm _ =>
                dsimp only at ht'
                split at ht' <;> first | exact tryTestFuse_clean hcl ht' | simp at ht'
              | var _ => simp at ht'
            | imm _ =>
              cases b with
              | var _ =>
                dsimp only at ht'
                split at ht' <;> first | exact tryTestFuse_clean hcl ht' | simp at ht'
              | imm _ => simp at ht'
          · simp at ht
        rcases orElse_eq_some h with he | hm
        · cases a <;> cases b <;> first | exact tryExtCmp_clean hcl he | simp at he
        · rcases orElse_eq_some hm with hm | hsw
          · rcases orElse_eq_some hm with hm' | hm' <;>
            · cases a <;> cases b <;> try (simp at hm'; done)
              all_goals
                obtain ⟨⟨c0, _⟩, hcmv, hmap⟩ := Option.map_eq_some_iff.mp hm'
                simp only [Prod.mk.injEq] at hmap
                have hce : c0 = c := by
                  rw [← hmap.1]; split <;> first | exact cmpMemRes_fst rfl | rfl
                subst hce; exact tryCmpMemVar_clean hcl hcmv
          · rcases orElse_eq_some hsw with hs | hwz
            · cases a <;> cases b <;> try (simp at hs; done)
              obtain ⟨⟨_, _, _⟩, hgo, he⟩ := Option.map_eq_some_iff.mp hs
              simp only [Prod.mk.injEq] at he; rw [← he.1]
              exact shiftCmpGo_clean hcl hgo
            · exact tryWidenZextCmp_clean hcl hwz
      | _ => simp [tryFuseCmp] at h
    | _ => simp [tryFuseCmp] at h
  | _ => simp [tryFuseCmp] at h

private theorem tryLoadSext_clean {st : SymState I} {vh : VariantHint} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts}
    {c : List I.Directive} {cl : FlagMask}
    (h : tryLoadSext I st vh code args dsts = some (c, cl)) : NoLab I c := by
  cases code <;> try (simp [tryLoadSext] at h; done)
  rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
  cases a with
  | imm _ => simp [tryLoadSext] at h
  | var x =>
    cases d0 with
    | vec _ => simp [tryLoadSext] at h
    | gpr rd =>
      simp only [tryLoadSext] at h
      cases hmd : st.memDefs.find? x with
      | none => simp [hmd] at h
      | some p =>
        rcases p with ⟨tm, addr⟩
        cases tm with
        | bits w' =>
          simp only [hmd] at h
          split at h
          · rcases orElse_eq_some h with h1 | h1
            · obtain ⟨_, h2⟩ := tryAddr_some h1; exact hcl.loadSext _ _ _ _ _ _ h2
            · obtain ⟨_, _, _, _, h2⟩ := tryAddrZext_some h1
              exact hcl.loadSextZextIdx _ _ _ _ _ _ _ _ _ h2
          · simp at h
        | _ => simp [hmd] at h

private theorem tryTestSlot_clean {h' : I.Hints} {st : SymState I} {neg : Bool} {n t : Nat}
    {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    (h : tryTestSlot I h' st neg n t pd = some (c, cl)) : NoLab I c := by
  unfold tryTestSlot at h
  split at h; · simp at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | andVarImm _ _ _ =>
      simp only [hdef] at h
      split at h
      · obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h
        exact hcl.testMem _ _ _ _ _ _ _ hk
      · simp at h
    | andVarVar _ _ _ =>
      simp only [hdef] at h
      split at h
      · rcases orElse_eq_some h with h1 | h1 <;>
          (obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h1;
           obtain ⟨_, hk'⟩ := tryArg_some hk; exact hcl.testMem _ _ _ _ _ _ _ hk')
      · simp at h
    | _ => simp [hdef] at h

private theorem tryExtSlot_clean {h' : I.Hints} {st : SymState I} {co : CmpOp} {n t : Nat}
    {ci : BitVec n} {pd : PDst I.Reg I.VReg I.Cond .bool} {c : List I.Directive} {cl : FlagMask}
    (h : tryExtSlot I h' st co n t ci pd = some (c, cl)) : NoLab I c := by
  unfold tryExtSlot at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | sextVar _ _ _ | zextVar _ _ _ =>
      simp only [hdef] at h
      split at h
      · obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h
        exact hcl.cmpMem _ _ _ _ _ _ _ hk
      · simp at h
    | _ => simp [hdef] at h

private theorem trySlotOp_clean {h' : I.Hints} {st : SymState I} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts}
    {c : List I.Directive} {cl : FlagMask} {iz z : Bool} {fl : Option FlagFact} {ex : Option I.Cond}
    (h : trySlotOp I h' st code args dsts = some (c, cl, iz, z, fl, ex)) : NoLab I c := by
  cases code with
  | cmp _ ty mty _ =>
    cases ty with
    | bits _ =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
        unfold trySlotOp at h; dsimp only at h
        split at h; · simp at h
        obtain ⟨⟨c1, cl1, fl1, ex1, iz1⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        rcases orElse_eq_some hs with ht | hs
        · split at ht
          · obtain ⟨⟨_, _⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
            simp only [Prod.mk.injEq] at he; rw [← he.1]
            cases a with
            | var _ =>
              cases b with
              | imm _ =>
                dsimp only at ht'
                split at ht' <;> first | exact tryTestSlot_clean hcl ht' | simp at ht'
              | var _ => simp at ht'
            | imm _ =>
              cases b with
              | var _ =>
                dsimp only at ht'
                split at ht' <;> first | exact tryTestSlot_clean hcl ht' | simp at ht'
              | imm _ => simp at ht'
          · simp at ht
        rcases orElse_eq_some hs with he' | hm
        · cases a <;> cases b <;> try (simp at he'; done)
          all_goals
            obtain ⟨⟨_, _⟩, he'', hmap⟩ := Option.map_eq_some_iff.mp he'
            simp only [extCmpMemRes, Prod.mk.injEq] at hmap; rw [← hmap.1]
            exact tryExtSlot_clean hcl he''
        · split at hm; · simp at hm
          rcases orElse_eq_some hm with h' | h' <;>
          · cases a <;> cases b <;> try (simp at h'; done)
            all_goals
              obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h'
              obtain ⟨_, hk'⟩ := tryArg_some hk
              obtain ⟨⟨c0, _⟩, hcm, hmap⟩ := Option.map_eq_some_iff.mp hk'
              simp only [Prod.mk.injEq] at hmap
              have hce : c0 = c1 := by
                rw [← hmap.1]; split <;> first | exact cmpMemRes_fst rfl | rfl
              subst hce; exact hcl.cmpMem _ _ _ _ _ _ _ hcm
      | _ => simp [trySlotOp] at h
    | _ => simp [trySlotOp] at h
  | add ty | sub ty | mul ty | and ty | or ty | xor ty =>
    cases ty with
    | bits _ =>
      rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
      cases d0 with
      | vec _ => simp [trySlotOp] at h
      | gpr _ =>
        unfold trySlotOp tryAluSlot at h; dsimp only at h
        split at h; · simp at h
        obtain ⟨⟨_, _, _⟩, hs, he⟩ := Option.map_eq_some_iff.mp h; cases he
        obtain ⟨⟨_, _⟩, hs', he0⟩ := Option.map_eq_some_iff.mp hs; cases he0
        rcases orElse_eq_some hs' with h1 | h2
        · cases a <;> try simp at h1
          obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h1
          obtain ⟨_, hk'⟩ := tryArg_some hk; exact hcl.aluMem _ _ _ _ _ _ _ _ hk'
        · cases b <;> try simp at h2
          obtain ⟨_, _, hk⟩ := Option.bind_eq_some_iff.mp h2
          obtain ⟨_, hk'⟩ := tryArg_some hk; exact hcl.aluMem _ _ _ _ _ _ _ _ hk'
    | _ => simp [trySlotOp] at h
  | _ => simp [trySlotOp] at h

private theorem tryLeaArith_clean {st : SymState I} {sig : List Ty}
    {args : Tup (Arg VNat) sig} {c : List I.Directive} {cl : FlagMask} {z : Bool} :
    ∀ {ts : List Ty} {code : OpCode sig ts} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts},
    tryLeaArith I st code args dsts = some (c, cl, z) → NoLab I c
  | [.bits w], _, (.gpr _, ()), htl => by
    unfold tryLeaArith at htl; dsimp only at htl
    rcases orElse_eq_some htl with htl | hsa
    case inr => exact tryShiftAlu_clean hcl hsa
    rcases orElse_eq_some htl with htl | hzext
    · obtain ⟨_, -, htl⟩ := Option.bind_eq_some_iff.mp htl
      obtain ⟨_, -, htl⟩ := Option.bind_eq_some_iff.mp htl
      obtain ⟨_, -, htl⟩ := Option.bind_eq_some_iff.mp htl
      obtain ⟨⟨_, _⟩, hlea, heq⟩ := Option.map_eq_some_iff.mp htl; cases heq
      exact hcl.leaArith _ _ _ _ _ _ _ _ hlea
    · by_cases h64 : w = 64
      · subst h64; dsimp only [tryLeaArithZext] at hzext
        obtain ⟨_, -, hzext⟩ := Option.bind_eq_some_iff.mp hzext
        obtain ⟨_, -, hzext⟩ := Option.bind_eq_some_iff.mp hzext
        obtain ⟨_, -, hzext⟩ := Option.bind_eq_some_iff.mp hzext
        obtain ⟨⟨_, _⟩, hlea, heq⟩ := Option.map_eq_some_iff.mp hzext; cases heq
        exact hcl.leaArithZext _ _ _ _ _ _ _ hlea
      · simp only [tryLeaArithZext] at hzext; split at hzext <;> simp_all
  | [], _, _, htl | [_], _, (.vec _, ()), htl | [_], _, (.flag _, ()), htl
  | .bool :: [], _, _, htl | .float _ :: [], _, _, htl | .pair _ _ :: [], _, _, htl
  | _ :: _ :: _, _, _, htl => by simp [tryLeaArith] at htl

private theorem tryReuseFlagCmp_clean {st : SymState I} {sig ts : List Ty}
    {code : OpCode sig ts} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {c : List I.Directive} {cl : FlagMask}
    {fl : Option FlagFact} {ex : Option I.Cond} {iz : Bool} {scr : List (I.Reg × BitVec 64)}
    (h : tryReuseFlagCmp I st code args dsts = some (c, cl, fl, ex, iz, scr)) : NoLab I c := by
  cases hstf : st.flags with
  | none => simp [tryReuseFlagCmp, hstf] at h
  | some ff =>
    cases ff; cases code <;> try (simp [tryReuseFlagCmp, hstf] at h; done)
    rename_i co ty mty hm
    cases ty <;> cases mty <;> try (simp [tryReuseFlagCmp, hstf] at h; done)
    rcases args with ⟨a, b, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    simp only [tryReuseFlagCmp, hstf] at h
    obtain ⟨⟨_, _, _⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h; · simp at h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases pd with
    | vec _ => simp at h
    | flag _ =>
      simp only at h; split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact NoLab.nil
      · simp at h
    | gpr _ =>
      obtain ⟨⟨_, _, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he; rw [← he.1]; exact lowerOpScr_clean hcl hop

private theorem lowerOpBody_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {ts : List Ty}
    {op : Op VNat ts} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {c : List I.Directive}
    (hl : lowerOpBody I h nv ip st op dsts = some (c, st')) :
    NoLab I c := by
  unfold lowerOpBody at hl
  split at hl
  · simp only [Option.some.injEq, Prod.mk.injEq] at hl
    rcases hl with ⟨rfl, -⟩; exact NoLab.nil
  obtain ⟨⟨c', cl, iv, _iz, _z, _fl, _ex, _scr⟩, hp, he⟩ := Option.map_eq_some_iff.mp hl
  cases he
  rcases orElse_eq_some hp with hreuse | hp
  · obtain ⟨⟨_, _, _, _, _, _⟩, hr, he⟩ := Option.map_eq_some_iff.mp hreuse; cases he
    rcases orElse_eq_some hr with hr | hr <;> exact tryReuseFlagCmp_clean hcl hr
  rcases orElse_eq_some hp with hfuse | hp
  · obtain ⟨⟨_, _, _, _, _⟩, hfc, he⟩ := Option.map_eq_some_iff.mp hfuse; cases he
    exact tryFuseCmp_clean hcl hfc
  rcases orElse_eq_some hp with hlx | hp
  · obtain ⟨⟨_, _⟩, hls, he⟩ := Option.map_eq_some_iff.mp hlx; cases he
    exact tryLoadSext_clean hcl hls
  rcases orElse_eq_some hp with hlt | hp
  · obtain ⟨⟨_, _, _, _, _⟩, hlt', he⟩ := Option.map_eq_some_iff.mp hlt; cases he
    exact tryLoadTrunc_clean hcl hlt'
  rcases orElse_eq_some hp with hlea | hp
  · obtain ⟨⟨_, _, _⟩, htl, he⟩ := Option.map_eq_some_iff.mp hlea; cases he
    exact tryLeaArith_clean hcl htl
  rcases orElse_eq_some hp with hzero | hp
  · obtain ⟨⟨_, _, _⟩, htz, he⟩ := Option.map_eq_some_iff.mp hzero; cases he
    exact tryMoviZero_clean hcl htz
  rcases orElse_eq_some hp with hp | hp
  · obtain ⟨pas, hk⟩ := pickPArgsCode_some hp
    have hv : ((I.vec.vop (normCmpOp op dsts).code pas dsts (h.variant.getD ip .default)).map
        fun x => (x.1, x.2, true, false, false, killFlags I x.2 st.flags, none, [])) =
        some (c, cl, iv, _iz, _z, _fl, _ex, _scr) → NoLab I c := fun hk => by
      obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk; cases he
      exact hcl.vop _ _ _ _ _ _ hop
    split at hk
    · rcases orElse_eq_some hk with hk | hk
      · obtain ⟨⟨_, _, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk; cases he
        exact lowerOpScr_clean hcl hop
      · exact hv hk
    · exact hv hk
  rcases orElse_eq_some hp with hrd | hp
  · obtain ⟨⟨_, _⟩, hrd', he⟩ := Option.map_eq_some_iff.mp hrd; cases he
    exact tryRematDirect_clean hcl hrd'
  rcases orElse_eq_some hp with hrc | hp
  · obtain ⟨⟨_, _⟩, hrc', he⟩ := Option.map_eq_some_iff.mp hrc; cases he
    exact tryRematCmpEqImm_clean hcl hrc'
  rcases orElse_eq_some hp with hra | hslot
  · obtain ⟨⟨_, _⟩, hra', he⟩ := Option.map_eq_some_iff.mp hra; cases he
    exact tryRematAdd64SameDst_clean hcl hra'
  · obtain ⟨⟨_, _, _, _, _, _⟩, hsl, he⟩ := Option.map_eq_some_iff.mp hslot; cases he
    exact trySlotOp_clean hcl hsl

theorem lowerOp_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {ts : List Ty}
    {op : Op VNat ts} {deferFuse mulHiOk : Bool} {c : List I.Directive}
    (hl : lowerOp I h nv ip st op deferFuse mulHiOk = some (c, st')) :
    NoLab I c := by
  unfold lowerOp at hl
  split at hl
  · rcases orElse_eq_some hl with h | h <;>
    · obtain ⟨df, -, rfl, -⟩ := Option.map_eq_some_iff.mp h; exact NoLab.nil
  split at hl
  · cases hd : recordDefC I.gpr.addrCse st.defs op.code op.args <;> simp [hd] at hl
    rcases hl with ⟨rfl, -⟩; exact NoLab.nil
  rcases orElse_eq_some hl with hmul | hl
  · split at hmul
    · obtain ⟨⟨_, _, _⟩, hm, rfl, -⟩ := Option.map_eq_some_iff.mp hmul
      exact tryMulHi_clean hcl hm
    · simp at hmul
  obtain ⟨dsts, -, hl⟩ := Option.bind_eq_some_iff.mp hl
  rcases orElse_eq_some hl with hbody | hrem
  · exact lowerOpBody_clean hcl hbody
  · obtain ⟨_, -, hrem⟩ := Option.bind_eq_some_iff.mp hrem
    obtain ⟨_, -, hrem⟩ := List.exists_of_findSome?_eq_some hrem
    obtain ⟨cPre, hrm, hrem⟩ := Option.bind_eq_some_iff.mp hrem
    obtain ⟨⟨cOp, _⟩, hbody, he⟩ := Option.map_eq_some_iff.mp hrem
    simp only [Prod.mk.injEq] at he; rw [← he.1]
    exact (rematAddImm64_clean hcl hrm).append (lowerOpBody_clean hcl hbody)

theorem lowerLoad_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {t : Ty}
    {a : Arg VNat i64} {fz : Bool} {c : List I.Directive}
    (hl : lowerLoad I h nv ip st t a fz = some (c, st')) :
    NoLab I c := by
  unfold lowerLoad at hl
  split at hl
  · split at hl
    · simp only [Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, -⟩; exact NoLab.nil
    · simp at hl
  split at hl
  · split at hl; · simp at hl
    obtain ⟨⟨_, _, _⟩, hls, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    exact lowerLoadScr_clean hcl hls
  · obtain ⟨_, -, hl⟩ := Option.bind_eq_some_iff.mp hl
    split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.vload _ _ _ _ _ hk
  · simp at hl

private theorem tryRmwHalf_clean {st : SymState I} {vh : VariantHint} {n x : Nat}
    {op : RmwOp} {other : Arg VNat (.bits n)} {a : Arg VNat i64} {c : List I.Directive}
    {clob : FlagMask} (h : tryRmwHalf I st vh n op x other a = some (c, clob)) : NoLab I c := by
  unfold tryRmwHalf at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, loadAddr⟩
    cases tm with
    | bits m' =>
      simp only [hmd] at h
      split at h
      · obtain ⟨_, hk1⟩ := tryAddr_some h
        obtain ⟨_, hk2⟩ := tryAddr_some hk1
        split at hk2
        · obtain ⟨_, hk3⟩ := tryArg_some hk2
          exact hcl.rmwMem _ _ _ _ _ _ hk3
        · simp at hk2
      · simp at h
    | _ => simp [hmd] at h

private theorem tryRmwStore_clean {st : SymState I} {vh : VariantHint} {t : Ty}
    {v : Arg VNat t} {a : Arg VNat i64} {c : List I.Directive} {clob : FlagMask}
    (h : tryRmwStore I st vh t v a = some (c, clob)) : NoLab I c := by
  cases t <;> cases v <;> try (simp [tryRmwStore] at h; done)
  simp only [tryRmwStore] at h
  split at h; · simp at h
  split at h
  · obtain ⟨⟨op, x, rhs⟩, -, hk⟩ := Option.bind_eq_some_iff.mp h
    rcases orElse_eq_some hk with hk1 | hk2
    · exact tryRmwHalf_clean hcl hk1
    · split at hk2
      · cases rhs with
        | imm _ => simp at hk2
        | var z => exact tryRmwHalf_clean hcl hk2
      · simp at hk2
  · simp at h

theorem lowerStore_clean {st st' : SymState I} {vh : VariantHint} {t : Ty} {v : Arg VNat t}
    {a : Arg VNat i64} {c : List I.Directive} (hl : lowerStore I st vh t v a = some (c, st')) :
    NoLab I c := by
  cases t with
  | pair x y =>
    simp only [lowerStore] at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨pa, hk⟩ := tryArg_some hta
    cases pa with
    | vec vs => obtain ⟨_, hk⟩ := tryAddr_some hk; exact hcl.vstore _ _ _ _ _ hk
    | gpr _ | imm _ => simp at hk
  | bool | bits _ | float _ =>
    simp only [lowerStore] at hl; split at hl; · simp at hl
    obtain ⟨⟨_, _, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    rcases orElse_eq_some hta with hta | hrmw
    · obtain ⟨_, hk⟩ := tryArgPref_some hta; exact lowerStoreScr_clean hcl hk
    · obtain ⟨⟨_, _⟩, hr, he'⟩ := Option.map_eq_some_iff.mp hrmw; cases he'
      exact tryRmwStore_clean hcl hr

theorem fnPrologue_clean (h : I.Hints) (E : Ext) : NoLab I (fnPrologue I h E) := by
  unfold fnPrologue; split
  · exact NoLab.nil
  · exact hcl.prologue _

theorem fnEpilogue_clean (h : I.Hints) (E : Ext) : NoLab I (fnEpilogue I h E) := by
  unfold fnEpilogue; split
  · exact NoLab.nil
  · exact hcl.epilogue _

omit hcl in
theorem lowerTail_spec {h : I.Hints} {E : Ext} {st : SymState I} {mc tail : List I.Directive}
    {ts : List Ty} {args : Tup (Arg VNat) ts} {locs : Tup (AbiReg I.Reg I.VReg) ts}
    {nv nl ip : Nat} {c : List I.Directive} {nv' nl' ip' : Nat}
    (hl : lowerTail I h E st mc tail args locs nv nl ip = .ok (c, nv', nl', ip')) :
    nv' = nv ∧ nl' = nl ∧ (LabelClean I → NoLab I mc → NoLab I tail → NoLab I c) := by
  unfold lowerTail at hl; repeat' (split at hl <;> try (simp at hl; done))
  simp only [Except.ok.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl, rfl, -⟩ := hl
  exact ⟨rfl, rfl, fun hcl hm ht => ((((hm.append (shuffle_clean hcl ‹_›)).append
    (canonAbiCode_clean hcl _ _)).append (restoreCs_clean hcl _ _)).append
      (fnEpilogue_clean hcl h E)).append ht⟩

end Labels

section Labels2
variable {I : Isa}

/-! ### Structural label bounds for `lowerExpr`/`lowerBlocks` -/

theorem prepend_ok {pre : List I.Directive} {r : Res I} {c : List I.Directive} {nv nl ip : Nat}
    (h : prepend pre r = .ok (c, nv, nl, ip)) : ∃ c0, r = .ok (c0, nv, nl, ip) ∧ c = pre ++ c0 := by
  cases r with
  | error e => simp [prepend] at h
  | ok q =>
    obtain ⟨c0, a, b, d⟩ := q; simp only [prepend, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact ⟨c0, rfl, rfl⟩

theorem ite_cases {α : Type} {p : Prop} [Decidable p] {a b r : α} (h : (if p then a else b) = r) :
    a = r ∨ b = r := by
  by_cases hp : p <;> simp_all

theorem finishJnz_ok {rs : List Ty} {fn : Sym} {nl : Nat} {tgt : Option Nat}
    {b : Expr VNat LNat rs} {br c₁ c₂ : List I.Directive} {nv₂ nl₂ ip₂ : Nat}
    {c : List I.Directive} {nv' nl' ip' : Nat}
    (h : finishJnzBranch I fn nl tgt b br c₁ c₂ nv₂ nl₂ ip₂ = .ok (c, nv', nl', ip')) :
    nv' = nv₂ ∧ nl' = nl₂ ∧
      (c = br ++ c₁ ∨ c = br ++ c₁ ++ [I.frame.label (lname fn nl)] ++ c₂) := by
  unfold finishJnzBranch at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl, -⟩ := h; simp)

/-- `jnz` code: `br ++ c₁ ++ [label nl] ++ c₂` with `c₁`, `c₂` in disjoint ranges above `nl`. -/
theorem LabOk.jnz (hcl : LabelClean I) {fn : Sym} {nl a b d : Nat} {br c₁ c₂ : List I.Directive}
    (hbr : NoLab I br) (hab : nl < a ∧ a ≤ b ∧ b ≤ d) (h₁ : LabOk I (lrange fn (nl + 1) b) c₁)
    (h₂ : LabOk I (lrange fn b d) c₂) {c : List I.Directive}
    (hc : c = br ++ c₁ ∨ c = br ++ c₁ ++ [I.frame.label (lname fn nl)] ++ c₂ ∨
      c = br ++ c₂ ∨ c = br ++ c₂ ++ [I.frame.label (lname fn nl)] ++ c₁) :
    LabOk I (lrange fn nl d) c := by
  have hl : LabOk I (lrange fn nl (nl + 1)) [I.frame.label (lname fn nl)] :=
    (LabOk.single hcl _).mono fun l hl => ⟨nl, Nat.le_refl _, Nat.lt_succ_self _, hl⟩
  have m : ∀ {x y l}, lrange fn x y l → nl ≤ x → y ≤ d → lrange fn nl d l :=
    fun h hx hy => lrange_mono h hx hy
  have three : ∀ {x y : List I.Directive} {S T : Sym → Prop}, LabOk I S x → LabOk I T y →
      (∀ l, S l → lrange fn (nl + 1) d l) → (∀ l, T l → lrange fn (nl + 1) d l) →
      (∀ l, S l → T l → False) → LabOk I (lrange fn nl d)
          (br ++ x ++ [I.frame.label (lname fn nl)] ++ y) := by
      intro x y S T hx hy hS hT hST
      refine (((hx.pre hbr).append (S := fun l => S l ∨ lrange fn nl (nl + 1) l) hl
        (fun l h1 h2 => lrange_disj (hS l h1) h2 (by omega)) (fun l h => h)).append hy
        (fun l h1 h2 => ?_) (fun l h => ?_))
      · exact h1.elim (fun h1 => hST l h1 h2) (fun h1 => lrange_disj h1 (hT l h2) (by omega))
      · rcases h with (h | h) | h
        · exact m (hS l h) (by omega) (Nat.le_refl _)
        · exact m h (Nat.le_refl _) (by omega)
        · exact m (hT l h) (by omega) (Nat.le_refl _)
  rcases hc with rfl | rfl | rfl | rfl
  · exact (h₁.pre hbr).mono fun l h => m h (by omega) (by omega)
  · exact three h₁ h₂ (fun l h => lrange_mono h (Nat.le_refl _) (by omega))
      (fun l h => lrange_mono h (by omega) (Nat.le_refl _)) (fun l h1 h2 =>
        lrange_disj h1 h2 (by omega))
  · exact (h₂.pre hbr).mono fun l h => m h (by omega) (by omega)
  · exact three h₂ h₁ (fun l h => lrange_mono h (by omega) (Nat.le_refl _))
      (fun l h => lrange_mono h (Nat.le_refl _) (by omega)) (fun l h1 h2 =>
        lrange_disj h1 h2 (by omega))

private theorem fuseJnzChoice_clean {I : Isa} {h : I.Hints} {fn : Sym} {nl ipT ipE : Nat}
    {rs : List Ty} {st1 : SymState I} {t e : Expr VNat LNat rs} {ft : Option Nat}
    {emit : Bool → Sym → Option (List I.Directive × FlagMask)} {fwd : Trie Nat}
    (hem : ∀ inv l c cl, emit inv l = some (c, cl) → NoLab I c)
    {inv : Bool} {tgt : Option Nat} {br : List I.Directive} {stBr : SymState I}
    (hf : fuseJnzChoice I h fn nl ipT ipE st1 t e ft emit fwd = some (inv, tgt, br, stBr)) :
    NoLab I br := by
  unfold fuseJnzChoice at hf
  obtain ⟨⟨brNl, clNl⟩, heNl, hm⟩ := Option.map_eq_some_iff.mp hf
  have hArm : ∀ {inv0 ip0} {arm0 : Expr VNat LNat rs} {j b s},
      threadFusedArm I h fn ip0 st1 (emit inv0) arm0 fwd = some (j, b, s) → NoLab I b := by
    intro inv0 ip0 arm0 j b s ha
    unfold threadFusedArm at ha
    split at ha
    · simp only [Option.bind_eq_some_iff] at ha
      obtain ⟨⟨b', c'⟩, h1, h2⟩ := ha
      split at h2
      · simp only [Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨-, rfl, -⟩ := h2; exact hem _ _ _ _ h1
      · simp at h2
    · simp at ha
  cases hfwd : threadFusedArm I h fn ipT st1 (emit false) t fwd <;>
    cases hinv : threadFusedArm I h fn ipE st1 (emit true) e fwd
  · rw [hfwd, hinv] at hm; cases hm; exact hem _ _ _ _ heNl
  · rw [hfwd, hinv] at hm; cases hm; exact hArm hinv
  · rw [hfwd, hinv] at hm; cases hm; exact hArm hfwd
  · rw [hfwd, hinv] at hm; dsimp only at hm
    split at hm <;> cases hm
    · exact hArm hinv
    · exact hArm hfwd

private theorem jnzSetup_clean (hcl : LabelClean I) {h : I.Hints} {fn : Sym} {nl ipT ipE : Nat}
    {rs : List Ty} {st1 : SymState I} {t e : Expr VNat LNat rs} {ft : Option Nat} {cond : JnzCond I}
    {fwd : Trie Nat} {inv : Bool} {tgt : Option Nat} {br : List I.Directive} {stBr : SymState I}
    (hj : jnzSetup I h fn nl ipT ipE st1 t e ft cond fwd = some (inv, tgt, br, stBr)) :
    NoLab I br := by
  cases cond with
  | flag cc =>
    simp only [jnzSetup, Option.some.injEq, Prod.mk.injEq] at hj
    cases hj.2.2.1; exact hcl.jcc _ _
  | gpr r =>
    dsimp only [jnzSetup] at hj
    cases hfn : I.gpr.jnzGprInv? with
    | none =>
      rw [hfn] at hj
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      cases hj.2.2.1; exact hcl.jnzGpr _ _
    | some jnzFn =>
      rw [hfn] at hj
      exact fuseJnzChoice_clean (fun inv l c cl he => by
        simp only [Option.some.injEq] at he
        have hc : c = (jnzFn r inv l).1 := (congrArg Prod.fst he).symm
        rw [hc]; exact hcl.jnzGprInv _ _ _ _ hfn) hj
  | slot idx =>
    simp only [jnzSetup, Option.bind_eq_some_iff] at hj
    obtain ⟨⟨_, _⟩, hjbr, hc⟩ := hj
    split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨-, -, rfl, -⟩ := hc; exact hcl.jnzMem _ _ _ _ _ hjbr
    · simp at hc
  | cmpZero co w r =>
    dsimp only [jnzSetup] at hj
    exact fuseJnzChoice_clean (fun _ _ _ _ he => hcl.cmpZeroJcc _ _ _ _ _ _ he) hj
  | cmpZeroMem co w x aa cc =>
    simp only [jnzSetup] at hj
    obtain ⟨⟨c0, cl0⟩, hcm, he⟩ := Option.map_eq_some_iff.mp hj
    simp only [finishCmpJnz, Prod.mk.injEq] at he; rw [← he.2.2.1]
    exact fun l hl => (List.mem_append.mp hl).elim
      (hcl.cmpMem _ _ _ _ _ _ _ hcm l) (hcl.jcc _ _ l)
  | cmpZeroFlag co w x r cc =>
    simp only [jnzSetup] at hj
    obtain ⟨⟨c0, cl0⟩, hop, he⟩ := Option.map_eq_some_iff.mp hj
    simp only [finishCmpJnz, Prod.mk.injEq] at he; rw [← he.2.2.1]
    exact fun l hl => (List.mem_append.mp hl).elim
      (hcl.op _ _ _ _ _ _ hop l) (hcl.jcc _ _ l)
  | testImm neg w r mask =>
    dsimp only [jnzSetup] at hj
    exact fuseJnzChoice_clean (fun _ _ _ _ he => hcl.testJcc _ _ _ _ _ _ _ he) hj

mutual
/-- `lowerExpr` is monotone in `nv`/`nl`, and (for a `LabelClean` ISA) its labels are distinct
`lname fn j` with `nl ≤ j < nl'`. -/
theorem lowerExpr_labels {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} :
    ∀ (e : Expr VNat LNat rs) (nv nl ip : Nat) (st : SymState I) (ft : Option Nat)
      (fwd : Trie Nat) (fwdTgts : Trie Bool) (c : List I.Directive) (nv' nl' ip' : Nat),
    lowerExpr I h E fn e nv nl ip st ft fwd fwdTgts = .ok (c, nv', nl', ip') →
    nv ≤ nv' ∧ nl ≤ nl' ∧ (LabelClean I → LabOk I (lrange fn nl nl') c)
  | .let_ op k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl =>
      (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerOp_clean hcl ‹_›))⟩
  | .load t a k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl =>
      (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerLoad_clean hcl ‹_›))⟩
  | .store v a k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨h1, h2, fun hcl =>
      (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerStore_clean hcl ‹_›))⟩
  | .call f args k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl => (h3 hcl).pre ((((stepPre_clean hcl ‹_›).append
      (shuffle_clean hcl ‹_›)).append (canonAbiCode_clean hcl _ _)).append (hcl.call _))⟩
  | .jnz (.imm b) t e, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; split at he <;> try (simp at he; done)
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    rcases ite_cases hr with hr | hr <;> obtain ⟨h1, h2, h3⟩ :=
        lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ hr <;>
      exact ⟨h1, h2, fun hcl => (h3 hcl).pre (stepPre_clean hcl ‹_›)⟩
  | .jnz (.var cx) t e, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    split at he <;> try (simp at he; done)
    split at he <;> try (simp at he; done)
    split at he <;> try (simp at he; done)
    rename_i inv tgt br stBr hs
    split at he <;> try (simp at he; done)
    rename_i ce nv₁ nl₁ ip₁ he₁
    split at he <;> try (simp at he; done)
    rename_i ct nv₂ nl₂ ip₂ he₂
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he₂
    rcases ite_cases hr with hr | hr <;> obtain ⟨rfl, rfl, hc⟩ := finishJnz_ok hr
    · refine ⟨by omega, by omega, fun hcl => (LabOk.jnz hcl (jnzSetup_clean hcl hs)
        ⟨Nat.lt_succ_self _, a2, b2⟩ (a3 hcl) (b3 hcl)
        (hc.elim (fun h => Or.inr (Or.inr (Or.inl h)))
          fun h => Or.inr (Or.inr (Or.inr h)))).pre (stepPre_clean hcl ‹_›)⟩
    · refine ⟨by omega, by omega, fun hcl => (LabOk.jnz hcl (jnzSetup_clean hcl hs)
        ⟨Nat.lt_succ_self _, a2, b2⟩ (a3 hcl) (b3 hcl)
        (hc.elim Or.inl fun h => Or.inr (Or.inl h))).pre (stepPre_clean hcl ‹_›)⟩
  | .jump j args, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    repeat' (split at he <;> try (simp at he; done))
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, -⟩ := he
      refine ⟨Nat.le_refl _, Nat.le_refl _, fun hcl => LabOk.clean ((((stepPre_clean hcl ‹_›).append
        (shuffle_clean hcl ‹_›))).append ?_)⟩
      first | exact NoLab.nil | exact hcl.jmp _
  | .ret vs, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; split at he <;> try (simp at he; done)
    obtain ⟨rfl, rfl, h3⟩ := lowerTail_spec he
    exact ⟨Nat.le_refl _, Nat.le_refl _,
      fun hcl => LabOk.clean (h3 hcl (stepPre_clean hcl ‹_›) hcl.ret)⟩
  | .exit f args, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨rfl, rfl, h3⟩ := lowerTail_spec he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun hcl =>
      LabOk.clean (h3 hcl (stepPre_clean hcl ‹_›) (hcl.exitJmp _))⟩
  | .hlt, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr, Except.ok.injEq, Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ => LabOk.clean NoLab.nil⟩
  | .group (sig := sig) bodies k, nv, nl, ip, st, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    split at he <;> try (simp at he; done)
    rename_i ck nv₁ nl₁ ip₁ he₁
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr
    refine ⟨by omega, by omega, fun hcl => (a3 hcl).append (b3 hcl a2) (fun l h1 h2 =>
      ?_) (fun l h => ?_)⟩
    · rcases h2 with h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
    · rcases h with h | h | h <;> exact lrange_mono h (by omega) (by omega)

/-- `lowerBlocks` analogue: block labels `lname fn j` for `lid ≤ j < lid + sig.length`, plus body
labels in `[nl, nl')`. -/
theorem lowerBlocks_labels {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks VNat LNat rs sig) (lid nv nl ip : Nat)
      (defs : Trie DefFact) (vw : Trie SlotWidth) (ft : Option Nat)
      (fwd : Trie Nat) (fwdTgts : Trie Bool) (c : List I.Directive) (nv' nl' ip' : Nat),
    lowerBlocks I h E fn bs lid nv nl ip defs vw ft fwd fwdTgts = .ok (c, nv', nl', ip') →
    nv ≤ nv' ∧ nl ≤ nl' ∧ (LabelClean I → lid + sig.length ≤ nl →
      LabOk I (fun l => lrange fn lid (lid + sig.length) l ∨ lrange fn nl nl' l) c)
  | _, .nil, lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerBlocks, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => LabOk.clean NoLab.nil⟩
  | _, .cons (sig :=
      sig) b bs, lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts, c, nv', nl', ip', he => by
    simp only [lowerBlocks] at he
    cases hfw : fwd.find? lid with
    | some fwdTgt =>
      rw [hfw] at he; dsimp only at he
      split at he <;> try (simp at he; done)
      split at he <;> try (simp at he; done)
      obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ _ _ he
      refine ⟨by omega, b2, fun hcl hlid => ?_⟩
      simp only [List.length_cons] at hlid ⊢
      exact (b3 hcl (by omega)).mono fun l hl =>
        hl.imp (fun h => lrange_mono h (by omega) (by omega)) id
    | none =>
      rw [hfw] at he; dsimp only at he
      repeat' (split at he <;> try (simp at he; done))
      rename_i cb nv₁ nl₁ ip₁ he₁
      obtain ⟨c0, hr, rfl⟩ := prepend_ok he
      obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he₁
      obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr
      refine ⟨by omega, by omega, fun hcl hlid => ?_⟩
      simp only [List.length_cons] at hlid ⊢
      have hl : LabOk I (lrange fn lid (lid + 1)) [I.frame.label (lname fn lid)] :=
        (LabOk.single hcl _).mono fun l hl => ⟨lid, Nat.le_refl _, Nat.lt_succ_self _, hl⟩
      refine (hl.append ((a3 hcl).append (b3 hcl (by omega)) (fun l h1 h2 => ?_) (fun l h => h))
        (fun l h1 h2 => ?_) (fun l h => ?_))
      · rcases h2 with h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
      · rcases h2 with h2 | h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
      · rcases h with h | h | h | h <;> first
          | exact Or.inl (lrange_mono h (by omega) (by omega))
          | exact Or.inr (lrange_mono h (by omega) (by omega))
end

theorem lowerExpr_nv_le {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} {e : Expr VNat LNat rs}
    {nv nl ip : Nat} {st : SymState I} {ft : Option Nat} {fwd : Trie Nat} {fwdTgts : Trie Bool}
    {c : List I.Directive} {nv' nl' ip' : Nat}
    (he : lowerExpr I h E fn e nv nl ip st ft fwd fwdTgts = .ok (c, nv', nl', ip')) :
    nv ≤ nv' ∧ nl ≤ nl' :=
  have hl := lowerExpr_labels e nv nl ip st ft fwd fwdTgts c nv' nl' ip' he; ⟨hl.1, hl.2.1⟩

theorem lowerBlocks_nv_le {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} {sig : List (List Ty)}
    {bs : Blocks VNat LNat rs sig} {lid nv nl ip : Nat} {defs : Trie DefFact} {vw : Trie SlotWidth}
    {ft : Option Nat} {fwd : Trie Nat} {fwdTgts : Trie Bool} {c : List I.Directive}
    {nv' nl' ip' : Nat}
    (he : lowerBlocks I h E fn bs lid nv nl ip defs vw ft fwd fwdTgts = .ok (c, nv', nl', ip')) :
    nv ≤ nv' ∧ nl ≤ nl' :=
  have hl := lowerBlocks_labels bs lid nv nl ip defs vw ft fwd fwdTgts c nv' nl' ip' he
  ⟨hl.1, hl.2.1⟩

theorem lowerFn_labOk {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (hf : lowerFn I hints E f = .ok code) :
    LabOk I (fun l => l = f.name ∨ ∃ j, l = lname f.name j) code := by
  unfold lowerFn at hf
  repeat' (split at hf <;> try (simp at hf; done))
  rename_i c _ _ _ he
  simp only [Except.ok.injEq] at hf; subst hf
  have h3 := (lowerExpr_labels _ _ _ _ _ _ _ _ _ _ _ _ he).2.2 hcl
  refine (LabOk.single hcl f.name).append
    (h3.pre ((fnPrologue_clean hcl hints E).append (saveCs_clean hcl _ _)))
    (fun l h1 h2 => ?_) (fun l h => ?_)
  · obtain ⟨j, -, -, rfl⟩ := h2; exact lname_ne h1
  · exact h.imp id fun ⟨j, _, _, e⟩ => ⟨j, e⟩

/-- Labels of a lowered function are pairwise distinct (proved structurally, without `decide`). -/
theorem lowerFn_labelsUnique {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (h : lowerFn I hints E f = .ok code) :
    ∀ (i j : Nat) l, code[i]? = some (I.frame.label l) →
      code[j]? = some (I.frame.label l) → i = j := (lowerFn_labOk hcl h).1

theorem lowerFn_label_mem {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (h : lowerFn I hints E f = .ok code) {i : Nat} {l : Sym}
    (hi : code[i]? = some (I.frame.label l)) : l = f.name ∨ ∃ j, l = lname f.name j :=
  (lowerFn_labOk hcl h).2 l (List.mem_of_getElem? hi)

end Labels2

end Rega
end LeanQbe.T
