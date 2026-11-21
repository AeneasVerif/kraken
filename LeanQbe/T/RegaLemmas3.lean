module

public import LeanQbe.T.RegaLemmas1
public import LeanQbe.T.WPLemmas

/-!
# `T7b` Part 3: Operands, Ops/Loads/Stores, and Structural `LabelsUnique` (Guardrail 5)

* `tryArg_ok`, `pickPArgs_ok`, `tryAddr_ok`, `lowerOp_ok`, `lowerLoad_ok`, `lowerStore_ok`.
* Structural label bounds (`LabelClean`, `lname_inj`, `lowerExpr_labels`/`lowerBlocks_labels`): every
  label emitted by `lowerExpr` is `lname fn j` with `j ∈ [nl, nl')`, pairwise distinct, via monotone
  `nl` (no `O(L^2)` `decide`); `lowerFn_labelsUnique`, `lowerFn_label_mem`, `lowerExpr_nv_le`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-! ## Pure helpers -/

theorem orElse_eq_some {α : Type} {a b : Option α} {r : α} (h : (a <|> b) = some r) :
    a = some r ∨ b = some r := by
  cases a <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem slotWidthEq_eq {a b : SlotWidth} (h : slotWidthEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [slotWidthEq]

theorem symArgEq_eq {a b : SymArg} (h : symArgEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [symArgEq]
  · rename_i x y; revert h; cases x <;> cases y <;> decide
  · exact slotWidthEq_eq h.1

theorem regLocEq_eq {I : Isa} {a b : RegLoc I.Reg I.VReg I.Cond} (h : regLocEq a b = true) :
    a = b := by
  cases a <;> cases b <;> simp_all [regLocEq]

theorem gprSym_match {G : VCtx} {w : BitVec 64} {sa' sa : SymArg} (h : GprSym G w sa')
    (hm : symArgMatchesGpr sa' sa = true) : GprSym G w sa := by
  unfold symArgMatchesGpr at hm
  split at hm
  · next he => rwa [← symArgEq_eq he]
  · split at hm
    · simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, beq_iff_eq] at hm
      obtain ⟨⟨rfl, hle⟩, rfl⟩ := hm
      simp only [GprSym, BitVec.setWidth_eq] at h ⊢
      exact ⟨hle, by rw [h.2]⟩
    · simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      simp only [GprSym, BitVec.setWidth_eq] at h ⊢
      rw [h.2]; cases ‹Bool› <;> rfl
    · simp at hm

theorem mem_cons_top {G : VCtx} {nv : Nat} (hlt : ∀ p ∈ G, p.2.2 < nv) {t t' : Ty} {v : Val t}
    {v' : Val t'} (h : (⟨t', v', nv⟩ : (a : Ty) × Val a × VNat a) ∈ ⟨t, v, nv⟩ :: G) :
    (⟨t', v'⟩ : Sigma Val) = ⟨t, v⟩ := by
  rcases List.mem_cons.mp h with h | h
  · cases h; rfl
  · exact absurd (hlt _ h) (Nat.lt_irrefl _)

theorem wp_recordDef {G : VCtx} {nv : Nat} {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact} (hd : recordDef code args = some df) :
    code.wp (vals args₁) (fun rvs => P rvs ∧ 
      0 < rs.length ∧ DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df) := by
  unfold recordDef at hd
  split at hd
  · split at hd
    · simp at hd
    · next hn =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, Nat.beq_eq] at hn; subst hn
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      split at hd <;> cases hd <;> cases h1 <;> cases h2
      all_goals
        simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp ⊢
        refine ⟨hwp, by simp, fun v' hm' => ?_⟩
        simp only [Tup.zip, Tup.levels] at hm'
        cases mem_cons_top hlt hm'
      · exact ⟨_, List.mem_cons_of_mem _ ‹_›, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ ‹_›, by simp [BitVec.add_comm]⟩
  · split at hd
    · next hn =>
      simp only [Nat.beq_eq] at hn; subst hn
      rcases hrel with _ | ⟨h1, _ | ⟨h2, -⟩⟩
      cases hd; cases h1; cases h2
      simp only [OpCode.wp_sub, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp ⊢
      refine ⟨hwp, by simp, fun v' hm' => ?_⟩
      simp only [Tup.zip, Tup.levels] at hm'
      cases mem_cons_top hlt hm'
      exact ⟨_, List.mem_cons_of_mem _ ‹_›, by simp [BitVec.sub_eq_add_neg]⟩
    · simp at hd
  · split at hd
    · next hn =>
      simp only [Nat.beq_eq] at hn; subst hn
      rcases hrel with _ | ⟨h1, -⟩
      cases hd; cases h1
      simp only [OpCode.wp_copy, vals, Arg.val] at hwp ⊢
      refine ⟨hwp, by simp, fun v' hm' => ?_⟩
      simp only [Tup.zip, Tup.levels] at hm'
      cases mem_cons_top hlt hm'
      simp
    · simp at hd
  · simp at hd

theorem recordDef_elide_ok {G : VCtx} {nv : Nat} {sig rs : List Ty} {code : OpCode sig rs}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact} (hd : recordDef code args = some df) :
    ∃ (rvs : Tup Val rs), P rvs ∧ rs = [i64] ∧
      DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df := by
  have hwp' := wp_recordDef hrel hlt hwp hd
  unfold recordDef at hd
  split at hd
  · split at hd
    · simp at hd
    · next hn =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, Nat.beq_eq] at hn; subst hn
      simp only [OpCode.wp_add, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
      exact ⟨_, hwp'.1, rfl, hwp'.2.2⟩
  · split at hd
    · next hn =>
      simp only [Nat.beq_eq] at hn; subst hn
      simp only [OpCode.wp_sub, Ty.hasFloat, Bool.false_eq_true, ite_false] at hwp'
      exact ⟨_, hwp'.1, rfl, hwp'.2.2⟩
    · simp at hd
  · split at hd
    · next hn =>
      simp only [Nat.beq_eq] at hn; subst hn
      simp only [OpCode.wp_copy] at hwp'
      exact ⟨_, hwp'.1, rfl, hwp'.2.2⟩
    · simp at hd
  · simp at hd

theorem zip_levels_mem {G : VCtx} : ∀ {ts : List Ty} {rvs : Tup Val ts} {nv : Nat} {p},
    p ∈ (Tup.zip rvs (Tup.levels ts nv) : VCtx) ++ G → p ∈ G ∨ (nv ≤ p.2.2 ∧ p.2.2 < nv + ts.length)
  | [], _, _, _, h => Or.inl (by simpa [Tup.zip] using h)
  | _ :: _, _, nv, p, h => by
    simp only [Tup.zip, Tup.levels, List.cons_append, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inr ⟨Nat.le_refl _, by simp⟩
    · rcases zip_levels_mem h with h | h
      · exact Or.inl h
      · refine Or.inr ⟨Nat.le_of_succ_le h.1, ?_⟩
        rw [List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]; exact h.2

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n : Nat} {Rf : Mem 64 → Prop}

/-! ## Operand lookups -/

theorem tryGpr_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {sa : SymArg}
    {k : T.Reg → Option α} {res : α} (h : tryGpr T.toIsa st.regs sa k = some res) :
    ∃ r, k r = some res ∧ r ∉ T.frame.scratch ∧ GprSym G (T.mach.getGpr s r) sa := by
  obtain ⟨⟨sa', rl⟩, hmem, hk⟩ := List.exists_of_findSome?_eq_some h
  cases rl with
  | gpr r =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact ⟨r, hk, by simpa using hc.1, gprSym_match (hA.regs _ hmem) hc.2⟩
    · simp at hk
  | vec _ | flag _ => simp at hk

theorem findGprFor_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {sa : SymArg} {r : T.Reg}
    (h : findGprFor T.toIsa true st.regs sa = some r) :
    r ∉ T.frame.scratch ∧ GprSym G (T.mach.getGpr s r) sa := by
  obtain ⟨⟨sa', rl⟩, hmem, hk⟩ := List.exists_of_findSome?_eq_some h
  cases rl with
  | gpr r' =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Option.some.injEq] at hk; subst hk
      simp only [Bool.and_eq_true, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hc
      exact ⟨by simpa using hc.1, gprSym_match (hA.regs _ hmem) hc.2⟩
    · simp at hk
  | vec _ | flag _ => simp at hk

theorem tryVec_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {sa : SymArg}
    {k : T.VReg → Option α} {res : α} (h : tryVec T.toIsa st.regs sa k = some res) :
    ∃ v, k v = some res ∧ v ∉ T.vec.vecScratch ∧ VecSym G .w512 (T.mach.getVec s v) sa := by
  obtain ⟨⟨sa', rl⟩, hmem, hk⟩ := List.exists_of_findSome?_eq_some h
  cases rl with
  | vec v =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      have := hA.regs _ hmem
      rw [symArgEq_eq hc.2] at this
      exact ⟨v, hk, by simpa using hc.1, this⟩
    · simp at hk
  | gpr _ | flag _ => simp at hk

theorem tryFlag_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond}
    {sa : SymArg} {k : T.Cond → Option α} {res : α}
    (h : tryFlag T.toIsa st.regs pref sa k = some res) :
    ∃ c, k c = some res ∧ FlagSym G (T.mach.evalCond s c) sa := by
  rcases orElse_eq_some h with h | h
  · obtain ⟨c, -, hk⟩ := List.exists_of_findSome?_eq_some h
    split at hk
    · next hc =>
      obtain ⟨⟨sa', rl⟩, hmem, hp⟩ := List.any_eq_true.mp hc
      simp only [Bool.and_eq_true] at hp
      have := hA.regs _ hmem
      rw [regLocEq_eq hp.2, symArgEq_eq hp.1] at this
      exact ⟨c, hk, this⟩
    · simp at hk
  · obtain ⟨⟨sa', rl⟩, hmem, hk⟩ := List.exists_of_findSome?_eq_some h
    cases rl with
    | flag c =>
      simp only at hk; split at hk
      · next hc =>
        have := hA.regs _ hmem
        rw [symArgEq_eq hc] at this
        exact ⟨c, hk, this⟩
      · simp at hk
    | gpr _ | vec _ => simp at hk

theorem tryArg_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond} {t : Ty}
    {a₁ : Arg Val t} {a : Arg VNat t} {k : PArg T.Reg T.VReg T.Cond t → Option α} {res : α}
    (hrel : ArgRel G t a₁ a) (h : tryArg T.toIsa st pref t a k = some res) :
    ∃ pa, k pa = some res ∧ (∀ r ∈ pa.gprs, r ∉ T.frame.scratch) ∧
      (∀ v, pa = .vec v → v ∉ T.vec.vecScratch) ∧ T.mach.PArgHolds s t pa a₁.val := by
  cases hrel with
  | var hm =>
    cases t with
    | bool =>
      rcases orElse_eq_some h with h | h
      · obtain ⟨c, hk, hf⟩ := tryFlag_ok hA h
        exact ⟨.flag c, hk, by simp [PArg.gprs], by simp, (hf _ _ hm).symm⟩
      · obtain ⟨r, hk, hr, hg⟩ := tryGpr_ok hA h
        exact ⟨.gpr r, hk, by simpa [PArg.gprs] using hr, by simp, hg _ _ hm⟩
    | bits _ =>
      obtain ⟨r, hk, hr, hg⟩ := tryGpr_ok hA h
      exact ⟨.gpr r, hk, by simpa [PArg.gprs] using hr, by simp, hg _ _ hm⟩
    | pair _ _ =>
      obtain ⟨v, hk, hv, hg⟩ := tryVec_ok hA h
      exact ⟨.vec v, hk, by simp [PArg.gprs], by rintro _ ⟨⟩; exact hv, (hg _ _ hm).2⟩
    | float _ => simp [tryArg] at h
  | imm c =>
    have imm : k (.imm c) = some res → ∃ pa, k pa = some res ∧ (∀ r ∈ pa.gprs, r ∉ T.frame.scratch) ∧
        (∀ v, pa = .vec v → v ∉ T.vec.vecScratch) ∧ T.mach.PArgHolds s t pa (Arg.imm c).val :=
      fun hk => ⟨.imm _, hk, by simp [PArg.gprs], by simp, by cases t <;> rfl⟩
    cases t with
    | bool =>
      rcases orElse_eq_some h with h | h
      · obtain ⟨c', hk, hf⟩ := tryFlag_ok hA h
        exact ⟨.flag c', hk, by simp [PArg.gprs], by simp, hf⟩
      rcases orElse_eq_some h with h | h
      · exact imm h
      · obtain ⟨r, hk, hr, hg⟩ := tryGpr_ok hA h
        exact ⟨.gpr r, hk, by simpa [PArg.gprs] using hr, by simp, hg⟩
    | bits w =>
      rcases orElse_eq_some h with h | h
      · exact imm h
      split at h
      · obtain ⟨r, hk, hr, hg⟩ := tryGpr_ok hA h
        refine ⟨.gpr r, hk, by simpa [PArg.gprs] using hr, by simp, hg.1, ?_⟩
        rw [hg.2]; exact (BitVec.setWidth_setWidth_of_le c (Nat.le_of_ble_eq_true ‹_›)).trans
          (BitVec.setWidth_eq c)
      · simp at h
    | pair a b =>
      rcases orElse_eq_some h with h | h
      · exact imm h
      split at h
      · simp at h
      · obtain ⟨v, hk, hv, hg⟩ := tryVec_ok hA h
        exact ⟨.vec v, hk, by simp [PArg.gprs], by rintro _ ⟨⟩; exact hv,
          immVec_vecHolds (vecWidth?_spec ‹_›).1 hg.2⟩
    | float _ => simp [tryArg] at h

theorem pickPArgs_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond} :
    ∀ {sig : List Ty} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
      {k : Tup (PArg T.Reg T.VReg T.Cond) sig → Option α} {res : α},
    TRel (ArgRel G) args₁ args → pickPArgs T.toIsa st pref args k = some res →
    ∃ pas, k pas = some res ∧ (∀ r ∈ tupArgGprs pas, r ∉ T.frame.scratch) ∧
      (∀ v ∈ tupArgVecs pas, v ∉ T.vec.vecScratch) ∧ TRel (T.mach.PArgHolds s) pas (vals args₁) := by
  intro sig args₁ args k res hrel h
  induction hrel generalizing res with
  | nil => exact ⟨(), h, by simp [tupArgGprs], by simp [tupArgVecs], .nil⟩
  | cons ha _ ih =>
    simp only [pickPArgs] at h
    obtain ⟨pa, hk, hg, hv, hp⟩ := tryArg_ok hA ha h
    obtain ⟨pas, hk', hg', hv', hp'⟩ := ih (k := fun pas => k (pa, pas)) hk
    refine ⟨(pa, pas), hk', ?_, ?_, .cons hp hp'⟩
    · cases pa <;> simp_all [tupArgGprs, PArg.gprs]
    · cases pa <;> simp_all [tupArgVecs]

theorem tryAddr_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {vh : VariantHint} {α : Type}
    {a₁ : Arg Val i64} {a : Arg VNat i64} {k : AddrArg T.Reg → Option α} {res : α}
    (hrel : ArgRel G i64 a₁ a) (h : tryAddr T.toIsa st vh a k = some res) :
    ∃ aa, k aa = some res ∧ (∀ r ∈ aa.regs, r ∉ T.frame.scratch) ∧
      aa.eval (T.mach.getGpr s) = a₁.val := by
  have reg : ∀ {r : T.Reg} {d : Int64} {x : BitVec 64}, k (.baseDisp r d) = some res →
      findGprFor T.toIsa true st.regs (.immBits 64 x) = some r ∨
        (∃ y v, findGprFor T.toIsa true st.regs (.var y) = some r ∧ ⟨i64, v, y⟩ ∈ G ∧ x = v) →
      x + d.toBitVec = a₁.val →
      ∃ aa, k aa = some res ∧ (∀ r ∈ aa.regs, r ∉ T.frame.scratch) ∧
        aa.eval (T.mach.getGpr s) = a₁.val := by
    intro r d x hk hr hx
    rcases hr with hr | ⟨y, v, hr, hm, rfl⟩ <;> obtain ⟨hs, hg⟩ := findGprFor_ok hA hr <;>
      refine ⟨.baseDisp r d, hk, by simpa [AddrArg.regs] using hs, ?_⟩
    · simp only [GprSym, BitVec.setWidth_eq] at hg; simp [AddrArg.eval, hg.2, ← hx]
    · have := (hg _ _ hm).2; simp only [BitVec.setWidth_eq] at this; simp [AddrArg.eval, this, ← hx]
  cases hrel with
  | imm c =>
    rcases orElse_eq_some h with h | h
    · exact ⟨.imm c, h, by simp [AddrArg.regs], rfl⟩
    · obtain ⟨r, hr, hk⟩ := Option.bind_eq_some_iff.mp h
      exact reg hk (Or.inl hr) (by simp [Arg.val])
  | var hm =>
    rename_i v x
    simp only [tryAddr] at h
    rcases orElse_eq_some h with h | h
    · split at h
      · rename_i off base d hdef _
        split at h
        · next hd =>
          obtain ⟨rb, hr, hk⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨vb, hmb, hv⟩ := hA.defs _ _ hdef v hm
          exact reg hk (Or.inr ⟨_, _, hr, hmb, rfl⟩) (by simp_all [Arg.val])
        · simp at h
      · simp at h
    rcases orElse_eq_some h with h | h
    · obtain ⟨r, hr, hk⟩ := Option.bind_eq_some_iff.mp h
      exact reg hk (Or.inr ⟨_, _, hr, hm, rfl⟩) (by simp [Arg.val])
    · split at h
      · next base d hdef =>
        obtain ⟨rb, hr, hk⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vb, hmb, hv⟩ := hA.defs _ _ hdef v hm
        exact reg hk (Or.inr ⟨_, _, hr, hmb, rfl⟩)
          (by simp [Arg.val, hv, Int64.toBitVec_ofBitVec])
      · next c hdef => exact ⟨.imm c, h, by simp [AddrArg.regs], (hA.defs _ _ hdef v hm).symm⟩
      · simp at h

/-! ## `Agree`/`Inv` plumbing -/

theorem Agree.consReg {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {sa : SymArg} {rl : RegLoc T.Reg T.VReg T.Cond}
    (hA : Agree T G nv st s σ) (h : RegLocOk T.mach G s sa rl) (hlt : symArgScopeOk nv sa = true) :
    Agree T G nv { st with regs := (sa, rl) :: st.regs } s σ :=
  { hA with
    regs := fun p hp => by rcases List.mem_cons.mp hp with rfl | hp <;> first | exact h | exact hA.regs p hp
    regs_lt := fun p hp => by rcases List.mem_cons.mp hp with rfl | hp <;> first | exact hlt | exact hA.regs_lt p hp }

theorem isGprTy_ne_pair {I : Isa} {t : Ty} (h : isGprTy I t = true) : ∀ a b, t ≠ .pair a b := by
  rintro a b rfl; simp [isGprTy] at h

/-- One new binder `⟨t, v, nv⟩`, with the vector-width trie possibly gaining an entry at `nv`. -/
theorem Agree.push {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) (t : Ty) (v : Val t) (vw' : Trie SlotWidth)
    (hvw0 : ∀ x < nv, vw'.find? x = st.vecWidths.find? x)
    (hvw : ∀ w, vw'.find? nv = some w → t.size ≤ w.bits ∧ ∃ a b, t = .pair a b)
    (hvw1 : ∀ x, nv < x → vw'.find? x = none)
    (hty : vw'.find? nv = none → ∀ a b, t ≠ .pair a b) :
    Agree T (⟨t, v, nv⟩ :: G) (nv + 1) { st with vecWidths := vw' } s σ := by
  have top : ∀ {t' : Ty} {v' : Val t'} {x}, ⟨t', v', x⟩ ∈ (⟨t, v, nv⟩ :: G : VCtx) → nv ≤ x →
      x = nv ∧ (⟨t', v'⟩ : Sigma Val) = ⟨t, v⟩ := fun hm hx => by
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm; exact ⟨rfl, rfl⟩
    · exact absurd (hA.ctx_lt _ hm) (Nat.not_lt.mpr hx)
  refine hA.extend (Nat.le_succ nv) (fun p hp => ?_) (fun p hp => ?_) (fun _ hp => List.mem_cons_of_mem _ hp)
    hvw0 (fun x w hx hle => ?_) (fun p hp hle hn => ?_)
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact Or.inr (Nat.le_refl _)
    · exact Or.inl hp
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (hA.ctx_lt p hp)
  · rcases Nat.eq_or_lt_of_le hle with rfl | hlt
    · exact ⟨Nat.lt_succ_self _, fun t' v' hm => by
        obtain ⟨-, he⟩ := top hm (Nat.le_refl _); cases he; exact hvw w hx⟩
    · simp [hvw1 x hlt] at hx
  · obtain ⟨h1, he⟩ := top (x := p.2.2) hp hle
    rw [show p.1 = t from congrArg Sigma.fst he]; exact hty (h1 ▸ hn)

theorem keep_of_frame {s s' : T.mach.MData} {gs : List T.Reg}
    (hk : T.mach.KeepsGpr s s' (gs ++ T.frame.scratch))
    (hgs : ∀ r ∈ gs, isAllocGpr T.toIsa hints.saved r = true) :
    ∀ r, isMoveGpr T.toIsa hints.saved r = false → T.mach.getGpr s' r = T.mach.getGpr s r := by
  intro r hr
  simp only [isMoveGpr, Bool.or_eq_false_iff] at hr
  refine hk r fun hm => ?_
  rcases List.mem_append.mp hm with hm | hm
  · simp [hgs r hm] at hr
  · simp [hm] at hr

theorem Inv.store {m : Mem 64} {s s' : T.mach.MData} {σ : List (BitVec 64)} {t : Ty}
    {a : BitVec 64} {v : Val t} (hI : Inv T hints s₀ ra n Rf m s σ)
    (hk : T.mach.KeepsGpr s s' T.frame.scratch) (hok : storeOk m t a)
    (hm : T.mach.mem s' = storeMem (T.mach.mem s) t a v) :
    Inv T hints s₀ ra n Rf (storeMem m t a v) s' σ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI
  refine ⟨h1, ?_, fun r hr hns => ?_, ?_, h5, h6⟩
  · rw [hk _ T.frameSpec.sp_disj.1]; exact h2
  · rw [hk r (fun h => (T.frameSpec.scratch_disj r h).2.1 hr)]; exact h3 r hr hns
  · rw [hm]; exact storeMem_frame h4 hok v

/-! ## Loads and stores -/

theorem lowerLoad_ok (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv ip : Nat}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {t : Ty} {a₁ : Arg Val i64} {a : Arg VNat i64}
    (hrel : ArgRel G i64 a₁ a) (hl : lowerLoad T.toIsa hints nv ip st t a = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ)
    {v : Val t} (hv : loadVal m t a₁.val = some v)
    (kont : ∀ s', Agree T (⟨t, v, nv⟩ :: G) (nv + 1) st' s' σ → Inv T hints s₀ ra n Rf m s' σ →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hspE := hspE
  have hload : ∀ (aa : AddrArg T.Reg), aa.eval (T.mach.getGpr s) = a₁.val →
      loadVal (T.mach.mem s) t (aa.eval (T.mach.getGpr s)) = some v :=
    fun aa hev => by rw [hev]; exact loadVal_frame hI.2.2.2.1 hv
  unfold lowerLoad at hl
  split at hl
  · next d _ =>
    split at hl
    · simp at hl
    · next hcond =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hcond
      obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
      cases heq
      obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
      refine T.gprSpec.load_spec hk (not_scratch_of_isAllocGpr hsv hcond.1) hreg (hload aa hev) hc
        fun s' ⟨hg, hm⟩ hfr => kont s' ?_ ?_
      · have hk := hA.kill hfr
        exact (hk.push t v _ (fun _ _ => rfl) (fun w h => absurd (hk.vw_lt _ _ h) (Nat.lt_irrefl _))
          (fun x hx => Option.eq_none_iff_forall_ne_some.mpr fun w h =>
            absurd (hk.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx)))
          (fun _ => isGprTy_ne_pair hcond.2)).consReg (sa := .var nv) (rl := .gpr d)
          (fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hg) (by simp [symArgScopeOk])
      · exact hI.keep hm (keep_of_frame (gs := [d]) hfr.1 (by simpa using hcond.1))
  · next vd _ =>
    obtain ⟨w, hw, hl⟩ := Option.bind_eq_some_iff.mp hl
    split at hl
    · simp at hl
    · next hcond =>
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hcond
      obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
      cases heq
      obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
      refine T.vecSpec.vload_spec hk (not_vecScratch_of_isAllocVec hcond) hreg (hload aa hev) hc
        fun s' ⟨hg, hm⟩ hfr => kont s' ?_ ?_
      · have hk := hA.kill hfr
        refine (hk.push t v _ (fun x hx => Trie.find?_insert_ne _ _ (Nat.ne_of_lt hx))
          (fun w' h => ?_) (fun x hx => ?_) (fun h => by simp [Trie.find?_insert_self] at h)).consReg (sa := .var nv)
          (rl := .vec vd) (fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hg.1, hg⟩)
          (by simp [symArgScopeOk])
        · simp only [Trie.find?_insert_self, Option.some.injEq] at h; subst h; exact vecWidth?_spec hw
        · rw [Trie.find?_insert_ne _ _ (Nat.ne_of_gt hx)]
          exact Option.eq_none_iff_forall_ne_some.mpr fun w h =>
            absurd (hk.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx))
      · exact hI.keep hm (keep_of_frame (gs := []) hfr.1 (by simp))
  · simp at hl

theorem lowerStore_ok (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    {G : VCtx} {nv : Nat} {vh : VariantHint}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {t : Ty} {v₁ : Arg Val t} {v : Arg VNat t}
    {a₁ : Arg Val i64} {a : Arg VNat i64} (hv : ArgRel G t v₁ v) (ha : ArgRel G i64 a₁ a)
    (hl : lowerStore T.toIsa st vh t v a = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ) (hok : storeOk m t a₁.val)
    (kont : ∀ s', Agree T G nv st' s' σ → Inv T hints s₀ ra n Rf (storeMem m t a₁.val v₁.val) s' σ →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hspE := hspE
  have hsok : ∀ (aa : AddrArg T.Reg), aa.eval (T.mach.getGpr s) = a₁.val →
      storeOk (T.mach.mem s) t (aa.eval (T.mach.getGpr s)) :=
    fun aa hev => by rw [hev]; exact storeOk_frame hI.2.2.2.1 hok
  cases t with
  | pair x y =>
    simp only [lowerStore] at hl
    obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
    cases heq
    obtain ⟨pa, hk, -, hpv, hp⟩ := tryArg_ok hA hv hta
    cases pa with
    | vec vs =>
      obtain ⟨aa, hk', hreg, hev⟩ := tryAddr_ok hA ha hk
      refine T.vecSpec.vstore_spec hk' hreg (hpv vs rfl) hp (hsok aa hev) hc
        fun s' hm hfr => kont s' (hA.kill hfr) ?_
      rw [hev] at hm
      exact hI.store hfr.1 hok hm
    | gpr _ | imm _ => simp at hk
  | bool | bits _ | float _ =>
    simp only [lowerStore] at hl
    split at hl
    · simp at hl
    · obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
      cases heq
      obtain ⟨pa, hk, hpg, -, hp⟩ := tryArg_ok hA hv hta
      obtain ⟨aa, hk', hreg, hev⟩ := tryAddr_ok hA ha hk
      refine T.gprSpec.store_spec hk' (fun r hr => ?_) hp (hsok aa hev) hc
        fun s' hm hfr => kont s' (hA.kill hfr) ?_
      · exact (List.mem_append.mp hr).elim (hpg r) (hreg r)
      · rw [hev] at hm
        exact hI.store hfr.1 hok hm

/-! ## Operations -/

/-- Per-destination typing facts checked by `resolveDsts`. -/
def DstsOk (I : Isa) : {ts : List Ty} → Tup (PDst I.Reg I.VReg I.Cond) ts → Prop
  | [], () => True
  | t :: _, (.gpr _, ds) => isGprTy I t = true ∧ DstsOk I ds
  | t :: _, (.vec _, ds) => (vecWidth? I t).isSome = true ∧ DstsOk I ds
  | _ :: _, (.flag _, ds) => DstsOk I ds

theorem resolveDsts_spec {I : Isa} {h : I.Hints} :
    ∀ {ts : List Ty} {nv : Nat} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts},
    resolveDsts I h ts nv = some dsts →
    (∀ r ∈ tupDstGprs dsts, isAllocGpr I h.saved r = true) ∧
      (∀ v ∈ tupDstVecs dsts, isAllocVec I v = true) ∧ DstsOk I dsts
  | [], _, _, _ => by simp [tupDstGprs, tupDstVecs, DstsOk]
  | t :: ts, nv, dsts, hr => by
    simp only [resolveDsts] at hr
    split at hr <;> (try split at hr) <;> (try (simp at hr; done))
    all_goals
      cases hr; have := resolveDsts_spec ‹resolveDsts _ _ _ _ = _›
      simp_all [tupDstGprs, tupDstVecs, DstsOk]

/-- Conclusion of `bindDsts_ok` for new binders `[nv, nv + len)`, old state `(regs, vw)`, result `r`. -/
def BindOk (T : Target) (G' : VCtx) (s' : T.mach.MData) (nv len : Nat)
    (regs : List (SymArg × RegLoc T.Reg T.VReg T.Cond)) (vw : Trie SlotWidth)
    (r : List (SymArg × RegLoc T.Reg T.VReg T.Cond) × Trie SlotWidth) : Prop :=
  (∀ p ∈ r.1, p ∈ regs ∨ (RegLocOk T.mach G' s' p.1 p.2 ∧ symArgScopeOk (nv + len) p.1 = true)) ∧
  (∀ x < nv, r.2.find? x = vw.find? x) ∧
  (∀ x w, r.2.find? x = some w → nv ≤ x → vw.find? x = some w ∨
    (x < nv + len ∧ ∀ t v, ⟨t, v, x⟩ ∈ G' → t.size ≤ w.bits ∧ ∃ a b, t = .pair a b)) ∧
  (∀ t v x, ⟨t, v, x⟩ ∈ G' → nv ≤ x → r.2.find? x = none → ∀ a b, t ≠ .pair a b)

theorem bindDsts_ok {G' : VCtx} {s' : T.mach.MData} :
    ∀ {ts : List Ty} (dsts : Tup (PDst T.Reg T.VReg T.Cond) ts) (rvs : Tup Val ts) (nv : Nat)
      (regs : List (SymArg × RegLoc T.Reg T.VReg T.Cond)) (vw : Trie SlotWidth),
    TRel (T.mach.PDstHolds s') dsts rvs → DstsOk T.toIsa dsts →
    (∀ t v x, ⟨t, v, x⟩ ∈ G' → nv ≤ x → ⟨t, v, x⟩ ∈ (Tup.zip rvs (Tup.levels ts nv) : VCtx)) →
    BindOk T G' s' nv ts.length regs vw (bindDsts T.toIsa dsts nv (regs, vw))
  | [], _, _, _, _, _, _, _, hG =>
    ⟨fun _ hp => Or.inl hp, fun _ _ => rfl, fun _ _ hx _ => Or.inl hx, fun t v x hm hx _ =>
      absurd (hG t v x hm hx) (by simp [Tup.zip])⟩
  | t :: ts, (d, ds), (rv, rvs), nv, regs, vw, .cons hd hds, hdo, hG => by
    have hG' : ∀ t v x, ⟨t, v, x⟩ ∈ G' → nv + 1 ≤ x →
        ⟨t, v, x⟩ ∈ (Tup.zip rvs (Tup.levels ts (nv + 1)) : VCtx) := fun t' v' x hm hx => by
      rcases List.mem_cons.mp (hG t' v' x hm (Nat.le_of_succ_le hx)) with he | he
      · cases he; exact absurd hx (Nat.lt_irrefl _)
      · exact he
    have top : ∀ t' v', ⟨t', v', nv⟩ ∈ G' → (⟨t', v'⟩ : Sigma Val) = ⟨t, rv⟩ := fun t' v' hm => by
      rcases List.mem_cons.mp (hG t' v' nv hm (Nat.le_refl _)) with he | he
      · cases he; rfl
      · have := (zip_levels_mem (G := []) (List.mem_append_left [] he)).resolve_left (by simp)
        exact absurd this.1 (Nat.not_succ_le_self _)
    have hsc : symArgScopeOk (nv + (ts.length + 1)) (.var nv) = true := by simp [symArgScopeOk]
    have hlen : nv + 1 + ts.length = nv + (ts.length + 1) := by omega
    have step : ∀ (rl : RegLoc T.Reg T.VReg T.Cond) (vw' : Trie SlotWidth), DstsOk T.toIsa ds →
        RegLocOk T.mach G' s' (.var nv) rl → (∀ x < nv, vw'.find? x = vw.find? x) →
        (∀ x w, vw'.find? x = some w → nv ≤ x → vw.find? x = some w ∨ (x < nv + (ts.length + 1) ∧
          ∀ t v, ⟨t, v, x⟩ ∈ G' → t.size ≤ w.bits ∧ ∃ a b, t = .pair a b)) →
        (vw'.find? nv = none → ∀ a b, t ≠ .pair a b) →
        BindOk T G' s' nv (ts.length + 1) regs vw
          (bindDsts T.toIsa ds (nv + 1) ((.var nv, rl) :: regs, vw')) := by
      intro rl vw' hdo' hrl h0 h1 h2
      obtain ⟨ih1, ih2, ih3, ih4⟩ := bindDsts_ok ds rvs (nv + 1) ((.var nv, rl) :: regs) vw' hds hdo' hG'
      refine ⟨fun p hp => ?_, fun x hx => ?_, fun x w hx hle => ?_, fun t' v' x hm hle hn => ?_⟩
      · rcases ih1 p hp with hp | hp
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact Or.inr ⟨hrl, hsc⟩
          · exact Or.inl hp
        · exact Or.inr ⟨hp.1, hlen ▸ hp.2⟩
      · rw [ih2 x (Nat.lt_succ_of_lt hx), h0 x hx]
      · rcases Nat.eq_or_lt_of_le hle with rfl | hlt
        · rw [ih2 _ (Nat.lt_succ_self _)] at hx; exact h1 _ _ hx (Nat.le_refl _)
        · rcases ih3 x w hx hlt with hx | hx
          · exact h1 x w hx (Nat.le_of_lt hlt)
          · exact Or.inr ⟨hlen ▸ hx.1, hx.2⟩
      · rcases Nat.eq_or_lt_of_le hle with rfl | hlt
        · rw [ih2 _ (Nat.lt_succ_self _)] at hn
          cases top t' v' hm; exact h2 hn
        · exact ih4 t' v' x hm hlt hn
    cases d with
    | gpr r =>
      exact step (.gpr r) vw hdo.2 (fun t' v' hm => by cases top t' v' hm; exact hd)
        (fun _ _ => rfl) (fun _ _ h _ => Or.inl h) (fun _ => isGprTy_ne_pair hdo.1)
    | vec vr =>
      obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp hdo.1
      have e : (bindDsts T.toIsa (ts := t :: ts) (PDst.vec vr, ds) nv (regs, vw)) =
          bindDsts T.toIsa ds (nv + 1) ((.var nv, .vec vr) :: regs, vw.insert nv w0) := by
        simp [bindDsts, hw0]
      rw [e]
      refine step (.vec vr) _ hdo.2 (fun t' v' hm => by cases top t' v' hm; exact ⟨hd.1, hd⟩)
        (fun x hx => Trie.find?_insert_ne _ _ (Nat.ne_of_lt hx)) (fun x w hx hle => ?_)
        (fun h => by simp [Trie.find?_insert_self] at h)
      rw [Trie.find?_insert] at hx; split at hx
      · cases hx; subst_vars
        exact Or.inr ⟨by omega, fun t' v' hm => by cases top t' v' hm; exact vecWidth?_spec hw0⟩
      · exact Or.inl hx
    | flag c =>
      exact step (.flag c) vw hdo (fun t' v' hm => by cases top t' v' hm; exact hd.symm)
        (fun _ _ => rfl) (fun _ _ h _ => Or.inl h) (fun _ => by simp)

theorem lowerOp_ok (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv ip : Nat}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {ts : List Ty} {op₁ : Op Val ts} {op : Op VNat ts}
    (hop : OpRel G op₁ op) (hl : lowerOp T.toIsa hints nv ip st op = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ)
    {P : Tup Val ts → Prop} (hwp : op₁.wp P)
    (kont : ∀ (rvs : Tup Val ts) s', P rvs →
      Agree T (Tup.zip rvs (Tup.levels ts nv) ++ G) (nv + ts.length) st' s' σ →
      Inv T hints s₀ ra n Rf m s' σ → T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hspE := hspE
  cases hop with
  | mk code hargs =>
  rename_i sig args₁ args
  unfold lowerOp at hl
  split at hl
  · cases hd : recordDef code args with
    | none => simp [hd] at hl
    | some df =>
      simp only [hd, Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      obtain ⟨rvs, hP, hrs, hdef⟩ := recordDef_elide_ok hargs hA.ctx_lt hwp hd
      subst hrs
      rcases rvs with ⟨rv, ⟨⟩⟩
      have hvw0 : ∀ x < nv, st.vecWidths.find? x = st.vecWidths.find? x := fun _ _ => rfl
      have hvw : ∀ w, st.vecWidths.find? nv = some w →
          i64.size ≤ w.bits ∧ ∃ a b, i64 = .pair a b := fun w hw =>
        absurd (hA.vw_lt _ _ hw) (Nat.lt_irrefl _)
      have hvw1 : ∀ x, nv < x → st.vecWidths.find? x = none := fun x hx =>
        Option.eq_none_iff_forall_ne_some.mpr fun w hw =>
          absurd (hA.vw_lt _ _ hw) (Nat.not_lt.mpr (Nat.le_of_lt hx))
      have hA1 := hA.push i64 rv st.vecWidths hvw0 hvw hvw1 (by intro _ a b h; cases h)
      refine kont (rv, ()) s hP
        { hA1 with
          defs := fun x d hx => by
            rw [Trie.find?_insert] at hx; split at hx
            · cases hx; subst_vars; exact hdef
            · exact hA1.defs x d hx
          defs_lt := fun x d hx => by
            rw [Trie.find?_insert] at hx; split at hx
            · subst_vars; exact Nat.lt_succ_self _
            · exact hA1.defs_lt x d hx }
        hI
  simp only [Option.bind_eq_some_iff] at hl
  obtain ⟨dsts, hdst, hl⟩ := hl
  obtain ⟨⟨c', clob, isVec⟩, hpick, heq⟩ := Option.map_eq_some_iff.mp hl
  cases heq
  obtain ⟨pas, hk, hpg, hpv, hph⟩ := pickPArgs_ok hA hargs hpick
  obtain ⟨hdg, hdv, hdo⟩ := resolveDsts_spec hdst
  have hdg' : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch :=
    fun r hr => not_scratch_of_isAllocGpr hsv (hdg r hr)
  have hdv' : ∀ v ∈ tupDstVecs dsts, v ∉ T.vec.vecScratch :=
    fun v hv => not_vecScratch_of_isAllocVec (hdv v hv)
  let G' : Tup Val ts → VCtx := fun rvs => Tup.zip rvs (Tup.levels ts nv) ++ G
  have hwp' : code.wp (vals args₁) (fun rvs => P rvs ∧ ∀ df, recordDef code args = some df →
      0 < ts.length ∧ DefOk (G' rvs) nv df) := by
    cases hd : recordDef code args with
    | none => exact OpCode.wp_mono code _ (fun r hp => ⟨hp, by simp⟩) hwp
    | some df =>
      exact OpCode.wp_mono code _ (fun r hp => ⟨hp.1, fun df' he => by cases he; exact hp.2⟩)
        (wp_recordDef hargs hA.ctx_lt hwp hd)
  have fin : ∀ s' (vC : List T.VReg), (∃ rvs, (P rvs ∧ ∀ df, recordDef code args = some df →
        0 < ts.length ∧ DefOk (G' rvs) nv df) ∧ TRel (T.mach.PDstHolds s') dsts rvs) →
      T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) vC clob →
      vC = (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) →
      T.mach.Run host (k + c'.length) s' post := by
    rintro s' vC ⟨rvs, ⟨hP, hdef⟩, hdh⟩ hm hfr rfl
    have hGtop : ∀ t v x, ⟨t, v, x⟩ ∈ G' rvs → nv ≤ x →
        ⟨t, v, x⟩ ∈ (Tup.zip rvs (Tup.levels ts nv) : VCtx) := fun t v x hm hx => by
      rcases List.mem_append.mp hm with hm | hm
      · exact hm
      · exact absurd hx (Nat.not_le_of_lt (hA.ctx_lt _ hm))
    have hK := hA.kill hfr
    obtain ⟨hb1, hb2, hb3, hb4⟩ := bindDsts_ok dsts rvs nv
      (killRegs T.toIsa (tupDstGprs dsts ++ T.frame.scratch)
        (if isVec then tupDstVecs dsts ++ T.vec.vecScratch else []) clob st.regs)
      st.vecWidths hdh hdo hGtop
    have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
      Option.eq_none_iff_forall_ne_some.mpr fun w h => absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
    have hA1 := hK.extend (G' := G' rvs) (nv' := nv + ts.length) (Nat.le_add_right _ _)
      (fun p hp => (zip_levels_mem hp).imp id (·.1))
      (fun p hp => (zip_levels_mem hp).elim (fun h => Nat.lt_of_lt_of_le (hA.ctx_lt p h)
        (Nat.le_add_right _ _)) (·.2))
      (fun p hp => List.mem_append_right _ hp) hb2
      (fun x w hx hle => (hb3 x w hx hle).resolve_left (by simp [hnone x hle]))
      (fun p hp hle hn => hb4 p.1 p.2.1 p.2.2 hp hle hn)
    have hr1 := fun p hp => (hb1 p hp).elim (fun hp => ⟨hA1.regs p hp, hA1.regs_lt p hp⟩) id
    have hd1 : ∀ x d, Trie.find? (match recordDef code args with
        | some df => st.defs.insert nv df | none => st.defs) x = some d →
        DefOk (G' rvs) x d ∧ x < nv + ts.length := by
      intro x d hx; split at hx
      · rw [Trie.find?_insert] at hx; split at hx
        · cases hx; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_add_of_pos_right (hdef _ ‹_›).1⟩
        · exact ⟨hA1.defs x d hx, hA1.defs_lt x d hx⟩
      · exact ⟨hA1.defs x d hx, hA1.defs_lt x d hx⟩
    exact kont rvs s' hP ⟨hA1.ctx_lt, fun p hp => (hr1 p hp).1, hA1.slots, fun x d hx => (hd1 x d hx).1,
      hA1.vw, fun p hp => (hr1 p hp).2, hA1.slots_lt, fun x d hx => (hd1 x d hx).2, hA1.vw_lt, hA1.vt⟩
      (hI.keep hm (keep_of_frame hfr.1 hdg))
  split at hk <;> (try rcases orElse_eq_some hk with hk | hk) <;>
    obtain ⟨⟨c'', cl⟩, hop', he⟩ := Option.map_eq_some_iff.mp hk <;> cases he
  · exact T.gprSpec.op_spec hop' hpg hdg' hph hwp' hc fun s' ⟨hQ, hm⟩ hfr => fin s' [] hQ hm hfr rfl
  all_goals exact T.vecSpec.vop_spec hop' hpg hpv hdg' hdv' hph hwp' hc
              fun s' ⟨hQ, hm⟩ hfr => fin s' _ hQ hm hfr rfl

end Lemmas

/-! ## Part B: structural `LabelsUnique` (Guardrail 5) -/

section Labels
variable {I : Isa}

/-- No directive of `c` is a label. -/
def NoLab (I : Isa) (c : List I.Directive) : Prop := ∀ l, I.frame.label l ∉ c

/-- Target-side side condition for `LabelsUnique`: `label` is injective and no `Isa` snippet emits
a label directive. -/
structure LabelClean (I : Isa) : Prop where
  label_inj : ∀ a b, I.frame.label a = I.frame.label b → a = b
  (mov : ∀ d s, NoLab I (I.gpr.mov d s)) (movi : ∀ d c, NoLab I (I.gpr.movi d c))
  (setcc : ∀ d c, NoLab I (I.gpr.setcc d c)) (jmp : ∀ l, NoLab I (I.gpr.jmp l))
  (jcc : ∀ c l, NoLab I (I.gpr.jcc c l)) (jnzGpr : ∀ r l, NoLab I (I.gpr.jnzGpr r l).1)
  op : ∀ {sig rs : List Ty} (code : OpCode sig rs) pas dsts vh c cl,
    I.gpr.op code pas dsts vh = some (c, cl) → NoLab I c
  (load : ∀ t r a c cl, I.gpr.load t r a = some (c, cl) → NoLab I c)
  (store : ∀ t pa a c cl, I.gpr.store t pa a = some (c, cl) → NoLab I c)
  (clearFlags : NoLab I I.gpr.clearFlags) (vmov : ∀ w d s, NoLab I (I.vec.vmov w d s))
  (vmovi : ∀ w d c code, I.vec.vmovi w d c = some code → NoLab I code)
  (vslotSt : ∀ w i s, NoLab I (I.vec.vslotSt w i s)) (vslotLd : ∀ w d i, NoLab I (I.vec.vslotLd w d i))
  vop : ∀ {sig rs : List Ty} (code : OpCode sig rs) pas dsts vh c cl,
    I.vec.vop code pas dsts vh = some (c, cl) → NoLab I c
  (vload : ∀ t d a c cl, I.vec.vload t d a = some (c, cl) → NoLab I c)
  (vstore : ∀ t s a c cl, I.vec.vstore t s a = some (c, cl) → NoLab I c)
  (prologue : ∀ n, NoLab I (I.frame.prologue n).1) (epilogue : ∀ n, NoLab I (I.frame.epilogue n).1)
  (slotSt : ∀ i r, NoLab I (I.frame.slotSt i r)) (slotLd : ∀ r i, NoLab I (I.frame.slotLd r i))
  (canonAbi : ∀ t r, NoLab I (I.frame.canonAbi t r).1) (call : ∀ f, NoLab I (I.frame.call f))
  (exitJmp : ∀ f, NoLab I (I.frame.exitJmp f)) (ret : NoLab I I.frame.ret)

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
  have := congrArg (List.foldl digF 0) (List.append_cancel_left (List.append_cancel_left h'))
  rwa [natDigits_fold _ _ _ (Nat.lt_succ_self a), natDigits_fold _ _ _ (Nat.lt_succ_self b)] at this

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
  (LabOk.clean (S := fun _ => False) ha).append h (fun _ h _ => h) (fun _ h => h.elim False.elim id)

/-! ### Snippet code is label-free -/

theorem tryArg_some {st : SymState I} {pref : List I.Cond} {α : Type} {t : Ty} {a : Arg VNat t}
    {k : PArg I.Reg I.VReg I.Cond t → Option α} {res : α} (h : tryArg I st pref t a k = some res) :
    ∃ pa, k pa = some res := by
  have fs : ∀ {β γ : Type} {l : List β} {g : β → Option α} {f : γ → PArg I.Reg I.VReg I.Cond t},
      (∀ b, g b = some res → ∃ x, k (f x) = some res) → l.findSome? g = some res →
      ∃ pa, k pa = some res := fun hg h => by
    obtain ⟨b, -, hb⟩ := List.exists_of_findSome?_eq_some h; obtain ⟨x, hx⟩ := hg b hb; exact ⟨_, hx⟩
  have gpr : ∀ {sa}, tryGpr I st.regs sa (k ∘ .gpr) = some res → ∃ pa, k pa = some res :=
    fs (f := PArg.gpr) fun ⟨_, rl⟩ hb => by
      cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb
  have vec : ∀ {sa}, tryVec I st.regs sa (k ∘ .vec) = some res → ∃ pa, k pa = some res :=
    fs (f := PArg.vec) fun ⟨_, rl⟩ hb => by
      cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb
  cases t with
  | bool =>
    have flag : ∀ {sa}, tryFlag I st.regs pref sa (k ∘ .flag) = some res → ∃ pa, k pa = some res := by
        intro sa h; rcases orElse_eq_some h with h | h
        · obtain ⟨c, -, hb⟩ := List.exists_of_findSome?_eq_some h
          split at hb <;> first | exact ⟨_, hb⟩ | simp at hb
        · exact fs (f := PArg.flag) (fun ⟨_, rl⟩ hb => by
            cases rl <;> simp only at hb <;> (try split at hb) <;> first | exact ⟨_, hb⟩ | simp at hb) h
    cases a with
    | var x => rcases orElse_eq_some h with h | h <;> first | exact flag h | exact gpr h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact flag h
      rcases orElse_eq_some h with h | h <;> first | exact ⟨_, h⟩ | exact gpr h
  | bits w =>
    cases a with
    | var x => exact gpr h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact ⟨_, h⟩
      · split at h <;> first | exact gpr h | simp at h
  | pair x y =>
    cases a with
    | var x => exact vec h
    | imm b =>
      rcases orElse_eq_some h with h | h
      · exact ⟨_, h⟩
      · split at h <;> first | exact vec h | simp at h
  | float _ => simp [tryArg] at h

theorem pickPArgs_some {st : SymState I} {pref : List I.Cond} {α : Type} :
    ∀ {sig : List Ty} {args : Tup (Arg VNat) sig}
      {k : Tup (PArg I.Reg I.VReg I.Cond) sig → Option α} {res : α},
    pickPArgs I st pref args k = some res → ∃ pas, k pas = some res
  | [], (), _, _, h => ⟨(), h⟩
  | _ :: _, (_, _), _, _, h => by
    obtain ⟨pa, h⟩ := tryArg_some h
    obtain ⟨pas, h⟩ := pickPArgs_some h
    exact ⟨_, h⟩

theorem tryAddr_some {st : SymState I} {vh : VariantHint} {α : Type} {a : Arg VNat i64}
    {k : AddrArg I.Reg → Option α} {res : α} (h : tryAddr I st vh a k = some res) :
    ∃ aa, k aa = some res := by
  cases a with
  | imm c =>
    rcases orElse_eq_some h with h | h
    · exact ⟨_, h⟩
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
  | var x =>
    simp only [tryAddr] at h
    rcases orElse_eq_some h with h | h
    · split at h <;> (try split at h) <;>
        first | (obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩) | simp at h
    rcases orElse_eq_some h with h | h
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
    · split at h
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact ⟨_, h⟩
      · exact ⟨_, h⟩
      · simp at h

variable (hcl : LabelClean I)
include hcl

theorem execMove_clean {nslots : Nat} {saved : List I.Reg} {mv : I.Move} {st st' : SymState I}
    {c : List I.Directive} (h : execMove I nslots saved mv st = some (c, st')) : NoLab I c := by
  cases mv <;> simp only [execMove] at h <;> (repeat' split at h) <;>
    first | (simp at h; done) | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h)
  all_goals first
    | exact hcl.mov _ _
    | exact hcl.movi _ _
    | exact hcl.slotLd _ _
    | exact hcl.slotSt _ _
    | exact hcl.setcc _ _
    | exact hcl.vmov _ _ _
    | exact hcl.vslotLd _ _ _
    | exact hcl.vslotSt _ _ _
    | exact hcl.vmovi _ _ _ _ ‹_›

theorem execMoves_clean {nslots : Nat} {saved : List I.Reg} :
    ∀ {mvs : List I.Move} {st st' : SymState I} {c : List I.Directive},
    execMoves I nslots saved mvs st = some (c, st') → NoLab I c
  | [], _, _, _, h => by simp only [execMoves, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact NoLab.nil
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

theorem shuffle_clean {nslots : Nat} {saved : List I.Reg} {st st' : SymState I}
    {tgts : List (SymArg × I.Loc)} {c : List I.Directive}
    (hs : shuffle I nslots saved st tgts = some (c, st')) : NoLab I c := by
  simp only [shuffle] at hs
  split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact NoLab.nil
  · split at hs
    · simp at hs
    · split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.1]; exact execMoves_clean hcl ‹_›
      · simp at hs

theorem canonAbiCode_clean : ∀ {ts : List Ty} (locs : Tup (AbiReg I.Reg I.VReg) ts),
    NoLab I (canonAbiCode I locs)
  | [], () => NoLab.nil
  | _ :: _, (.gpr _, locs) => (hcl.canonAbi _ _).append (canonAbiCode_clean locs)
  | _ :: _, (.vec _, locs) => canonAbiCode_clean locs

theorem restoreCs_clean : ∀ (base : Nat) (rs : List I.Reg), NoLab I (restoreCs I base rs)
  | _, [] => NoLab.nil
  | _, _ :: rs => (hcl.slotLd _ _).append (restoreCs_clean _ rs)

theorem saveCs_clean : ∀ (base : Nat) (rs : List I.Reg), NoLab I (saveCs I base rs)
  | _, [] => NoLab.nil
  | _, _ :: rs => (hcl.slotSt _ _).append (saveCs_clean _ rs)

theorem lowerOp_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {ts : List Ty}
    {op : Op VNat ts} {c : List I.Directive} (hl : lowerOp I h nv ip st op = some (c, st')) :
    NoLab I c := by
  unfold lowerOp at hl
  split at hl
  · cases hd : recordDef op.code op.args <;> simp [hd] at hl
    rcases hl with ⟨rfl, -⟩; exact NoLab.nil
  simp only [Option.bind_eq_some_iff] at hl
  obtain ⟨dsts, -, hl⟩ := hl
  obtain ⟨⟨c', cl, iv⟩, hp, he⟩ := Option.map_eq_some_iff.mp hl
  cases he
  obtain ⟨pas, hk⟩ := pickPArgs_some hp
  have hv : (I.vec.vop op.code pas dsts (h.variant.getD ip .default)).map
      (fun x => (x.1, x.2, true)) = some (c', cl, iv) → NoLab I c' := fun hk => by
    obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk; cases he; exact hcl.vop _ _ _ _ _ _ hop
  split at hk
  · rcases orElse_eq_some hk with hk | hk
    · obtain ⟨⟨_, _⟩, hop, he⟩ := Option.map_eq_some_iff.mp hk; cases he; exact hcl.op _ _ _ _ _ _ hop
    · exact hv hk
  · exact hv hk

theorem lowerLoad_clean {h : I.Hints} {nv ip : Nat} {st st' : SymState I} {t : Ty}
    {a : Arg VNat i64} {c : List I.Directive} (hl : lowerLoad I h nv ip st t a = some (c, st')) :
    NoLab I c := by
  unfold lowerLoad at hl
  split at hl
  · split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.load _ _ _ _ _ hk
  · obtain ⟨_, -, hl⟩ := Option.bind_eq_some_iff.mp hl
    split at hl; · simp at hl
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨_, hk⟩ := tryAddr_some hta; exact hcl.vload _ _ _ _ _ hk
  · simp at hl

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
    obtain ⟨⟨_, _⟩, hta, he⟩ := Option.map_eq_some_iff.mp hl; cases he
    obtain ⟨_, hk⟩ := tryArg_some hta; obtain ⟨_, hk⟩ := tryAddr_some hk; exact hcl.store _ _ _ _ _ hk

omit hcl in
theorem lowerTail_spec {h : I.Hints} {st : SymState I} {mc tail : List I.Directive} {ts : List Ty}
    {args : Tup (Arg VNat) ts} {locs : Tup (AbiReg I.Reg I.VReg) ts} {nv nl ip : Nat}
    {c : List I.Directive} {nv' nl' ip' : Nat}
    (hl : lowerTail I h st mc tail args locs nv nl ip = .ok (c, nv', nl', ip')) :
    nv' = nv ∧ nl' = nl ∧ (LabelClean I → NoLab I mc → NoLab I tail → NoLab I c) := by
  unfold lowerTail at hl; repeat' (split at hl <;> try (simp at hl; done))
  simp only [Except.ok.injEq, Prod.mk.injEq] at hl; obtain ⟨rfl, rfl, rfl, -⟩ := hl
  exact ⟨rfl, rfl, fun hcl hm ht => ((((hm.append (shuffle_clean hcl ‹_›)).append
    (canonAbiCode_clean hcl _)).append (restoreCs_clean hcl _ _)).append (hcl.epilogue _)).append ht⟩

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
    {b : Expr VNat LNat rs} {br c₁ c₂ : List I.Directive} {nv₂ nl₂ ip₂ : Nat} {c : List I.Directive}
    {nv' nl' ip' : Nat} (h : finishJnzBranch I fn nl tgt b br c₁ c₂ nv₂ nl₂ ip₂ = .ok (c, nv', nl', ip')) :
    nv' = nv₂ ∧ nl' = nl₂ ∧ (c = br ++ c₁ ∨ c = br ++ c₁ ++ [I.frame.label (lname fn nl)] ++ c₂) := by
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
      (∀ l, S l → T l → False) → LabOk I (lrange fn nl d) (br ++ x ++ [I.frame.label (lname fn nl)] ++ y) := by
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
      (fun l h => lrange_mono h (by omega) (Nat.le_refl _)) (fun l h1 h2 => lrange_disj h1 h2 (by omega))
  · exact (h₂.pre hbr).mono fun l h => m h (by omega) (by omega)
  · exact three h₂ h₁ (fun l h => lrange_mono h (by omega) (Nat.le_refl _))
      (fun l h => lrange_mono h (Nat.le_refl _) (by omega)) (fun l h1 h2 => lrange_disj h1 h2 (by omega))

mutual
/-- `lowerExpr` is monotone in `nv`/`nl`, and (for a `LabelClean` ISA) its labels are distinct
`lname fn j` with `nl ≤ j < nl'`. -/
theorem lowerExpr_labels {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} :
    ∀ (e : Expr VNat LNat rs) (nv nl ip : Nat) (st : SymState I) (ft : Option Nat)
      (c : List I.Directive) (nv' nl' ip' : Nat),
    lowerExpr I h E fn e nv nl ip st ft = .ok (c, nv', nl', ip') →
    nv ≤ nv' ∧ nl ≤ nl' ∧ (LabelClean I → LabOk I (lrange fn nl nl') c)
  | .let_ op k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl => (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerOp_clean hcl ‹_›))⟩
  | .load t a k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl => (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerLoad_clean hcl ‹_›))⟩
  | .store v a k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨h1, h2, fun hcl => (h3 hcl).pre ((stepPre_clean hcl ‹_›).append (lowerStore_clean hcl ‹_›))⟩
  | .call f args k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he; obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr
    exact ⟨by omega, h2, fun hcl => (h3 hcl).pre ((((stepPre_clean hcl ‹_›).append
      (shuffle_clean hcl ‹_›)).append (canonAbiCode_clean hcl _)).append (hcl.call _))⟩
  | .jnz (.imm b) t e, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; split at he <;> try (simp at he; done)
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    rcases ite_cases hr with hr | hr <;> obtain ⟨h1, h2, h3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ hr <;>
      exact ⟨h1, h2, fun hcl => (h3 hcl).pre (stepPre_clean hcl ‹_›)⟩
  | .jnz (.var cx) t e, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    split at he <;> try (simp at he; done)
    split at he <;> try (simp at he; done)
    split at he <;> try (simp at he; done)
    rename_i _ ce nv₁ nl₁ ip₁ he₁
    split at he <;> try (simp at he; done)
    rename_i _ ct nv₂ nl₂ ip₂ he₂
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he₂
    rcases ite_cases hr with hr | hr <;> obtain ⟨rfl, rfl, hc⟩ := finishJnz_ok hr
    · refine ⟨by omega, by omega, fun hcl => (LabOk.jnz hcl ?_ ⟨Nat.lt_succ_self _, a2, b2⟩ (a3 hcl)
        (b3 hcl) (hc.elim (fun h => Or.inr (Or.inr (Or.inl h))) fun h => Or.inr (Or.inr (Or.inr h)))).pre
        (stepPre_clean hcl ‹_›)⟩
      first | (cases ‹Sum I.Cond I.Reg› <;> simp only [jnzSetup] <;> first | exact hcl.jcc _ _ | exact hcl.jnzGpr _ _) | (split <;> first | exact hcl.jcc _ _ | exact hcl.jnzGpr _ _)
    · refine ⟨by omega, by omega, fun hcl => (LabOk.jnz hcl ?_ ⟨Nat.lt_succ_self _, a2, b2⟩ (a3 hcl)
        (b3 hcl) (hc.elim Or.inl fun h => Or.inr (Or.inl h))).pre (stepPre_clean hcl ‹_›)⟩
      first | (cases ‹Sum I.Cond I.Reg› <;> simp only [jnzSetup] <;> first | exact hcl.jcc _ _ | exact hcl.jnzGpr _ _) | (split <;> first | exact hcl.jcc _ _ | exact hcl.jnzGpr _ _)
  | .jump j args, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    repeat' (split at he <;> try (simp at he; done))
    all_goals
      simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, -⟩ := he
      refine ⟨Nat.le_refl _, Nat.le_refl _, fun hcl => LabOk.clean ((((stepPre_clean hcl ‹_›).append
        (shuffle_clean hcl ‹_›))).append ?_)⟩
      first | exact NoLab.nil | exact hcl.jmp _
  | .ret vs, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; split at he <;> try (simp at he; done)
    obtain ⟨rfl, rfl, h3⟩ := lowerTail_spec he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun hcl => LabOk.clean (h3 hcl (stepPre_clean hcl ‹_›) hcl.ret)⟩
  | .exit f args, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he; repeat' (split at he <;> try (simp at he; done))
    obtain ⟨rfl, rfl, h3⟩ := lowerTail_spec he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun hcl =>
      LabOk.clean (h3 hcl (stepPre_clean hcl ‹_›) (hcl.exitJmp _))⟩
  | .hlt, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ => LabOk.clean NoLab.nil⟩
  | .group (sig := sig) bodies k, nv, nl, ip, st, ft, c, nv', nl', ip', he => by
    simp only [lowerExpr] at he
    split at he <;> try (simp at he; done)
    rename_i ck nv₁ nl₁ ip₁ he₁
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    refine ⟨by omega, by omega, fun hcl => (a3 hcl).append (b3 hcl a2) (fun l h1 h2 => ?_) (fun l h => ?_)⟩
    · rcases h2 with h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
    · rcases h with h | h | h <;> exact lrange_mono h (by omega) (by omega)

/-- `lowerBlocks` analogue: block labels `lname fn j` for `lid ≤ j < lid + sig.length`, plus body
labels in `[nl, nl')`. -/
theorem lowerBlocks_labels {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks VNat LNat rs sig) (lid nv nl ip : Nat)
      (defs : Trie DefFact) (vw : Trie SlotWidth) (ft : Option Nat) (c : List I.Directive)
      (nv' nl' ip' : Nat),
    lowerBlocks I h E fn bs lid nv nl ip defs vw ft = .ok (c, nv', nl', ip') →
    nv ≤ nv' ∧ nl ≤ nl' ∧ (LabelClean I → lid + sig.length ≤ nl →
      LabOk I (fun l => lrange fn lid (lid + sig.length) l ∨ lrange fn nl nl' l) c)
  | _, .nil, lid, nv, nl, ip, defs, vw, ft, c, nv', nl', ip', he => by
    simp only [lowerBlocks, Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, -⟩ := he
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => LabOk.clean NoLab.nil⟩
  | _, .cons (sig := sig) b bs, lid, nv, nl, ip, defs, vw, ft, c, nv', nl', ip', he => by
    simp only [lowerBlocks] at he
    repeat' (split at he <;> try (simp at he; done))
    rename_i cb nv₁ nl₁ ip₁ he₁
    obtain ⟨c0, hr, rfl⟩ := prepend_ok he
    obtain ⟨a1, a2, a3⟩ := lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he₁
    obtain ⟨b1, b2, b3⟩ := lowerBlocks_labels _ _ _ _ _ _ _ _ _ _ _ _ hr
    refine ⟨by omega, by omega, fun hcl hlid => ?_⟩
    simp only [List.length_cons] at hlid ⊢
    have hl : LabOk I (lrange fn lid (lid + 1)) [I.frame.label (lname fn lid)] :=
      (LabOk.single hcl _).mono fun l hl => ⟨lid, Nat.le_refl _, Nat.lt_succ_self _, hl⟩
    refine (hl.append ((a3 hcl).append (b3 hcl (by omega)) (fun l h1 h2 => ?_) (fun l h => h))
      (fun l h1 h2 => ?_) (fun l h => ?_))
    · rcases h2 with h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
    · rcases h2 with h2 | h2 | h2 <;> exact lrange_disj h1 h2 (by omega)
    · rcases h with h | h | h | h <;> first
        | exact Or.inl (lrange_mono h (by omega) (by omega)) | exact Or.inr (lrange_mono h (by omega) (by omega))
end

theorem lowerExpr_nv_le {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} {e : Expr VNat LNat rs}
    {nv nl ip : Nat} {st : SymState I} {ft : Option Nat} {c : List I.Directive} {nv' nl' ip' : Nat}
    (he : lowerExpr I h E fn e nv nl ip st ft = .ok (c, nv', nl', ip')) : nv ≤ nv' ∧ nl ≤ nl' :=
  have hl := lowerExpr_labels e nv nl ip st ft c nv' nl' ip' he
  ⟨hl.1, hl.2.1⟩

theorem lowerBlocks_nv_le {h : I.Hints} {E : Ext} {fn : Sym} {rs : List Ty} {sig : List (List Ty)}
    {bs : Blocks VNat LNat rs sig} {lid nv nl ip : Nat} {defs : Trie DefFact} {vw : Trie SlotWidth}
    {ft : Option Nat} {c : List I.Directive} {nv' nl' ip' : Nat}
    (he : lowerBlocks I h E fn bs lid nv nl ip defs vw ft = .ok (c, nv', nl', ip')) :
    nv ≤ nv' ∧ nl ≤ nl' :=
  have hl := lowerBlocks_labels bs lid nv nl ip defs vw ft c nv' nl' ip' he
  ⟨hl.1, hl.2.1⟩

theorem lowerFn_labOk {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (hf : lowerFn I hints E f = .ok code) :
    LabOk I (fun l => l = f.name ∨ ∃ j, l = lname f.name j) code := by
  unfold lowerFn at hf
  repeat' (split at hf <;> try (simp at hf; done))
  rename_i c _ _ _ he
  simp only [Except.ok.injEq] at hf; subst hf
  have h3 := (lowerExpr_labels _ _ _ _ _ _ _ _ _ _ he).2.2 hcl
  refine (LabOk.single hcl f.name).append (h3.pre ((hcl.prologue _).append (saveCs_clean hcl _ _)))
    (fun l h1 h2 => ?_) (fun l h => ?_)
  · obtain ⟨j, -, -, rfl⟩ := h2; exact lname_ne h1
  · exact h.imp id fun ⟨j, _, _, e⟩ => ⟨j, e⟩

/-- Guardrail 5: labels of a lowered function are pairwise distinct (structurally, no `decide`). -/
theorem lowerFn_labelsUnique {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (h : lowerFn I hints E f = .ok code) :
    ∀ (i j : Nat) l, code[i]? = some (I.frame.label l) → code[j]? = some (I.frame.label l) → i = j :=
  (lowerFn_labOk hcl h).1

theorem lowerFn_label_mem {hints : I.Hints} {E : Ext} {f : Fn} {code : List I.Directive}
    (hcl : LabelClean I) (h : lowerFn I hints E f = .ok code) {i : Nat} {l : Sym}
    (hi : code[i]? = some (I.frame.label l)) : l = f.name ∨ ∃ j, l = lname f.name j :=
  (lowerFn_labOk hcl h).2 l (List.mem_of_getElem? hi)

end Labels2

end Rega
end LeanQbe.T
