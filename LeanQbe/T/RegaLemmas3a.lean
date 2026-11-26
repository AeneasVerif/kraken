module

public import LeanQbe.T.RegaLemmas1
public import LeanQbe.T.RegaLemmasCmpReuse
public import LeanQbe.T.RegaLemmas2
public import LeanQbe.T.WPLemmas

/-!
# `RegaLemmas` Part 3a: Operands, Loads/Stores, and Operation Sub-Lemmas

`tryArg_ok`, `pickPArgs_ok`, `tryAddr_ok`, `lowerLoad_ok`, `lowerStore_ok`, `bindDsts_ok`,
`tryFuseCmp_ok`, `tryLoadSext_ok`, `normCmpOp_ok`, `recordBoolDef_ok`, `tryLeaArith_ok`, and
`tryReuseFlagCmp_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-! ## Pure helpers -/

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
  | gprZ r =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact ⟨r, hk, by simpa using hc.1, gprSym_match (hA.regs _ hmem).1 hc.2⟩
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
  | gprZ r' =>
    simp only at hk; split at hk
    · next hc =>
      simp only [Option.some.injEq] at hk; subst hk
      simp only [Bool.and_eq_true, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hc
      exact ⟨by simpa using hc.1, gprSym_match (hA.regs _ hmem).1 hc.2⟩
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
  | gpr _ | gprZ _ | flag _ => simp at hk

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
    | gpr _ | gprZ _ | vec _ => simp at hk

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
    have imm : k (.imm c) = some res → ∃ pa, k pa = some res ∧
      (∀ r ∈ pa.gprs, r ∉ T.frame.scratch) ∧
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
      (∀ v ∈ tupArgVecs pas, v ∉ T.vec.vecScratch) ∧ TRel (T.mach.PArgHolds s) pas (vals args₁) :=
          by
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
      · next base idx sh d hdef =>
        obtain ⟨sc, hsc, r1⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨rb, hrb, r2⟩ := Option.bind_eq_some_iff.mp r1
        obtain ⟨ri, hri, hk⟩ := Option.bind_eq_some_iff.mp r2
        obtain ⟨vb, vi, hmb, hmi, hv⟩ := hA.defs _ _ hdef v hm
        obtain ⟨hsb, hgb⟩ := findGprFor_ok hA hrb
        obtain ⟨hsi, hgi⟩ := findGprFor_ok hA hri
        have hb := (hgb _ _ hmb).2
        have hi := (hgi _ _ hmi).2
        simp only [BitVec.setWidth_eq] at hb hi
        have hsh : sc.shift = sh := by
          rcases sh with _ | _ | _ | _ | _ <;> simp [AddrScale.ofShift?] at hsc <;>
            subst hsc <;> rfl
        refine ⟨.baseIdxDisp rb ri sc (Int64.ofBitVec d), hk, fun r hr => ?_, ?_⟩
        · simp only [AddrArg.regs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> assumption
        · simp [Arg.val, AddrArg.eval, hb, hi, hv, hsh, Int64.toBitVec_ofBitVec]
      · next c hdef => exact ⟨.imm c, h, by simp [AddrArg.regs], (hA.defs _ _ hdef v hm).symm⟩
      · simp at h

theorem tryAddrZext_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type}
    {a₁ : Arg Val i64} {a : Arg VNat i64}
    {k : T.Reg → T.Reg → AddrScale → Int64 → Option α} {res : α}
    (hrel : ArgRel G i64 a₁ a) (h : tryAddrZext T.toIsa st a k = some res) :
    ∃ rb ri sc disp, ∃ vb : BitVec 64, ∃ vi : BitVec 32,
      k rb ri sc disp = some res ∧ rb ∉ T.frame.scratch ∧ ri ∉ T.frame.scratch ∧
      GprHolds (T.mach.getGpr s rb) i64 vb ∧
      GprHolds (T.mach.getGpr s ri) (.bits 32) vi ∧
      vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec = a₁.val := by
  cases hrel with
  | imm _ => simp [tryAddrZext] at h
  | var hm =>
    rename_i v x
    simp only [tryAddrZext] at h
    cases hdef : st.defs.find? x with
    | none => simp [hdef] at h
    | some df =>
      cases df with
      | addrSum base idx sh d =>
        rw [hdef] at h; dsimp only at h
        cases hz : zextAddrSumVar? st.defs base idx sh with
        | none => simp [hz] at h
        | some p =>
          rw [hz] at h; rcases p with ⟨rbVar, ridxVar, zv⟩
          obtain ⟨sc, hsc, r1⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨rb, hrb, r2⟩ := Option.bind_eq_some_iff.mp r1
          obtain ⟨ri, hri, hk⟩ := Option.bind_eq_some_iff.mp r2
          obtain ⟨vb0, vi0, hb0, hi0, hv⟩ := hA.defs _ _ hdef v hm
          obtain ⟨vb, vi, hmb, hmi, hsum⟩ := zextAddrSumVar_ok (d := d) hA.defs hb0 hi0 hz
          obtain ⟨hsb, hgb⟩ := findGprFor_ok hA hrb
          obtain ⟨hsi, hgi⟩ := findGprFor_ok hA hri
          have hsh : sc.shift = sh := by
            rcases sh with _ | _ | _ | _ | _ <;> simp [AddrScale.ofShift?] at hsc <;>
              subst hsc <;> rfl
          refine ⟨rb, ri, sc, Int64.ofBitVec d, vb, vi, hk, hsb, hsi, hgb _ _ hmb, hgi _ _ hmi,
            ?_⟩
          simp only [Arg.val]
          rw [hv, hsum, hsh, Int64.toBitVec_ofBitVec]
      | _ => simp [hdef] at h

/-! ## `Agree`/`Inv` plumbing -/

theorem Agree.consReg {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {sa : SymArg} {rl : RegLoc T.Reg T.VReg T.Cond}
    (hA : Agree T G nv st s σ) (h : RegLocOk T.mach G s sa rl) (hlt : symArgScopeOk nv sa = true) :
    Agree T G nv { st with regs := (sa, rl) :: st.regs } s σ :=
  { hA with
    regs := fun p hp => (List.mem_cons.mp hp).elim (fun he => he ▸ h) (hA.regs p)
    regs_lt := fun p hp => (List.mem_cons.mp hp).elim (fun he => he ▸ hlt) (hA.regs_lt p) }

theorem Agree.consRegZ {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {sa : SymArg} {r : T.Reg}
    (hA : Agree T G nv st s σ) (h : RegLocOk T.mach G s sa (.gprZ r))
    (hlt : symArgScopeOk nv sa = true)
    (hz : T.mach.getGpr s r = ((T.mach.getGpr s r).setWidth 32).setWidth 64) :
    Agree T G nv { st with regs := (sa, .gprZ r) :: st.regs, zeroExt32 := r :: st.zeroExt32 } s σ :=
  { hA with
    regs := fun p hp => (List.mem_cons.mp hp).elim (fun he => he ▸ h) (hA.regs p)
    regs_lt := fun p hp => (List.mem_cons.mp hp).elim (fun he => he ▸ hlt) (hA.regs_lt p)
    zeroExt32_ok := fun q hq => (List.mem_cons.mp hq).elim (fun he => he ▸ hz) (hA.zeroExt32_ok q) }

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
  refine hA.extend (Nat.le_succ nv) (fun p hp => ?_) (fun p hp => ?_) (fun _ hp =>
    List.mem_cons_of_mem _ hp) (ctx_uniq_cons hA.ctx_lt hA.ctx_uniq)
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

theorem Inv.store {zl : Bool} {m : Mem 64} {s s' : T.mach.MData} {σ : List (BitVec 64)} {t : Ty}
    {a : BitVec 64} {v : Val t} (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hk : T.mach.KeepsGpr s s' T.frame.scratch) (hok : storeOk m t a)
    (hm : T.mach.mem s' = storeMem (T.mach.mem s) t a v) :
    Inv T hints s₀ ra n Rf (storeMem m t a v) s' σ zl := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hI
  exact ⟨h1, by rw [hk _ T.frameSpec.sp_disj.1]; exact h2,
    fun r hr hns => by
      rw [hk r (fun h => (T.frameSpec.scratch_disj r h).2.1 hr)]; exact h3 r hr hns,
    by rw [hm]; exact storeMem_frame h4 hok v, h5, h6,
    fun h => ⟨(h7 h).1, T.frameSpec.raReg_of_raRegs s s' ra
      (fun r hr => hk r (T.frameSpec.ra_disj r hr).2.1) (h7 h).2⟩⟩

/-! ## Loads and stores -/

theorem lowerLoad_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved) {G : VCtx} {nv ip : Nat}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {t : Ty} {a₁ : Arg Val i64} {a : Arg VNat i64}
    {fz : Bool} (hrel : ArgRel G i64 a₁ a)
    (hl : lowerLoad T.toIsa hints nv ip st t a fz = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    {v : Val t} (hv : loadVal m t a₁.val = some v)
    (kont : ∀ s', Agree T (⟨t, v, nv⟩ :: G) (nv + 1) st' s' σ →
      MemDefsOk (⟨t, v, nv⟩ :: G) m (nv + 1) st'.memDefs → Inv T hints s₀ ra n Rf m s' σ zl →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hspE := hspE
  have hload : ∀ (aa : AddrArg T.Reg), aa.eval (T.mach.getGpr s) = a₁.val →
      loadVal (T.mach.mem s) t (aa.eval (T.mach.getGpr s)) = some v :=
    fun aa hev => by rw [hev]; exact loadVal_frame hI.2.2.2.1 hv
  have hMgrow : MemDefsOk (⟨t, v, nv⟩ :: G) m (nv + 1) st.memDefs :=
    hM.grow (Nat.le_succ _)
      (fun p hp => (List.mem_cons.mp hp).elim (fun h => Or.inr (h ▸ Nat.le_refl _)) Or.inl)
      (fun _ h => List.mem_cons_of_mem _ h)
  unfold lowerLoad at hl
  split at hl
  · split at hl
    · rename_i hgt
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      rcases hl with ⟨rfl, rfl⟩
      have hpush := hA.push t v st.vecWidths (fun _ _ => rfl)
        (fun w h => absurd (hA.vw_lt _ _ h) (Nat.lt_irrefl _))
        (fun x hx => Option.eq_none_iff_forall_ne_some.mpr fun w h =>
          absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx)))
        (fun _ => isGprTy_ne_pair hgt)
      simpa using kont s { hpush with } (hM.insert hA.ctx_lt hrel hv) hI
    · simp at hl
  split at hl
  · next d _ =>
    split at hl
    · simp at hl
    · next hcond =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at hcond
      obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
      cases heq
      have hpushK : ∀ {s'}, T.mach.Frame T.gpr.condReads s s' (d :: T.frame.scratch) [] clob →
          Agree T (⟨t, v, nv⟩ :: G) (nv + 1)
            { st with
              regs := killRegs T.toIsa (d :: T.frame.scratch) [] clob st.regs
              zeroExt32 := killZeroExt (d :: T.frame.scratch) st.zeroExt32
              flags := killFlags T.toIsa clob st.flags } s' σ :=
        fun hfr => by
          have hk := hA.kill hfr
          exact hk.push t v _ (fun _ _ => rfl)
            (fun w h => absurd (hk.vw_lt _ _ h) (Nat.lt_irrefl _))
            (fun x hx => Option.eq_none_iff_forall_ne_some.mpr fun w h =>
              absurd (hk.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx)))
            (fun _ => isGprTy_ne_pair hcond.2)
      have hkeepI : ∀ {s'}, T.mach.Frame T.gpr.condReads s s' (d :: T.frame.scratch) [] clob →
          T.mach.mem s' = T.mach.mem s → Inv T hints s₀ ra n Rf m s' σ zl :=
        fun hfr hm => hI.keep hm (keep_of_frame (gs := [d]) hfr.1 (by simpa using hcond.1))
      have finZero32 : T.toIsa.gpr.zeroUpper32Load = true → (ht32 : t = .bits 32) →
          ∀ {s'}, T.mach.getGpr s' d = (ht32 ▸ v).setWidth 64 → T.mach.mem s' = T.mach.mem s →
          T.mach.Frame T.gpr.condReads s s' (d :: T.frame.scratch) [] clob →
          T.mach.Run host (k + c.length) s' post := by
        intro hzu1 ht32 s' hg hm hfr
        subst ht32
        have hzk : T.mach.getGpr s' d = ((T.mach.getGpr s' d).setWidth 32).setWidth 64 := by
          rw [hg, setWidth_32_64_val]
        have hr1 := (hpushK hfr).consRegZ (sa := .var nv) (r := d)
          ⟨fun t' v' hm' => by
            cases mem_cons_top hA.ctx_lt hm'
            exact ⟨by decide, by rw [hg, BitVec.setWidth_setWidth_of_le _ (by decide),
              BitVec.setWidth_eq]⟩,
            fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨by decide, hg⟩⟩
          (by simp [symArgScopeOk]) hzk
        exact kont s' (by simpa [hzu1, tyEq] using hr1) hMgrow (hkeepI hfr hm)
      have finZext : T.toIsa.gpr.zeroExtLoad = true →
          (T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32)) = false →
          ∀ {s'}, AbiGprHolds (T.mach.getGpr s' d) t v → T.mach.mem s' = T.mach.mem s →
          T.mach.Frame T.gpr.condReads s s' (d :: T.frame.scratch) [] clob →
          T.mach.Run host (k + c.length) s' post := by
        intro hze hzuf s' hg hm hfr
        have hr1 := (hpushK hfr).consReg (sa := .var nv) (rl := .gprZ d)
          ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hg.toGprHolds,
            fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hg⟩
          (by simp [symArgScopeOk])
        exact kont s' (by simpa [hze, hzuf] using hr1) hMgrow (hkeepI hfr hm)
      have finPlain : T.toIsa.gpr.zeroExtLoad = false →
          (T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32)) = false →
          ∀ {s'}, GprHolds (T.mach.getGpr s' d) t v → T.mach.mem s' = T.mach.mem s →
          T.mach.Frame T.gpr.condReads s s' (d :: T.frame.scratch) [] clob →
          T.mach.Run host (k + c.length) s' post := by
        intro hzef hzuf s' hg hm hfr
        have hr1 := (hpushK hfr).consReg (sa := .var nv) (rl := .gpr d)
          (fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hg)
          (by simp [symArgScopeOk])
        exact kont s' (by simpa [hzef, hzuf] using hr1) hMgrow (hkeepI hfr hm)
      rcases orElse_eq_some hta with hta | htz
      · obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
        by_cases hzu : T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32) = true
        · simp only [Bool.and_eq_true] at hzu
          have ht32 : t = .bits 32 := by
            cases t <;> simp [tyEq] at hzu; exact congrArg Ty.bits hzu.2
          subst ht32
          exact T.gprSpec.load_zero32 hzu.1 hk (not_scratch_of_isAllocGpr hsv hcond.1) hreg
            (hload aa hev) hc (fun s' ⟨hg, hm⟩ hfr => finZero32 hzu.1 rfl hg hm hfr)
        · have hzuf : (T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32)) = false := by
            cases hb : T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32) <;> simp_all
          by_cases hze : T.toIsa.gpr.zeroExtLoad = true
          · exact T.gprSpec.load_zext hze hk (not_scratch_of_isAllocGpr hsv hcond.1) hreg
              (hload aa hev) hc (fun s' ⟨hg, hm⟩ hfr => finZext hze hzuf hg hm hfr)
          · have hzef : T.toIsa.gpr.zeroExtLoad = false := by
              cases hb : T.toIsa.gpr.zeroExtLoad <;> simp_all
            exact T.gprSpec.load_spec hk (not_scratch_of_isAllocGpr hsv hcond.1) hreg
              (hload aa hev) hc (fun s' ⟨hg, hm⟩ hfr => finPlain hzef hzuf hg hm hfr)
      · obtain ⟨rb, ri, sc, disp, vb, vi, hk, hrb, hri, hvb, hvi, hev⟩ :=
          tryAddrZext_ok hA hrel htz
        have hlm : loadVal (T.mach.mem s) t
            (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) = some v := by
          rw [hev]; exact loadVal_frame hI.2.2.2.1 hv
        by_cases hzu : T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32) = true
        · simp only [Bool.and_eq_true] at hzu
          have ht32 : t = .bits 32 := by
            cases t <;> simp [tyEq] at hzu; exact congrArg Ty.bits hzu.2
          subst ht32
          exact T.gprSpec.loadZextIdx_zero32 hzu.1 hk (not_scratch_of_isAllocGpr hsv hcond.1)
            hrb hri hvb hvi hlm hc (fun s' ⟨hg, hm⟩ hfr => finZero32 hzu.1 rfl hg hm hfr)
        · have hzuf : (T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32)) = false := by
            cases hb : T.toIsa.gpr.zeroUpper32Load && tyEq t (.bits 32) <;> simp_all
          by_cases hze : T.toIsa.gpr.zeroExtLoad = true
          · exact T.gprSpec.loadZextIdx_zext hze hk (not_scratch_of_isAllocGpr hsv hcond.1)
              hrb hri hvb hvi hlm hc (fun s' ⟨hg, hm⟩ hfr => finZext hze hzuf hg hm hfr)
          · have hzef : T.toIsa.gpr.zeroExtLoad = false := by
              cases hb : T.toIsa.gpr.zeroExtLoad <;> simp_all
            exact T.gprSpec.loadZextIdx_spec hk (not_scratch_of_isAllocGpr hsv hcond.1)
              hrb hri hvb hvi hlm hc (fun s' ⟨hg, hm⟩ hfr => finPlain hzef hzuf hg hm hfr)
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
        fun s' ⟨hg, hm⟩ hfr => kont s' ?_ hMgrow ?_
      · have hk := hA.kill hfr
        refine (hk.push t v _ (fun x hx => Trie.find?_insert_ne _ _ (Nat.ne_of_lt hx))
          (fun w' h => ?_) (fun x hx => ?_) (fun h =>
            by simp [Trie.find?_insert_self] at h)).consReg (sa := .var nv)
          (rl := .vec vd) (fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hg.1, hg⟩)
          (by simp [symArgScopeOk])
        · simp only [Trie.find?_insert_self,
            Option.some.injEq] at h; subst h; exact vecWidth?_spec hw
        · rw [Trie.find?_insert_ne _ _ (Nat.ne_of_gt hx)]
          exact Option.eq_none_iff_forall_ne_some.mpr fun w h =>
            absurd (hk.vw_lt _ _ h) (Nat.not_lt.mpr (Nat.le_of_lt hx))
      · exact hI.keep hm (keep_of_frame (gs := []) hfr.1 (by simp))
  · simp at hl

private theorem rmwFact_ok {G : VCtx} {y w : Nat} {df : DefFact} {vy : BitVec w} {op : RmwOp}
    {x : Nat} {rhs : Arg VNat (.bits w)} (hOk : DefOk G y df)
    (hmy : ⟨.bits w, vy, y⟩ ∈ G) (hf : rmwFact w df = some (op, x, rhs)) :
    ∃ (vx : BitVec w) (rhs₁ : Arg Val (.bits w)),
      ⟨.bits w, vx, x⟩ ∈ G ∧ ArgRel G (.bits w) rhs₁ rhs ∧ vy = op.eval vx rhs₁.val := by
  cases df with
  | addImm64 b d =>
    simp only [rmwFact] at hf; split at hf
    · rename_i h64; replace h64 : w = 64 := by simpa using h64
      subst h64; simp only [Option.some.injEq, Prod.mk.injEq] at hf
      rcases hf with ⟨rfl, rfl, rfl⟩
      obtain ⟨vb, hmb, rfl⟩ := hOk vy hmy
      exact ⟨vb, .imm (d.setWidth 64), hmb, .imm _, by simp [RmwOp.eval, BitVec.setWidth_eq]⟩
    · simp at hf
  | addrSum b i sh d =>
    simp only [rmwFact] at hf; split at hf
    · rename_i hc; simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at hc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      rcases hf with ⟨rfl, rfl, rfl⟩
      obtain ⟨vb, vi, hmb, hmi, rfl⟩ := hOk vy hmy
      exact ⟨vb, .var vi, hmb, .var hmi, by simp [RmwOp.eval]⟩
    · simp at hf
  | binVarVar w' op' a b =>
    simp only [rmwFact] at hf; split at hf
    · rename_i hw; replace hw : w' = w := Nat.beq_eq.mp hw; subst hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      rcases hf with ⟨rfl, rfl, rfl⟩
      obtain ⟨va, vb, hma, hmb, rfl⟩ := hOk.2 vy hmy
      exact ⟨va, .var vb, hma, .var hmb, rfl⟩
    · simp at hf
  | binVarImm w' op' a c =>
    simp only [rmwFact] at hf; split at hf
    · rename_i hw; replace hw : w' = w := Nat.beq_eq.mp hw; subst hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      rcases hf with ⟨rfl, rfl, rfl⟩
      obtain ⟨va, hma, rfl⟩ := hOk.2 vy hmy
      exact ⟨va, .imm (c.setWidth w'), hma, .imm _, rfl⟩
    · simp at hf
  | andVarVar w' a b =>
    simp only [rmwFact] at hf; split at hf
    · rename_i hw; replace hw : w' = w := Nat.beq_eq.mp hw; subst hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      rcases hf with ⟨rfl, rfl, rfl⟩
      obtain ⟨va, vb, hma, hmb, rfl⟩ := hOk.2 vy hmy
      exact ⟨va, .var vb, hma, .var hmb, rfl⟩
    · simp at hf
  | andVarImm w' a c =>
    simp only [rmwFact] at hf; split at hf
    · rename_i hw; replace hw : w' = w := Nat.beq_eq.mp hw; subst hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      rcases hf with ⟨rfl, rfl, rfl⟩
      obtain ⟨va, hma, rfl⟩ := hOk.2 vy hmy
      exact ⟨va, .imm (c.setWidth w'), hma, .imm _, rfl⟩
    · simp at hf
  | _ => simp [rmwFact] at hf

private theorem tryRmwHalf_ok {zl : Bool} {G : VCtx} {nv n' : Nat} {vh : VariantHint}
    {op : RmwOp} {x : Nat} {vx : BitVec n'} {other₁ : Arg Val (.bits n')}
    {other : Arg VNat (.bits n')} {a₁ : Arg Val i64} {a : Arg VNat i64} {resVal : BitVec n'}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {k : Nat} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs)
    (hmx : ⟨.bits n', vx, x⟩ ∈ G) (hrhs : ArgRel G (.bits n') other₁ other)
    (ha : ArgRel G i64 a₁ a) (hok : storeOk m (.bits n') a₁.val)
    (hres : resVal = op.eval vx other₁.val)
    (h : tryRmwHalf T.toIsa st vh n' op x other a = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c T.frame.scratch [] clob s
      (fun s' => T.mach.mem s' = storeMem (T.mach.mem s) (.bits n') a₁.val resVal) post := by
  unfold tryRmwHalf at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, loadAddr⟩
    cases tm with
    | bits m' =>
      simp only [hmd] at h
      split at h
      · rename_i hmeq
        have hm' : m' = n' := Nat.beq_eq.mp hmeq; subst hm'
        obtain ⟨-, hlv0⟩ := hM x (.bits m') loadAddr hmd
        obtain ⟨a_l, ha_l, hlv⟩ := hlv0 vx hmx
        obtain ⟨aa1, hk1, hreg1, hev1⟩ := tryAddr_ok hA ha_l h
        obtain ⟨aa2, hk2, _, hev2⟩ := tryAddr_ok hA ha hk1
        split at hk2
        · rename_i haa
          have haa' : aa1 = aa2 := beq_iff_eq.mp haa; subst haa'
          obtain ⟨pb, hk3, hpb, -, hphp⟩ := tryArg_ok hA hrhs hk2
          have hlm : loadVal (T.mach.mem s) (.bits m') (aa1.eval (T.mach.getGpr s)) =
              some vx := by rw [hev1]; exact loadVal_frame hI.2.2.2.1 hlv
          have hsok : storeOk (T.mach.mem s) (.bits m') (aa1.eval (T.mach.getGpr s)) := by
            rw [hev2]; exact storeOk_frame hI.2.2.2.1 hok
          refine fun hinf kont =>
            T.gprSpec.rmwMem_spec hk3
              (fun r hr => (List.mem_append.mp hr).elim (hreg1 r) (hpb r))
              hlm hsok hphp (P := fun rvs => rvs = (resVal, ()))
              (by rw [RmwOp.wp_eval, ← hres]) hinf fun s' ⟨rv, hrv, hms⟩ hfr => ?_
          cases hrv
          refine kont s' ?_ hfr
          rwa [← hev2]
        · simp at hk2
      · simp at h
    | _ => simp [hmd] at h

private theorem tryRmwStore_ok {zl : Bool} {G : VCtx} {nv : Nat} {vh : VariantHint}
    {t : Ty} {v₁ : Arg Val t} {v : Arg VNat t} {a₁ : Arg Val i64} {a : Arg VNat i64}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {k : Nat} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs)
    (hv : ArgRel G t v₁ v) (ha : ArgRel G i64 a₁ a)
    (hok : storeOk m t a₁.val) (h : tryRmwStore T.toIsa st vh t v a = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c T.frame.scratch [] clob s
      (fun s' => T.mach.mem s' = storeMem (T.mach.mem s) t a₁.val v₁.val) post := by
  cases t <;> cases v <;> try (simp [tryRmwStore] at h; done)
  rename_i n' y
  cases hv with | var hmy =>
  simp only [tryRmwStore] at h
  split at h; · simp at h
  cases hdef : st.defs.find? y with
  | none => simp [hdef] at h
  | some df =>
    simp only [hdef] at h
    obtain ⟨⟨op, x, rhs⟩, hrf, hk⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨vx, rhs₁, hmx, hrhs, hvy⟩ := rmwFact_ok (hA.defs y df hdef) hmy hrf
    rcases orElse_eq_some hk with hk1 | hk2
    · exact tryRmwHalf_ok hA hI hM hmx hrhs ha hok hvy hk1
    · split at hk2
      · rename_i hcomm
        cases rhs with
        | imm _ => simp at hk2
        | var z =>
          cases hrhs with | var hmz =>
          rename_i vz
          exact tryRmwHalf_ok hA hI hM hmz (.var hmx) ha hok
            (by simp only [Arg.val] at hvy ⊢; rw [hvy, RmwOp.eval_comm hcomm]) hk2
      · simp at hk2

theorem lowerStore_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    {G : VCtx} {nv : Nat} {vh : VariantHint}
    {st st' : SymState T.toIsa} {c : List T.Directive} {k : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {t : Ty} {v₁ : Arg Val t} {v : Arg VNat t}
    {a₁ : Arg Val i64} {a : Arg VNat i64} (hv : ArgRel G t v₁ v) (ha : ArgRel G i64 a₁ a)
    (hl : lowerStore T.toIsa st vh t v a = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ zl) (hok : storeOk m t a₁.val)
    (kont : ∀ s', Agree T G nv st' s' σ →
      MemDefsOk G (storeMem m t a₁.val v₁.val) nv st'.memDefs →
      Inv T hints s₀ ra n Rf (storeMem m t a₁.val v₁.val) s' σ zl →
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
        fun s' hm hfr => kont s' { hA.kill hfr with } (MemDefsOk.empty _ _ _) ?_
      rw [hev] at hm
      exact hI.store hfr.1 hok hm
    | gpr _ | imm _ => simp at hk
  | bool | bits _ | float _ =>
    simp only [lowerStore] at hl
    split at hl
    · simp at hl
    · obtain ⟨⟨c', clob⟩, hta, heq⟩ := Option.map_eq_some_iff.mp hl
      cases heq
      rcases orElse_eq_some hta with hta | hrmw
      · obtain ⟨pa, hk, hpg, -, hp⟩ := tryArg_ok hA hv hta
        rcases orElse_eq_some hk with hk' | hkz
        · obtain ⟨aa, hk1, hreg, hev⟩ := tryAddr_ok hA ha hk'
          refine T.gprSpec.store_spec hk1 (fun r hr => ?_) hp (hsok aa hev) hc
            fun s' hm hfr => kont s' { hA.kill hfr with } (MemDefsOk.empty _ _ _) ?_
          · exact (List.mem_append.mp hr).elim (hpg r) (hreg r)
          · rw [hev] at hm
            exact hI.store hfr.1 hok hm
        · obtain ⟨rb, ri, sc, disp, vb, vi, hk1, hrb, hri, hvb, hvi, hev⟩ :=
            tryAddrZext_ok hA ha hkz
          refine T.gprSpec.storeZextIdx_spec hk1 hpg hrb hri hp hvb hvi
            (by rw [hev]; exact storeOk_frame hI.2.2.2.1 hok) hc
            fun s' hm hfr => kont s' { hA.kill hfr with } (MemDefsOk.empty _ _ _) ?_
          rw [hev] at hm
          exact hI.store hfr.1 hok hm
      · refine tryRmwStore_ok hA hI hM hv ha hok hrmw hc fun s' hm hfr =>
          kont s' { hA.kill hfr with } (MemDefsOk.empty _ _ _) (hI.store hfr.1 hok hm)

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
      obtain ⟨ih1, ih2, ih3, ih4⟩ :=
          bindDsts_ok ds rvs (nv + 1) ((.var nv, rl) :: regs) vw' hds hdo' hG'
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

theorem cmpOp_evalBits_signExtend {m n : Nat} (_hm : 0 < m) (hmn : m < n)
    {co : CmpOp} (hco : cmpIsSignedOrEq co = true) (a : BitVec m) (c : BitVec n)
    (hc : (c.truncate m).signExtend n = c) :
    co.evalBits (a.signExtend n) c = co.evalBits a (c.truncate m) := by
  have hle : m ≤ n := Nat.le_of_lt hmn
  have ha : (a.signExtend n).toInt = a.toInt := BitVec.toInt_signExtend_of_le hle
  have hci : c.toInt = (c.truncate m).toInt :=
    calc c.toInt = ((c.truncate m).signExtend n).toInt := congrArg BitVec.toInt hc.symm
      _ = (c.truncate m).toInt := BitVec.toInt_signExtend_of_le hle
  have heq : (a.signExtend n = c) ↔ (a = c.truncate m) :=
    ⟨fun h => BitVec.eq_of_toInt_eq (by rw [← ha, h, hci]), fun h => by rw [h, hc]⟩
  cases co <;> simp only [cmpIsSignedOrEq] at hco <;> try (cases hco; done)
  all_goals simp only [CmpOp.evalBits, BitVec.slt, BitVec.sle, Ne, ha, hci, heq]

theorem cmpOp_evalBits_zeroExtend {m n : Nat} (hmn : m < n)
    {co : CmpOp} (hco : cmpIsUnsignedOrEq co = true) (a : BitVec m) (c : BitVec n)
    (hc : (c.truncate m).zeroExtend n = c) :
    co.evalBits (a.zeroExtend n) c = co.evalBits a (c.truncate m) := by
  have hle : m ≤ n := Nat.le_of_lt hmn
  have ha : (a.zeroExtend n).toNat = a.toNat := by
    change (a.setWidth n).toNat = a.toNat
    rw [BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) hle))]
  have hcn : c.toNat = (c.truncate m).toNat := by
    calc c.toNat = ((c.truncate m).setWidth n).toNat := congrArg BitVec.toNat hc.symm
      _ = (c.truncate m).toNat := by
        rw [BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (c.truncate m).isLt
            (Nat.pow_le_pow_right (by decide) hle))]
  have heq : (a.zeroExtend n = c) ↔ (a = c.truncate m) :=
    ⟨fun h => BitVec.eq_of_toNat_eq (by rw [← ha, h, hcn]), fun h => by rw [h, hc]⟩
  cases co <;> simp only [cmpIsUnsignedOrEq] at hco <;> try (cases hco; done)
  all_goals simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, Ne, ha, hcn, heq]

theorem symArgScopeOk_of_argRel {G : VCtx} {nv w : Nat} {a₁ : Arg Val (.bits w)}
    {a : Arg VNat (.bits w)} {sa : SymArg}
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hrel : ArgRel G (.bits w) a₁ a)
    (hsa : toSymArg T.toIsa (.bits w) a = some sa) :
    symArgScopeOk nv sa = true := by
  cases hrel with
  | var hm =>
    simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
    simp [symArgScopeOk, Nat.ble_eq]; exact hlt _ hm
  | imm c =>
    simp only [toSymArg] at hsa; split at hsa
    · simp only [Option.some.injEq] at hsa; subst hsa; rfl
    · simp at hsa

private theorem tryAddr_unique {G : VCtx} {nv : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {vh : VariantHint} {α : Type}
    {addr : Arg VNat i64} {k : AddrArg T.Reg → Option α} {res : α}
    (hA : Agree T G nv st s σ) (hk : tryAddr T.toIsa st vh addr k = some res)
    {a₁ a₂ : Arg Val i64} (h1 : ArgRel G i64 a₁ addr) (h2 : ArgRel G i64 a₂ addr) :
    a₁.val = a₂.val := by
  cases addr with
  | imm c => cases h1; cases h2; rfl
  | var x =>
    cases h1 with | var hm1 => cases h2 with | var hm2 =>
    simp only [tryAddr] at hk
    rcases orElse_eq_some hk with h | h
    · cases vh with
      | disp off =>
        cases hdef : st.defs.find? x with
        | none => simp [hdef] at h
        | some df =>
          cases df with
          | addImm64 base d =>
            simp only [hdef] at h
            split at h
            · obtain ⟨rb, hrb, _⟩ := Option.bind_eq_some_iff.mp h
              obtain ⟨-, hgb⟩ := findGprFor_ok hA hrb
              obtain ⟨vb1, hmb1, hv1⟩ := hA.defs _ _ hdef _ hm1
              obtain ⟨vb2, hmb2, hv2⟩ := hA.defs _ _ hdef _ hm2
              have hb1 := (hgb _ _ hmb1).2; have hb2 := (hgb _ _ hmb2).2
              simp only [BitVec.setWidth_eq] at hb1 hb2
              simp [Arg.val, hv1, hv2, ← hb1, ← hb2]
            · simp at h
          | _ => simp [hdef] at h
      | _ => simp at h
    rcases orElse_eq_some h with h | h
    · obtain ⟨rx, hrx, _⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨-, hgx⟩ := findGprFor_ok hA hrx
      have hx1 := (hgx _ _ hm1).2; have hx2 := (hgx _ _ hm2).2
      simp only [BitVec.setWidth_eq] at hx1 hx2
      simp [Arg.val, ← hx1, ← hx2]
    · cases hdef : st.defs.find? x with
      | none => simp [hdef] at h
      | some df =>
        cases df with
        | addImm64 base d =>
          simp only [hdef] at h
          obtain ⟨rb, hrb, _⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨-, hgb⟩ := findGprFor_ok hA hrb
          obtain ⟨vb1, hmb1, hv1⟩ := hA.defs _ _ hdef _ hm1
          obtain ⟨vb2, hmb2, hv2⟩ := hA.defs _ _ hdef _ hm2
          have hb1 := (hgb _ _ hmb1).2; have hb2 := (hgb _ _ hmb2).2
          simp only [BitVec.setWidth_eq] at hb1 hb2
          simp [Arg.val, hv1, hv2, ← hb1, ← hb2]
        | addrSum base idx sh d =>
          simp only [hdef] at h
          obtain ⟨sc, _, r1⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨rb, hrb, r2⟩ := Option.bind_eq_some_iff.mp r1
          obtain ⟨ri, hri, _⟩ := Option.bind_eq_some_iff.mp r2
          obtain ⟨-, hgb⟩ := findGprFor_ok hA hrb
          obtain ⟨-, hgi⟩ := findGprFor_ok hA hri
          obtain ⟨vb1, vi1, hmb1, hmi1, hv1⟩ := hA.defs _ _ hdef _ hm1
          obtain ⟨vb2, vi2, hmb2, hmi2, hv2⟩ := hA.defs _ _ hdef _ hm2
          have hb1 := (hgb _ _ hmb1).2; have hb2 := (hgb _ _ hmb2).2
          have hi1 := (hgi _ _ hmi1).2; have hi2 := (hgi _ _ hmi2).2
          simp only [BitVec.setWidth_eq] at hb1 hb2 hi1 hi2
          simp [Arg.val, hv1, hv2, ← hb1, ← hb2, ← hi1, ← hi2]
        | imm64 c =>
          simp only [hdef] at h
          have hv1 := hA.defs _ _ hdef _ hm1
          have hv2 := hA.defs _ _ hdef _ hm2
          simp [Arg.val, hv1, hv2]
        | _ => simp [hdef] at h

theorem memDefs_tryAddr_symBits {G : VCtx} {nv w x : Nat}
    {vh : VariantHint} {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)}
    {m : Mem 64} {α : Type} {k : AddrArg T.Reg → Option α} {res : α}
    {addr : Arg VNat i64} {vx : BitVec w}
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hmd : st.memDefs.find? x = some (.bits w, addr))
    (hmx : ⟨.bits w, vx, x⟩ ∈ G)
    (hk : tryAddr T.toIsa st vh addr k = some res) :
    SymBits G w vx (.var x) := by
  intro v hv
  obtain ⟨-, hlv0⟩ := hM x (.bits w) addr hmd
  obtain ⟨a₁, ha₁, hl₁⟩ := hlv0 vx hmx
  obtain ⟨a₂, ha₂, hl₂⟩ := hlv0 v hv
  rw [tryAddr_unique hA hk ha₂ ha₁, hl₁] at hl₂
  exact (Option.some.inj hl₂).symm

theorem tryArg_bits_det {G : VCtx} {nv : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} (hA : Agree T G nv st s σ)
    {pref : List T.Cond} {α : Type} {w : Nat} (hw : w ≤ 64)
    {a₁ : Arg Val (.bits w)} {a : Arg VNat (.bits w)}
    {k : PArg T.Reg T.VReg T.Cond (.bits w) → Option α} {res : α} {sa : SymArg}
    (hrel : ArgRel G (.bits w) a₁ a)
    (hta : tryArg T.toIsa st pref (.bits w) a k = some res)
    (hsa : toSymArg T.toIsa (.bits w) a = some sa) :
    SymBits G w a₁.val sa := by
  cases hrel with
  | var hm =>
    simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
    simp only [tryArg] at hta
    obtain ⟨r, -, -, hg⟩ := tryGpr_ok hA hta
    intro v hv
    rw [← (hg (.bits w) v hv).2, (hg (.bits w) _ hm).2]; rfl
  | imm c =>
    simp only [toSymArg] at hsa; split at hsa
    · simp only [Option.some.injEq] at hsa; subst hsa
      exact ⟨rfl, (BitVec.setWidth_setWidth_of_le c hw).trans (BitVec.setWidth_eq c)⟩
    · simp at hsa

private theorem symBits_arg_eq {G : VCtx} {w : Nat} (hw : w ≤ 64)
    {a₁ : Arg Val (.bits w)} {a : Arg VNat (.bits w)} {sa : SymArg} {v : BitVec w}
    (hrel : ArgRel G (.bits w) a₁ a) (hsa : toSymArg T.toIsa (.bits w) a = some sa)
    (hsb : SymBits G w v sa) : a₁.val = v := by
  cases hrel with
  | var hm =>
    simp only [toSymArg, Option.some.injEq] at hsa; subst hsa
    exact hsb _ hm
  | imm c =>
    simp only [toSymArg] at hsa; split at hsa
    · simp only [Option.some.injEq] at hsa; subst hsa
      rw [← hsb.2, BitVec.setWidth_setWidth_of_le c hw, BitVec.setWidth_eq]; rfl
    · simp at hsa

private theorem testOp_with_extra {k w : Nat} {neg : Bool}
    {pa pb : PArg T.Reg T.VReg T.Cond (.bits w)} {pd : PDst T.Reg T.VReg T.Cond .bool}
    {c : List T.Directive} {clob : FlagMask} {va vb : BitVec w} {s : T.mach.MData}
    (hto : T.gpr.testOp w neg pa pb pd = some (c, clob))
    (hreg : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ T.frame.scratch)
    (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (hpa : T.mach.PArgHolds s (.bits w) pa va)
    (hpb : T.mach.PArgHolds s (.bits w) pb vb) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w
        T.mach.PDstHolds s' .bool pd res ∧
        (∀ cc, testBoolExtra? T.toIsa neg clob pd = some cc → T.mach.evalCond s' cc = res) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  by_cases hex : (testBoolExtra? T.toIsa neg clob pd).isSome
  · obtain ⟨cc, hcc⟩ := Option.isSome_iff_exists.mp hex
    have hhex := hcc
    unfold testBoolExtra? at hcc
    split at hcc
    · rename_i hgd
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hgd
      have htf : T.gpr.hasTestFlags = true := hgd.1
      have hcl : clob ≠ FlagMask.none := fun h => by subst h; simp at hgd
      have hco : T.gpr.condOfCmp? (if neg then .ne else .eq) = some cc := by
        cases pd <;> simp at hcc ⊢; exact hcc
      refine (T.gprSpec.testOp_boolFlag_spec htf hcl hco hto hreg hdg hpa hpb).conseq
        fun s' ⟨h1, h2, h3⟩ _ =>
          ⟨h1, fun cc' hcc' => by rw [hhex, Option.some.injEq] at hcc'; subst hcc'; exact h2, h3⟩
    · simp at hcc
  · have hnone : testBoolExtra? T.toIsa neg clob pd = none := by
      cases h : testBoolExtra? T.toIsa neg clob pd <;> simp_all
    refine (T.gprSpec.testOp_spec hto hreg hdg hpa hpb).conseq fun s' ⟨h1, h2⟩ _ =>
      ⟨h1, (fun cc hcc => by rw [hnone] at hcc; cases hcc), h2⟩

theorem testMem_with_extra {k w : Nat} {neg : Bool} {a : AddrArg T.Reg}
    {pb : PArg T.Reg T.VReg T.Cond (.bits w)} {pd : PDst T.Reg T.VReg T.Cond .bool}
    {c : List T.Directive} {clob : FlagMask} {va vb : BitVec w} {s : T.mach.MData}
    (htm : T.gpr.testMem w neg a pb pd = some (c, clob))
    (hreg : ∀ r ∈ a.regs ++ pb.gprs, r ∉ T.frame.scratch)
    (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (hlm : loadVal (T.mach.mem s) (.bits w) (a.eval (T.mach.getGpr s)) = some va)
    (hpb : T.mach.PArgHolds s (.bits w) pb vb) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w
        T.mach.PDstHolds s' .bool pd res ∧
        (∀ cc, testBoolExtra? T.toIsa neg clob pd = some cc → T.mach.evalCond s' cc = res) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  by_cases hex : (testBoolExtra? T.toIsa neg clob pd).isSome
  · obtain ⟨cc, hcc⟩ := Option.isSome_iff_exists.mp hex
    have hhex := hcc
    unfold testBoolExtra? at hcc
    split at hcc
    · rename_i hgd
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hgd
      have htf : T.gpr.hasTestFlags = true := hgd.1
      have hcl : clob ≠ FlagMask.none := fun h => by subst h; simp at hgd
      have hco : T.gpr.condOfCmp? (if neg then .ne else .eq) = some cc := by
        cases pd <;> simp at hcc ⊢; exact hcc
      refine (T.gprSpec.testMem_boolFlag_spec htf hcl hco htm hreg hdg hlm hpb).conseq
        fun s' ⟨h1, h2, h3⟩ _ =>
          ⟨h1, fun cc' hcc' => by rw [hhex, Option.some.injEq] at hcc'; subst hcc'; exact h2, h3⟩
    · simp at hcc
  · have hnone : testBoolExtra? T.toIsa neg clob pd = none := by
      cases h : testBoolExtra? T.toIsa neg clob pd <;> simp_all
    refine (T.gprSpec.testMem_spec htm hreg hdg hlm hpb).conseq fun s' ⟨h1, h2⟩ _ =>
      ⟨h1, (fun cc hcc => by rw [hnone] at hcc; cases hcc), h2⟩

theorem cmpMem_with_ext {k w : Nat} {co : CmpOp} {a : AddrArg T.Reg}
    {pb : PArg T.Reg T.VReg T.Cond (.bits w)} {pd : PDst T.Reg T.VReg T.Cond .bool}
    {c : List T.Directive} {clob : FlagMask} {va vb : BitVec w} {s : T.mach.MData}
    (hcm : T.gpr.cmpMem co w a pb pd = some (c, clob))
    (hreg : ∀ r ∈ a.regs ++ pb.gprs, r ∉ T.frame.scratch)
    (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (hlm : loadVal (T.mach.mem s) (.bits w) (a.eval (T.mach.getGpr s)) = some va)
    (hpb : T.mach.PArgHolds s (.bits w) pb vb) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        let ex := (extCmpMemRes T.toIsa co pd c clob).2.2
        T.mach.PDstHolds s' .bool pd (co.evalBits va vb) ∧
        (∀ cc, ex = some cc → T.mach.evalCond s' cc = co.evalBits va vb) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  cases hcmo : T.gpr.cmpMemFlagsOut? co pd with
  | none =>
    refine (T.gprSpec.cmpMem_spec hcm hreg hdg hlm hpb).conseq fun s' ⟨hd, hm⟩ _ =>
      ⟨hd, fun cc hcc => by cases pd <;> simp [extCmpMemRes, hcmo] at hcc, hm⟩
  | some lf =>
    refine (T.gprSpec.cmpMem_flags_spec hcmo hcm hreg hdg hlm hpb).conseq
      fun s' ⟨hd, hfl, hm⟩ _ => ⟨hd, fun cc hcc => ?_, hm⟩
    cases pd <;> simp [extCmpMemRes, hcmo] at hcc
    have hf := hfl (if lf then co else co.swap) cc (by simp) hcc
    rw [hf]; cases lf <;> simp [CmpOp.swap_evalBits]

theorem cmpMemRes_with_flags {G : VCtx} {nv k w : Nat} (hw : w ≤ 64)
    {st : SymState T.toIsa} {co : CmpOp} {lhs rhs : SymArg}
    {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive} {clob : FlagMask}
    {flPost : Option FlagFact} {ex : Option T.Cond} {a : AddrArg T.Reg}
    {pb : PArg T.Reg T.VReg T.Cond (.bits w)} {va vb : BitVec w} {s : T.mach.MData}
    (hA_fl : FlagFactOk T G s st.flags) (hA_flt : FlagFactScope nv st.flags)
    (hlhs : SymBits G w va lhs) (hrhs : SymBits G w vb rhs)
    (hlhsAt : SymValAt G w va lhs) (hrhsAt : SymValAt G w vb rhs)
    (hsl : symArgScopeOk nv lhs = true) (hsr : symArgScopeOk nv rhs = true)
    (hres : cmpMemRes T.toIsa st co w lhs rhs pd c clob = (c, clob, flPost, ex))
    (hcm : T.gpr.cmpMem co w a pb pd = some (c, clob))
    (hreg : ∀ r ∈ a.regs ++ pb.gprs, r ∉ T.frame.scratch)
    (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (hlm : loadVal (T.mach.mem s) (.bits w) (a.eval (T.mach.getGpr s)) = some va)
    (hpb : T.mach.PArgHolds s (.bits w) pb vb) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        T.mach.PDstHolds s' .bool pd (co.evalBits va vb) ∧
        FlagFactOk T G s' flPost ∧ FlagFactScope nv flPost ∧
        (∀ cc, ex = some cc → T.mach.evalCond s' cc = co.evalBits va vb) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  unfold cmpMemRes at hres
  cases hcmo : T.gpr.cmpMemFlagsOut? co pd with
  | none =>
    rw [hcmo] at hres; simp only [Prod.mk.injEq] at hres
    rcases hres with ⟨-, -, rfl, rfl⟩
    refine (T.gprSpec.cmpMem_spec hcm hreg hdg hlm hpb).conseq fun s' ⟨hd, hm⟩ hfr =>
      ⟨hd, hA_fl.kill hfr, hA_flt.kill, (fun _ h => nomatch h), hm⟩
  | some lf =>
    rw [hcmo] at hres; simp only [Prod.mk.injEq] at hres
    rcases hres with ⟨-, -, rfl, rfl⟩
    refine (T.gprSpec.cmpMem_flags_spec hcmo hcm hreg hdg hlm hpb).conseq
      fun s' ⟨hd, hfl, hm⟩ _ => ?_
    refine ⟨hd, ⟨hw, if lf then va else vb, if lf then vb else va, ?_, ?_, ?_, ?_, hfl⟩,
      ⟨?_, ?_⟩, fun cc hcc => ?_, hm⟩
    · cases lf <;> simp [hlhsAt, hrhsAt]
    · cases lf <;> simp [hlhs, hrhs]
    · cases lf <;> simp [hlhsAt, hrhsAt]
    · cases lf <;> simp [hlhs, hrhs]
    · cases lf <;> simp [hsl, hsr]
    · cases lf <;> simp [hsl, hsr]
    · cases pd <;> simp at hcc
      have hf := hfl (if lf then co else co.swap) cc (by simp) hcc
      rw [hf]; cases lf <;> simp [CmpOp.swap_evalBits]

private theorem tryTestMemVar_ok {zl : Bool} {G : VCtx} {nv w x k : Nat} {neg : Bool}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vx : BitVec w} {other₁ : Arg Val (.bits w)} {other : Arg VNat (.bits w)}
    {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hmx : ⟨.bits w, vx, x⟩ ∈ G)
    (hrel : ArgRel G (.bits w) other₁ other) (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryTestMemVar T.toIsa st neg w x other pd = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (vx &&& other₁.val) 0#w
        T.mach.PDstHolds s' .bool pd res ∧
        (∀ cc, testBoolExtra? T.toIsa neg clob pd = some cc → T.mach.evalCond s' cc = res) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  unfold tryTestMemVar at h
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at h
  | some p =>
    rcases p with ⟨tm, addr⟩
    cases tm with
    | bits w' =>
      simp only [hmd] at h
      split at h
      · rename_i heq
        have hw : w' = w := Nat.beq_eq.mp heq
        subst hw
        obtain ⟨-, hlv0⟩ := hM x (.bits w') addr hmd
        obtain ⟨a₁, ha₁, hlv⟩ := hlv0 vx hmx
        obtain ⟨aa, hk1, hreg, hev⟩ := tryAddr_ok hA ha₁ h
        obtain ⟨pb, hk2, hpb, -, hphp⟩ := tryArg_ok hA hrel hk1
        have hlm : loadVal (T.mach.mem s) (.bits w') (aa.eval (T.mach.getGpr s)) = some vx := by
          rw [hev]; exact loadVal_frame hI.2.2.2.1 hlv
        exact testMem_with_extra hk2
          (fun r hr => (List.mem_append.mp hr).elim (hreg r) (hpb r)) hdg hlm hphp
      · simp at h
    | _ => simp [hmd] at h

private theorem tryTestFuse_ok {zl : Bool} {G : VCtx} {nv w t k : Nat} {neg : Bool}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vt : BitVec w} {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hmt : ⟨.bits w, vt, t⟩ ∈ G)
    (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryTestFuse T.toIsa st neg w t pd = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits vt 0#w
        T.mach.PDstHolds s' .bool pd res ∧
        (∀ cc, testBoolExtra? T.toIsa neg clob pd = some cc → T.mach.evalCond s' cc = res) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  unfold tryTestFuse at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | andVarImm w' x ci =>
      simp only [hdef] at h
      split at h
      · simp at h
      · rename_i hne
        have hw : w' = w := Nat.beq_eq.mp (by simpa using hne)
        subst hw
        obtain ⟨-, hfun⟩ := hA.defs t _ hdef
        obtain ⟨vx, hmx, rfl⟩ := hfun vt hmt
        rcases orElse_eq_some h with h1 | h2
        · exact tryTestMemVar_ok hA hI hM hmx (.imm (ci.setWidth w')) hdg h1
        · obtain ⟨pa, hk, hpa, -, hphp⟩ := tryArg_ok hA (.var hmx) h2
          exact testOp_with_extra hk (by simpa [PArg.gprs] using hpa) hdg hphp rfl
    | andVarVar w' x y =>
      simp only [hdef] at h
      split at h
      · simp at h
      · rename_i hne
        have hw : w' = w := Nat.beq_eq.mp (by simpa using hne)
        subst hw
        obtain ⟨-, hfun⟩ := hA.defs t _ hdef
        obtain ⟨vx, vy, hmx, hmy, rfl⟩ := hfun vt hmt
        rcases orElse_eq_some h with h1 | h
        · exact tryTestMemVar_ok hA hI hM hmx (.var hmy) hdg h1
        rcases orElse_eq_some h with h2 | h3
        · simpa [BitVec.and_comm] using tryTestMemVar_ok hA hI hM hmy (.var hmx) hdg h2
        · obtain ⟨pa, hk1, hpa, -, hpaH⟩ := tryArg_ok hA (.var hmx) h3
          obtain ⟨pb, hk2, hpb, -, hpbH⟩ := tryArg_ok hA (.var hmy) hk1
          exact testOp_with_extra hk2
            (fun r hr => (List.mem_append.mp hr).elim (hpa r) (hpb r)) hdg hpaH hpbH
    | _ => simp [hdef] at h

private theorem symBits_imm64 {G : VCtx} {w : Nat} (hw : w ≤ 64) (v : BitVec w) :
    SymBits G w v (.immBits w (v.setWidth 64)) :=
  ⟨rfl, BitVec.eq_of_getLsbD_eq fun j hj => by
    simp [hj, show j < 64 by omega]⟩

private theorem tryExtCmp_ok {zl : Bool} {G : VCtx} {nv w t k : Nat} {vh : VariantHint}
    {co : CmpOp} (hw : w ≤ 64) {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64} {vt ci : BitVec w}
    {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive}
    {clob : FlagMask} {flPost : Option FlagFact} {ex : Option T.Cond}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hmt : ⟨.bits w, vt, t⟩ ∈ G)
    (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : tryExtCmp T.toIsa st vh co w t ci pd = some (c, clob, flPost, ex)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        T.mach.PDstHolds s' .bool pd (co.evalBits vt ci) ∧
        FlagFactOk T G s' flPost ∧ FlagFactScope nv flPost ∧
        (∀ cc, ex = some cc → T.mach.evalCond s' cc = co.evalBits vt ci) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  have run_ok : ∀ {mw x} (hmw : mw < w) (va : BitVec mw)
      (hev : co.evalBits vt ci = co.evalBits va (ci.truncate mw))
      (hmx : ⟨.bits mw, va, x⟩ ∈ G),
      ((match st.memDefs.find? x with
       | some (.bits m', addr) =>
         if Nat.beq m' mw then
           tryAddr T.toIsa st .default addr fun aa =>
             (T.gpr.cmpMem co mw aa (.imm (ci.truncate mw)) pd).map fun p =>
               cmpMemRes T.toIsa st co mw (.var x) (.immBits mw ((ci.truncate mw).setWidth 64))
                 pd p.1 p.2
         else none
       | _ => none) <|>
      (if T.toIsa.supportsTestFuse then
        tryGpr T.toIsa st.regs (.var x) fun rx =>
          (T.gpr.op (.cmp co (.bits mw)) (.gpr rx, .imm (ci.truncate mw), ()) (pd, ()) vh).map
            fun p =>
              let lf? := T.gpr.cmpFlagsOut? co mw (.gpr rx) (.imm (ci.truncate mw)) pd
              let immS : SymArg := .immBits mw ((ci.truncate mw).setWidth 64)
              let fl := match lf? with
                | some lf =>
                  some (.cmp mw (if lf then .var x else immS)
                                (if lf then immS else .var x) false)
                | none => killFlags T.toIsa p.2 st.flags
              let ex := match pd with
                | .gpr _ => lf?.bind fun lf => T.gpr.condOfCmp? (if lf then co else co.swap)
                | _ => none
              (p.1, p.2, fl, ex)
       else none)) = some (c, clob, flPost, ex) →
      T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
        (fun s' =>
          T.mach.PDstHolds s' .bool pd (co.evalBits vt ci) ∧
          FlagFactOk T G s' flPost ∧ FlagFactScope nv flPost ∧
          (∀ cc, ex = some cc → T.mach.evalCond s' cc = co.evalBits vt ci) ∧
          T.mach.mem s' = T.mach.mem s) post := by
    intro mw x hmw va hev hmx hr
    have hmw64 : mw ≤ 64 := Nat.le_of_lt (Nat.lt_of_lt_of_le hmw hw)
    have himmOk : SymBits G mw (ci.truncate mw) (.immBits mw ((ci.truncate mw).setWidth 64)) :=
      symBits_imm64 hmw64 (ci.truncate mw)
    have hvarLt : symArgScopeOk nv (.var x) = true := by
      simp [symArgScopeOk, Nat.ble_eq]; exact hA.ctx_lt _ hmx
    have himmLt : symArgScopeOk nv (.immBits mw ((ci.truncate mw).setWidth 64)) = true := by
      simp [symArgScopeOk]
    rcases orElse_eq_some hr with h1 | h2
    · cases hmd : st.memDefs.find? x with
      | none => simp [hmd] at h1
      | some p =>
        rcases p with ⟨tm, addr⟩
        cases tm with
        | bits m' =>
          simp only [hmd] at h1
          split at h1
          · rename_i hmeq
            have hm' : m' = mw := Nat.beq_eq.mp hmeq
            subst hm'
            obtain ⟨-, hlv0⟩ := hM x (.bits m') addr hmd
            obtain ⟨a₁, ha₁, hlv⟩ := hlv0 va hmx
            obtain ⟨aa, hk, hreg, haev⟩ := tryAddr_ok hA ha₁ h1
            obtain ⟨⟨c0, cl0⟩, hcm, hex⟩ := Option.map_eq_some_iff.mp hk
            have hsx := memDefs_tryAddr_symBits hA hM hmd hmx h1
            have hce : c0 = c ∧ cl0 = clob := by
              unfold cmpMemRes at hex; split at hex <;> simp only [Prod.mk.injEq] at hex <;>
                exact ⟨hex.1, hex.2.1⟩
            rcases hce with ⟨rfl, rfl⟩
            have hlm : loadVal (T.mach.mem s) (.bits m') (aa.eval (T.mach.getGpr s)) = some va := by
              rw [haev]; exact loadVal_frame hI.2.2.2.1 hlv
            rw [hev]
            exact cmpMemRes_with_flags hmw64 hA.flags_ok hA.flags_lt hsx himmOk hmx himmOk
              hvarLt himmLt hex hcm (by simpa [PArg.gprs] using hreg) hdg hlm rfl
          · simp at h1
        | _ => simp [hmd] at h1
    · split at h2
      · obtain ⟨rx, hk, hrx, hgx⟩ := tryGpr_ok hA h2
        obtain ⟨⟨c0, cl0⟩, hop, hex⟩ := Option.map_eq_some_iff.mp hk
        simp only [Prod.mk.injEq] at hex
        rcases hex with ⟨rfl, rfl, hflEq, hexEq⟩
        cases hcmo : T.gpr.cmpFlagsOut? co mw (.gpr rx) (.imm (ci.truncate mw)) pd with
        | none =>
          rw [hcmo] at hflEq hexEq; dsimp only at hflEq hexEq
          subst hflEq
          have hexNone : ex = none := by cases pd <;> simpa using hexEq.symm
          subst hexNone
          intro hc hkont
          refine T.gprSpec.op_spec (P := fun r => r = (co.evalBits va (ci.truncate mw), ()))
            hop (by simpa [tupArgGprs, PArg.gprs] using hrx)
            (by simpa [tupDstGprs] using hdg)
            (.cons (hgx _ _ hmx) (.cons rfl .nil)) (by simp [OpCode.wp_cmp, liftCmp]) hc
            fun s' ⟨⟨⟨b, ⟨⟩⟩, hb, hpd⟩, hm⟩ hfr => ?_
          cases hb; cases hpd with | cons hd _ =>
          exact hkont s' ⟨hev ▸ hd, hA.flags_ok.kill hfr, hA.flags_lt.kill,
            (fun _ hh => nomatch hh), hm⟩ (by simpa [tupDstGprs] using hfr)
        | some lf =>
          rw [hcmo] at hflEq hexEq; dsimp only at hflEq hexEq
          rw [← hflEq, ← hexEq, hev]
          refine (T.gprSpec.op_cmpFlags_spec hcmo hop (by simpa [PArg.gprs] using hrx) hdg
            (hgx _ _ hmx) rfl).conseq fun s' ⟨hd, hfl, hm⟩ _ => ?_
          refine ⟨hd, ⟨hmw64, if lf then va else ci.truncate mw,
            if lf then ci.truncate mw else va, ?_, ?_, ?_, ?_, hfl⟩, ⟨?_, ?_⟩,
            fun cc hcc => ?_, hm⟩
          · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
            · exact himmOk
            · exact hmx
          · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
            · exact himmOk
            · exact fun v hv => by rw [← (hgx (.bits mw) v hv).2, (hgx (.bits mw) _ hmx).2]
          · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
            · exact hmx
            · exact himmOk
          · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
            · exact fun v hv => by rw [← (hgx (.bits mw) v hv).2, (hgx (.bits mw) _ hmx).2]
            · exact himmOk
          · cases lf <;> simp [hvarLt, himmLt]
          · cases lf <;> simp [hvarLt, himmLt]
          · cases pd <;> simp at hcc
            have hf := hfl (if lf then co else co.swap) cc (by simp) hcc
            rw [hf]; cases lf <;> simp [CmpOp.swap_evalBits]
      · simp at h2
  unfold tryExtCmp at h
  cases hdef : st.defs.find? t with
  | none => simp [hdef] at h
  | some df =>
    cases df with
    | sextVar mw nw x =>
      simp only [hdef] at h
      split at h
      · simp at h
      · rename_i hgd
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
          beq_iff_eq] at hgd
        obtain ⟨⟨⟨⟨rfl, hm0⟩, hmn⟩, hco⟩, hci⟩ := hgd
        obtain ⟨-, -, -, hfun⟩ := hA.defs t _ hdef
        obtain ⟨va, hmx, rfl⟩ := hfun vt hmt
        exact run_ok hmn va (cmpOp_evalBits_signExtend hm0 hmn hco va ci hci) hmx
          (by
            cases pd <;> cases hmd : st.memDefs.find? x
            all_goals (try rw [hmd] at h); dsimp only at h ⊢; exact h)
    | zextVar mw nw x =>
      simp only [hdef] at h
      split at h
      · simp at h
      · rename_i hgd
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq,
          beq_iff_eq] at hgd
        obtain ⟨⟨⟨⟨rfl, _⟩, hmn⟩, hco⟩, hci⟩ := hgd
        obtain ⟨-, -, -, hfun⟩ := hA.defs t _ hdef
        obtain ⟨va, hmx, rfl⟩ := hfun vt hmt
        exact run_ok hmn va (cmpOp_evalBits_zeroExtend hmn hco va ci hci) hmx
          (by
            cases pd <;> cases hmd : st.memDefs.find? x
            all_goals (try rw [hmd] at h); dsimp only at h ⊢; exact h)
    | _ => simp [hdef] at h

private theorem tryCmpMemVar_with_flags {zl : Bool} {G : VCtx} {nv w x k : Nat} {co : CmpOp}
    (hw : w ≤ 64) {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {vx : BitVec w} {other₁ : Arg Val (.bits w)} {other : Arg VNat (.bits w)}
    {pd : PDst T.Reg T.VReg T.Cond .bool} {c : List T.Directive} {clob : FlagMask}
    {flPost : Option FlagFact} {ex : Option T.Cond}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hmx : ⟨.bits w, vx, x⟩ ∈ G)
    (hrel : ArgRel G (.bits w) other₁ other) (hdg : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch)
    (h : ((tryCmpMemVar T.toIsa st co w x other pd).map fun p =>
      match toSymArg T.toIsa (.bits w) other with
      | some sb => cmpMemRes T.toIsa st co w (.var x) sb pd p.1 p.2
      | none => (p.1, p.2, killFlags T.toIsa p.2 st.flags, none)) = some (c, clob, flPost, ex)) :
    T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
      (fun s' =>
        T.mach.PDstHolds s' .bool pd (co.evalBits vx other₁.val) ∧
        FlagFactOk T G s' flPost ∧ FlagFactScope nv flPost ∧
        (∀ cc, ex = some cc → T.mach.evalCond s' cc = co.evalBits vx other₁.val) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  obtain ⟨⟨c0, cl0⟩, hcmv, hmap⟩ := Option.map_eq_some_iff.mp h
  unfold tryCmpMemVar at hcmv
  cases hmd : st.memDefs.find? x with
  | none => simp [hmd] at hcmv
  | some p =>
    rcases p with ⟨tm, addr⟩
    cases tm with
    | bits w' =>
      simp only [hmd] at hcmv
      split at hcmv
      · rename_i heq
        have hw' : w' = w := Nat.beq_eq.mp heq
        subst hw'
        obtain ⟨-, hlv0⟩ := hM x (.bits w') addr hmd
        obtain ⟨a₁, ha₁, hlv⟩ := hlv0 vx hmx
        obtain ⟨aa, hk1, hreg, hev⟩ := tryAddr_ok hA ha₁ hcmv
        obtain ⟨pb, hk2, hpb, -, hphp⟩ := tryArg_ok hA hrel hk1
        have hlm : loadVal (T.mach.mem s) (.bits w') (aa.eval (T.mach.getGpr s)) = some vx := by
          rw [hev]; exact loadVal_frame hI.2.2.2.1 hlv
        have hsx := memDefs_tryAddr_symBits hA hM hmd hmx hcmv
        have hsx_lt : symArgScopeOk nv (.var x) = true := by
          simp [symArgScopeOk, Nat.ble_eq]; exact hA.ctx_lt _ hmx
        cases hsb : toSymArg T.toIsa (.bits w') other with
        | none =>
          rw [hsb] at hmap; dsimp only at hmap
          simp only [Prod.mk.injEq] at hmap; rcases hmap with ⟨rfl, rfl, rfl, rfl⟩
          refine (T.gprSpec.cmpMem_spec hk2
            (fun r hr => (List.mem_append.mp hr).elim (hreg r) (hpb r)) hdg hlm hphp).conseq
            fun s' ⟨hd, hm⟩ hfr =>
              ⟨hd, hA.flags_ok.kill hfr, hA.flags_lt.kill, (fun _ h => nomatch h), hm⟩
        | some sb =>
          rw [hsb] at hmap; dsimp only at hmap
          have hsb_ok := tryArg_bits_det hA hw hrel hk1 hsb
          have hsb_lt := symArgScopeOk_of_argRel hA.ctx_lt hrel hsb
          have hcm_eq : c0 = c ∧ cl0 = clob := by
            unfold cmpMemRes at hmap; split at hmap <;> simp only [Prod.mk.injEq] at hmap <;>
              exact ⟨hmap.1, hmap.2.1⟩
          rcases hcm_eq with ⟨rfl, rfl⟩
          have hsb_at := symValAt_of_toSymArg (T := T) hw hrel hsb
          exact cmpMemRes_with_flags hw hA.flags_ok hA.flags_lt hsx hsb_ok hmx hsb_at hsx_lt
            hsb_lt hmap hk2 (fun r hr => (List.mem_append.mp hr).elim (hreg r) (hpb r)) hdg hlm hphp
      · simp at hcmv
    | _ => simp [hmd] at hcmv

theorem tryFuseCmp_ok {zl : Bool} {G : VCtx} {nv k : Nat} {vh : VariantHint}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {sig ts : List Ty} {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig}
    {args : Tup (Arg VNat) sig} {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts}
    {P : Tup Val ts → Prop} {c : List T.Directive} {clob : FlagMask}
    {flPost : Option FlagFact} {ex : Option T.Cond}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch) (hwp : code.wp (vals args₁) P)
    (h : tryFuseCmp T.toIsa st vh code args dsts = some (c, clob, flPost, ex)) :
    T.mach.FallsTo T.gpr.condReads host k c (tupDstGprs dsts ++ T.frame.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
          (∀ cc, ex = some cc → ∃ (ht : ts = [.bool]) (b : Bool),
            rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b)) ∧
        FlagFactOk T G s' flPost ∧ FlagFactScope nv flPost ∧
        T.mach.mem s' = T.mach.mem s) post := by
  cases code with
  | cmp co ty mty hm =>
    cases ty with
    | bits w =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩
        rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
        rcases dsts with ⟨pd, ⟨⟩⟩
        cases hargs with | cons ha hb => cases hb with | cons hb _ =>
        have hdg1 : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch := fun r hr =>
          hdg r (by simpa [tupDstGprs] using hr)
        have hP : P (co.evalBits a₁.val b₁.val, ()) := by
          simpa [OpCode.wp_cmp, vals, liftCmp] using hwp
        have wrap : ∀ {bval : Bool}, bval = co.evalBits a₁.val b₁.val →
            T.mach.FallsTo T.gpr.condReads host k c (pd.gprs ++ T.frame.scratch) [] clob s
              (fun s' => T.mach.PDstHolds s' .bool pd bval ∧
                FlagFactOk T G s' flPost ∧ FlagFactScope nv flPost ∧
                (∀ cc, ex = some cc → T.mach.evalCond s' cc = bval) ∧
                T.mach.mem s' = T.mach.mem s) post →
            T.mach.FallsTo T.gpr.condReads host k c
              (tupDstGprs (ts := [.bool]) (pd, ()) ++ T.frame.scratch) [] clob s
              (fun s' => (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') (as := [.bool]) (pd, ()) rvs ∧
                  (∀ cc, ex = some cc → ∃ (ht : [Ty.bool] = [.bool]) (b : Bool),
                    rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b)) ∧
                FlagFactOk T G s' flPost ∧ FlagFactScope nv flPost ∧
                T.mach.mem s' = T.mach.mem s) post := by
          intro bval heq hft hc hkont
          refine hft hc fun s' ⟨hd, hfo, hfl, hex, hms⟩ hfr =>
            hkont s' ⟨⟨(co.evalBits a₁.val b₁.val, ()), hP, .cons (heq ▸ hd) .nil,
              fun cc hcc => ⟨rfl, _, rfl, heq ▸ hex cc hcc⟩⟩, hfo, hfl, hms⟩
              (by simpa [tupDstGprs] using hfr)
        unfold tryFuseCmp at h
        dsimp only at h
        split at h
        · simp at h
        rename_i hwn
        have hw : w ≤ 64 := Nat.ble_eq.mp (by simpa using hwn)
        rcases orElse_eq_some h with ht | h
        · split at ht
          · rename_i hco
            have hcoEq : (if co == .ne then CmpOp.ne else CmpOp.eq) = co := by
              cases co <;> simp at hco ⊢
            obtain ⟨⟨c0, cl0⟩, ht', he⟩ := Option.map_eq_some_iff.mp ht
            simp only [Prod.mk.injEq] at he
            rcases he with ⟨rfl, rfl, rfl, rfl⟩
            cases a with
            | var t =>
              cases b with
              | imm c0 =>
                dsimp only at ht'
                split at ht'
                · rename_i hc0
                  have hc0' : c0 = 0#w := beq_iff_eq.mp hc0
                  cases ha with | var hmt => cases hb with | imm =>
                  exact wrap (by rw [hcoEq, hc0']; rfl)
                    ((tryTestFuse_ok hA hI hM hmt hdg1 ht').conseq fun s' ⟨h1, h2, h3⟩ hfr =>
                      ⟨h1, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
                · simp at ht'
              | var _ => simp at ht'
            | imm c0 =>
              cases b with
              | var t =>
                dsimp only at ht'
                split at ht'
                · rename_i hc0
                  have hc0' : c0 = 0#w := beq_iff_eq.mp hc0
                  cases ha with | imm => cases hb with | var hmt =>
                  refine wrap ?_
                    ((tryTestFuse_ok hA hI hM hmt hdg1 ht').conseq fun s' ⟨h1, h2, h3⟩ hfr =>
                      ⟨h1, hA.flags_ok.kill hfr, hA.flags_lt.kill, h2, h3⟩)
                  rw [hcoEq, ← CmpOp.swap_evalBits]
                  cases co <;> simp [CmpOp.swap, hc0'] at hco ⊢
                · simp at ht'
              | imm _ => simp at ht'
          · simp at ht
        rcases orElse_eq_some h with he | hm'
        · cases a with
          | var t =>
            cases b with
            | imm ci =>
              cases ha with | var hmt => cases hb with | imm =>
              exact wrap rfl (tryExtCmp_ok hw hA hI hM hmt hdg1 he)
            | var _ => simp at he
          | imm ci =>
            cases b with
            | var t =>
              cases ha with | imm => cases hb with | var hmt =>
              exact wrap (CmpOp.swap_evalBits co _ _) (tryExtCmp_ok hw hA hI hM hmt hdg1 he)
            | imm _ => simp at he
        · rcases orElse_eq_some hm' with hm1 | hm2
          · cases a with
            | var x =>
              cases ha with | var hmx =>
              exact wrap rfl (tryCmpMemVar_with_flags hw hA hI hM hmx hb hdg1 hm1)
            | imm _ => simp at hm1
          · cases b with
            | var y =>
              cases hb with | var hmy =>
              exact wrap (CmpOp.swap_evalBits co _ _)
                (tryCmpMemVar_with_flags hw hA hI hM hmy ha hdg1 hm2)
            | imm _ => simp at hm2
      | _ => simp [tryFuseCmp] at h
    | _ => simp [tryFuseCmp] at h
  | _ => simp [tryFuseCmp] at h

theorem setWidth_widen_64 {w l : Nat} (x : BitVec w) (h : w ≤ l) :
    (x.setWidth l).setWidth 64 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_setWidth]
  by_cases hjw : j < w
  · simp [hjw, show j < l by omega]
  · simp [BitVec.getLsbD_of_ge x j (by omega)]

theorem signExtend_setWidth_le {w n : Nat} (x : BitVec w) (hn : n ≤ 64) :
    (x.signExtend 64).setWidth n = x.signExtend n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < 64 by omega]

theorem tryLoadSext_ok {zl : Bool} {G : VCtx} {nv k : Nat} {vh : VariantHint}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {sig ts : List Ty} {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig}
    {args : Tup (Arg VNat) sig} {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts}
    {P : Tup Val ts → Prop} {c : List T.Directive} {clob : FlagMask}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch) (hwp : code.wp (vals args₁) P)
    (h : tryLoadSext T.toIsa st vh code args dsts = some (c, clob)) :
    T.mach.FallsTo T.gpr.condReads host k c (tupDstGprs dsts ++ T.frame.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs) ∧
        T.mach.mem s' = T.mach.mem s) post := by
  cases code <;> try (simp [tryLoadSext] at h; done)
  rename_i m0 n0
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
        | bits m' =>
          simp only [hmd] at h
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hcond
            obtain ⟨rfl, hn⟩ := hcond
            rcases args₁ with ⟨a₁, ⟨⟩⟩
            cases hargs with
            | cons ha₁ _ =>
              cases ha₁ with
              | var hmx =>
                rename_i vx
                obtain ⟨-, hlv0⟩ := hM x (.bits m') addr hmd
                obtain ⟨b₁, hb₁, hlv⟩ := hlv0 vx hmx
                have hrd : rd ∉ T.frame.scratch := hdg rd (by simp [tupDstGprs])
                simp only [OpCode.wp, vals, Arg.val] at hwp
                rcases orElse_eq_some h with hta | htz
                · obtain ⟨aa, hk1, hreg, hev⟩ := tryAddr_ok hA hb₁ hta
                  have hlm : loadVal (T.mach.mem s) (.bits m') (aa.eval (T.mach.getGpr s)) =
                      some vx := by rw [hev]; exact loadVal_frame hI.2.2.2.1 hlv
                  refine fun hinf kont => T.gprSpec.loadSext_spec hk1 hrd hreg hlm hinf
                    fun s' ⟨hg, hm⟩ hfr => kont s' ⟨⟨(vx.signExtend n0, ()), hwp.2,
                      TRel.cons ⟨hn, by rw [hg]; exact signExtend_setWidth_le vx hn⟩ .nil⟩, hm⟩ ?_
                  simpa [tupDstGprs] using hfr
                · obtain ⟨rb, ri, sc, disp, vb, vi, hk1, hrb, hri, hvb, hvi, hev⟩ :=
                    tryAddrZext_ok hA hb₁ htz
                  have hlm : loadVal (T.mach.mem s) (.bits m')
                      (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) = some vx := by
                    rw [hev]; exact loadVal_frame hI.2.2.2.1 hlv
                  refine fun hinf kont => T.gprSpec.loadSextZextIdx_spec hk1 hrd hrb hri hvb hvi
                    hlm hinf fun s' ⟨hg, hm⟩ hfr => kont s' ⟨⟨(vx.signExtend n0, ()), hwp.2,
                      TRel.cons ⟨hn, by rw [hg]; exact signExtend_setWidth_le vx hn⟩ .nil⟩, hm⟩ ?_
                  simpa [tupDstGprs] using hfr
          · simp at h
        | _ => simp [hmd] at h

private theorem normCmpOp_cmp (I : Isa) (co : CmpOp) (n : Nat) (hpf : Ty.bool = (Ty.bits n).mask)
    (a b : Arg VNat (Ty.bits n)) (pd : PDst I.Reg I.VReg I.Cond Ty.bool) :
    normCmpOp (I := I) { code := .cmp co (.bits n) .bool hpf, args := (a, b, ()) } (pd, ()) =
    let (co', a', b') := normCmpExpr co n a b
    let ok := match pd with
      | .gpr _ => true
      | .flag cd => I.gpr.condOfCmp? co' == some cd
      | .vec _ => false
    if ok then { code := .cmp co' (.bits n) .bool hpf, args := (a', b', ()) }
    else { code := .cmp co (.bits n) .bool hpf, args := (a, b, ()) } := rfl

theorem normCmpOp_ok {G : VCtx} {ts sig : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hargs : TRel (ArgRel G) args₁ args) (dsts : Tup (PDst T.Reg T.VReg T.Cond) ts) :
    ∃ op₁N : Op Val ts,
      OpRel G op₁N (normCmpOp (I := T.toIsa) { code := code, args := args } dsts) ∧
      ∀ Q : Tup Val ts → Prop, code.wp (vals args₁) Q → op₁N.wp Q := by
  cases ts with
  | nil => exact ⟨{ code := code, args := args₁ }, OpRel.mk code hargs, fun _ h => h⟩
  | cons t0 ts0 =>
    cases ts0 with
    | cons _ _ =>
      cases t0 <;>
        exact ⟨{ code := code, args := args₁ }, OpRel.mk code hargs, fun _ h => h⟩
    | nil =>
      cases t0 with
      | bits _ | float _ | pair _ _ =>
        exact ⟨{ code := code, args := args₁ }, OpRel.mk code hargs, fun _ h => h⟩
      | bool =>
        cases code
        case cmp co ty hpf =>
          cases ty with
          | float _ | bool | pair _ _ =>
            exact ⟨{ code := .cmp co _ .bool hpf, args := args₁ }, OpRel.mk _ hargs, fun _ h => h⟩
          | bits n =>
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
            rcases dsts with ⟨pd, ⟨⟩⟩
            cases hargs with | cons ha hb => cases hb with | cons hb _ =>
            have keepCmp : ∃ op₁N : Op Val [.bool],
                OpRel G op₁N { code := .cmp co (.bits n) .bool hpf, args := (a, b, ()) } ∧
                ∀ Q : Tup Val [.bool] → Prop,
                  (OpCode.cmp co (.bits n) .bool hpf).wp (vals (a₁, b₁, ())) Q → op₁N.wp Q :=
              ⟨{ code := .cmp co (.bits n) .bool hpf, args := (a₁, b₁, ()) },
                .mk (.cmp co (.bits n) .bool hpf) (.cons ha (.cons hb .nil)), fun _ h => h⟩
            cases a with
            | var t =>
              cases b with
              | var y =>
                cases pd with
                | gpr _ | vec _ => rw [normCmpOp_cmp]; exact keepCmp
                | flag cd =>
                  rw [normCmpOp_cmp]
                  dsimp only [normCmpExpr]
                  by_cases hcd : (T.gpr.condOfCmp? co == some cd) = true
                  · simp [hcd]; exact keepCmp
                  · simp [hcd]; exact keepCmp
              | imm c =>
                cases ha with | var hm => cases hb with | imm =>
                rename_i vt
                let mkNorm : ∃ op₁N : Op Val [.bool],
                    OpRel G op₁N { code := .cmp (normCmpZero1 co c).1 (.bits n) .bool hpf,
                                   args := (.var t, .imm (normCmpZero1 co c).2, ()) } ∧
                    ∀ Q : Tup Val [.bool] → Prop,
                      (OpCode.cmp co (.bits n) .bool hpf).wp
                        (vals ((.var vt, .imm c, ()) : Tup (Arg Val) [.bits n, .bits n])) Q →
                      op₁N.wp Q :=
                  ⟨{ code := .cmp (normCmpZero1 co c).1 (.bits n) .bool hpf,
                     args := (.var vt, .imm (normCmpZero1 co c).2, ()) },
                    .mk (.cmp _ (.bits n) .bool hpf) (.cons (.var hm) (.cons (.imm _) .nil)),
                    fun Q hQ => by
                      simpa [Op.wp, OpCode.wp_cmp, vals, liftCmp, Arg.val,
                        normCmpZero1_evalBits co vt c] using hQ⟩
                cases pd with
                | gpr _ => rw [normCmpOp_cmp]; exact mkNorm
                | vec _ => rw [normCmpOp_cmp]; exact keepCmp
                | flag cd =>
                  rw [normCmpOp_cmp]
                  dsimp only [normCmpExpr]
                  by_cases hcd : (T.gpr.condOfCmp? (normCmpZero1 co c).1 == some cd) = true
                  · simp [hcd]; exact mkNorm
                  · simp [hcd]; exact keepCmp
            | imm c =>
              cases b with
              | imm d =>
                cases pd with
                | gpr _ | vec _ => rw [normCmpOp_cmp]; exact keepCmp
                | flag cd =>
                  rw [normCmpOp_cmp]
                  dsimp only [normCmpExpr]
                  by_cases hcd : (T.gpr.condOfCmp? co == some cd) = true
                  · simp [hcd]; exact keepCmp
                  · simp [hcd]; exact keepCmp
              | var t =>
                cases ha with | imm => cases hb with | var hm =>
                rename_i vt
                by_cases hc0 : ((normCmpZero1 co.swap c).2 == 0#n) = true
                · have hc0eq : (normCmpZero1 co.swap c).2 = 0#n := beq_iff_eq.mp hc0
                  let mkNorm : ∃ op₁N : Op Val [.bool],
                      OpRel G op₁N { code := .cmp (normCmpZero1 co.swap c).1 (.bits n) .bool hpf,
                                     args := (.var t, .imm 0#n, ()) } ∧
                      ∀ Q : Tup Val [.bool] → Prop,
                        (OpCode.cmp co (.bits n) .bool hpf).wp
                          (vals ((.imm c, .var vt, ()) : Tup (Arg Val) [.bits n, .bits n])) Q →
                        op₁N.wp Q :=
                    ⟨{ code := .cmp (normCmpZero1 co.swap c).1 (.bits n) .bool hpf,
                       args := (.var vt, .imm 0#n, ()) },
                      .mk (.cmp _ (.bits n) .bool hpf) (.cons (.var hm) (.cons (.imm _) .nil)),
                      fun Q hQ => by
                        simp only [Op.wp, OpCode.wp_cmp, vals, liftCmp, Arg.val] at hQ ⊢
                        rwa [← CmpOp.swap_evalBits, ← normCmpZero1_evalBits co.swap vt c,
                          hc0eq] at hQ⟩
                  cases pd with
                  | gpr _ => rw [normCmpOp_cmp]; dsimp only [normCmpExpr]; simp [hc0]; exact mkNorm
                  | vec _ => rw [normCmpOp_cmp]; dsimp only; exact keepCmp
                  | flag cd =>
                    rw [normCmpOp_cmp]; dsimp only [normCmpExpr]; simp [hc0]
                    split
                    · exact mkNorm
                    · exact keepCmp
                · cases pd with
                  | gpr _ | flag _ =>
                    rw [normCmpOp_cmp]; dsimp only [normCmpExpr]; simp [hc0]; exact keepCmp
                  | vec _ => rw [normCmpOp_cmp]; dsimp only; exact keepCmp
        all_goals
          exact ⟨{ code := _, args := args₁ }, OpRel.mk _ hargs, fun _ h => h⟩

private theorem deferBoolDef_ok {G : VCtx} {nv : Nat} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {co : CmpOp} {n : Nat}
    {a₁ b₁ : Arg Val (.bits n)} {a b : Arg VNat (.bits n)}
    (hlt : ∀ p ∈ G, p.2.2 < nv) (hn : n ≤ 64) {co0 : CmpOp} {t : Nat}
    (hpair : (match a, b with
      | .var t, .imm c =>
        let (co0, c0) := normCmpZero1 co c
        if c0 == 0#n then some (co0, t) else none
      | .imm c, .var t =>
        let (co0, c0) := normCmpZero1 co.swap c
        if c0 == 0#n then some (co0, t) else none
      | _, _ => none) = some (co0, t))
    (h1 : ArgRel G (.bits n) a₁ a) (h2 : ArgRel G (.bits n) b₁ b) :
    let res := co.evalBits a₁.val b₁.val
    let df := match defs.find? t with
      | some (.andVarImm w x mask) =>
        if (co0 == .eq || co0 == .ne) && Nat.beq w n then
          DefFact.testBitVar (co0 == .ne) w x mask
        else .cmpZeroVar co0 n t
      | some (.sextVar m n' x) =>
        if Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsSignedOrEq co0 then
          .cmpZeroVar co0 m x
        else .cmpZeroVar co0 n t
      | some (.zextVar m n' x) =>
        if Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsUnsignedOrEq co0 then
          .cmpZeroVar co0 m x
        else .cmpZeroVar co0 n t
      | _ => .cmpZeroVar co0 n t
    DefOk (⟨Ty.bool, res, nv⟩ :: G) nv df := by
  intro res df
  have hbase : ∃ vt : BitVec n, ⟨.bits n, vt, t⟩ ∈ G ∧ res = co0.evalBits vt 0#n := by
    cases a <;> cases b <;> simp only at hpair
    · cases hpair
    · split at hpair
      · next hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        cases h1 with | var hm => cases h2 with | imm =>
        exact ⟨_, hm, by
          dsimp [res]; rw [← normCmpZero1_evalBits co _ _, beq_iff_eq.mp hc]⟩
      · simp at hpair
    · split at hpair
      · next hc =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        cases h1 with | imm => cases h2 with | var hm =>
        exact ⟨_, hm, by
          dsimp [res]
          rw [← CmpOp.swap_evalBits, ← normCmpZero1_evalBits co.swap _ _, beq_iff_eq.mp hc]⟩
      · simp at hpair
    · cases hpair
  obtain ⟨vt, hmt, hres⟩ := hbase
  have hCmpT : DefOk (⟨Ty.bool, res, nv⟩ :: G) nv (.cmpZeroVar co0 n t) := by
    refine ⟨hn, fun cv hcv => ?_⟩
    cases mem_cons_top hlt hcv
    exact ⟨vt, List.mem_cons_of_mem _ hmt, hres⟩
  dsimp only [df]
  cases hdx : defs.find? t with
  | none => exact hCmpT
  | some d =>
    have hdok := hdefs t d hdx
    cases d with
    | andVarImm w x mask =>
      dsimp only; split
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.beq_eq] at hc
        obtain ⟨hco, rfl⟩ := hc
        obtain ⟨hw, hx⟩ := hdok
        obtain ⟨vx, hmx, rfl⟩ := hx vt hmt
        refine ⟨hw, fun cv hcv => ?_⟩
        cases mem_cons_top hlt hcv
        refine ⟨vx, List.mem_cons_of_mem _ hmx, ?_⟩
        rw [hres]; rcases hco with rfl | rfl <;> simp
      · exact hCmpT
    | sextVar m n' x =>
      dsimp only; split
      · rename_i hc
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
        obtain ⟨⟨⟨rfl, hm0⟩, hmn⟩, hco⟩ := hc
        obtain ⟨_, _, _, hx⟩ := hdok
        obtain ⟨vx, hmx, rfl⟩ := hx vt hmt
        refine ⟨by omega, fun cv hcv => ?_⟩
        cases mem_cons_top hlt hcv
        refine ⟨vx, List.mem_cons_of_mem _ hmx, ?_⟩
        have htr : ((0#n').truncate m).signExtend n' = 0#n' := by
          apply BitVec.eq_of_toInt_eq
          rw [BitVec.toInt_signExtend_of_le (Nat.le_of_lt hmn)]
          simp [BitVec.truncate]
        have hev := cmpOp_evalBits_signExtend hm0 hmn hco vx 0#n' htr
        have h0m : (0#n').truncate m = 0#m := BitVec.eq_of_toNat_eq (by simp [BitVec.truncate])
        rw [hres, hev, h0m]
      · exact hCmpT
    | zextVar m n' x =>
      dsimp only; split
      · rename_i hc
        simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
        obtain ⟨⟨⟨rfl, hm0⟩, hmn⟩, hco⟩ := hc
        obtain ⟨_, _, _, hx⟩ := hdok
        obtain ⟨vx, hmx, rfl⟩ := hx vt hmt
        refine ⟨by omega, fun cv hcv => ?_⟩
        cases mem_cons_top hlt hcv
        refine ⟨vx, List.mem_cons_of_mem _ hmx, ?_⟩
        have htr : ((0#n').truncate m).zeroExtend n' = 0#n' := by
          apply BitVec.eq_of_toNat_eq; simp [BitVec.truncate]
        have hev := cmpOp_evalBits_zeroExtend hmn hco vx 0#n' htr
        have h0m : (0#n').truncate m = 0#m := BitVec.eq_of_toNat_eq (by simp [BitVec.truncate])
        rw [hres, hev, h0m]
      · exact hCmpT
    | _ => exact hCmpT

theorem recordBoolDef_ok {G : VCtx} {nv : Nat} {defs : Trie DefFact}
    (hdefs : ∀ x d, defs.find? x = some d → DefOk G x d) {sig rs : List Ty}
    {code : OpCode sig rs} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    (hrel : TRel (ArgRel G) args₁ args) (hlt : ∀ p ∈ G, p.2.2 < nv) {P : Tup Val rs → Prop}
    (hwp : code.wp (vals args₁) P) {df : DefFact}
    (hd : recordBoolDef defs code args = some df) :
    ∃ (_h : rs = [.bool]) (rvs : Tup Val rs), P rvs ∧
      DefOk (Tup.zip rvs (Tup.levels rs nv) ++ G) nv df := by
  cases code with
  | cmp co ty mty hty =>
    cases ty with
    | bits n =>
      cases mty with
      | bool =>
        rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
        rcases hrel with _ | ⟨ha, _ | ⟨hb, -⟩⟩
        dsimp only [recordBoolDef] at hd
        split at hd; · simp at hd
        rename_i hn
        have hnle : n ≤ 64 := Nat.ble_eq.mp (by cases hb : n.ble 64 <;> simp_all)
        obtain ⟨⟨co0, t⟩, hpair, hd⟩ := Option.map_eq_some_iff.mp hd
        subst hd
        simp only [OpCode.wp, liftCmp, vals] at hwp
        exact ⟨rfl, (co.evalBits a₁.val b₁.val, ()), hwp,
          deferBoolDef_ok hdefs hlt hnle hpair ha hb⟩
      | _ => simp [recordBoolDef] at hd
    | _ => simp [recordBoolDef] at hd
  | _ => simp [recordBoolDef] at hd


theorem tryLeaArith_ok {zl : Bool} {G : VCtx} {nv k : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64} {sig ts : List Ty}
    {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {clob : FlagMask} {z32 : Bool}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hargs : TRel (ArgRel G) args₁ args) (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hwp : code.wp (vals args₁) P) (hinf : c.IsInfixAt (T.mach.prog host) k)
    (h : tryLeaArith T.toIsa st code args dsts = some (c, clob, z32))
    (fin : z32 = false → ∀ s',
      (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs) → T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post)
    (fin32 : z32 = true → ∀ {rd} (ht : ts = [.bits 32]),
      dsts = (ht ▸ (PDst.gpr rd, ())) → ∀ s' (rv : BitVec 32), P (ht ▸ (rv, ())) →
      T.mach.getGpr s' rd = rv.setWidth 64 → T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (rd :: T.frame.scratch) [] clob →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have _hI := hI
  cases ts with
  | nil => simp [tryLeaArith] at h
  | cons t0 ts0 =>
    cases ts0 with
    | cons _ _ => simp [tryLeaArith] at h
    | nil =>
      cases t0 with
      | bool | float _ | pair _ _ => simp [tryLeaArith] at h
      | bits w =>
        rcases dsts with ⟨d0, ⟨⟩⟩
        cases d0 with
        | vec _ => simp [tryLeaArith] at h
        | gpr rd =>
          unfold tryLeaArith at h; dsimp only at h
          have hrd : rd ∉ T.frame.scratch := hdg rd (by simp [tupDstGprs])
          rcases orElse_eq_some h with h | hzext
          · obtain ⟨⟨base?, idx, sc, disp⟩, he1, hbind⟩ := Option.bind_eq_some_iff.mp h
            have hext : ∃ (rv : BitVec w) (vi : BitVec w), P (rv, ()) ∧ ⟨.bits w, vi, idx⟩ ∈ G ∧
                ∃ vb : BitVec w, (∀ b, base? = some b → ⟨.bits w, vb, b⟩ ∈ G) ∧
                rv = (if base?.isSome then vb else 0#w) + (vi <<< sc.shift) +
                  disp.toBitVec.setWidth w := by
              by_cases h64 : w = 64
              · subst h64
                have h64b : Nat.beq 64 64 = true := rfl
                simp only [h64b, ↓reduceIte] at he1
                simpa [BitVec.setWidth_eq] using extractLea64_ok hA.defs hargs hwp he1
              · by_cases h32 : w = 32
                · subst h32
                  have h32b : Nat.beq 32 32 = true := rfl
                  have h64b : Nat.beq 32 64 = false := rfl
                  simp only [h64b, h32b, Bool.false_eq_true, ↓reduceIte] at he1
                  exact extractLea32_ok hA.defs hargs hwp he1
                · have h64b : Nat.beq w 64 = false :=
                    Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using h64)
                  have h32b : Nat.beq w 32 = false :=
                    Bool.eq_false_iff.mpr (by simpa [Nat.beq_eq] using h32)
                  simp [h64b, h32b] at he1
            obtain ⟨rv, vi, hP, hi, vb, hvb, rfl⟩ := hext
            obtain ⟨rb?, hrb, hbind⟩ := Option.bind_eq_some_iff.mp hbind
            obtain ⟨ri, hri, hbind⟩ := Option.bind_eq_some_iff.mp hbind
            obtain ⟨⟨c', cl'⟩, hlea, heq⟩ := Option.map_eq_some_iff.mp hbind
            rcases heq with ⟨rfl, rfl, rfl⟩
            obtain ⟨hri_s, hri_g⟩ := findGprFor_ok hA hri
            have hvi : GprHolds (T.mach.getGpr s ri) (.bits w) vi := hri_g _ _ hi
            have hrb_ok : (∀ r, rb? = some r → r ∉ T.frame.scratch) ∧
                (∀ r, rb? = some r → GprHolds (T.mach.getGpr s r) (.bits w) vb) ∧
                rb?.isSome = base?.isSome := by
              cases base? with
              | none =>
                cases hrb; exact ⟨(fun _ h => by cases h), (fun _ h => by cases h), rfl⟩
              | some b =>
                obtain ⟨rb, hfb, he⟩ := Option.map_eq_some_iff.mp hrb; subst he
                obtain ⟨hsb, hgb⟩ := findGprFor_ok hA hfb
                exact ⟨fun _ he => by cases he; exact hsb,
                  fun _ he => by cases he; exact hgb _ _ (hvb b rfl), rfl⟩
            by_cases hz : (Nat.beq w 32 && T.toIsa.gpr.zeroUpper32LeaArith) = true
            · obtain ⟨rfl, hz32⟩ : w = 32 ∧ T.toIsa.gpr.zeroUpper32LeaArith = true := by
                simpa [Bool.and_eq_true, Nat.beq_eq] using hz
              refine T.gprSpec.leaArith_zero32 hz32 hlea hrb_ok.1 hri_s hrd hrb_ok.2.1 hvi hinf
                fun s' ⟨hg, hm⟩ hfr => ?_
              rw [hrb_ok.2.2] at hg
              exact fin32 hz rfl rfl s' _ hP hg hm hfr
            · refine T.gprSpec.leaArith_spec hlea hrb_ok.1 hri_s hrd hrb_ok.2.1 hvi hinf
                fun s' ⟨hg, hm⟩ hfr => ?_
              rw [hrb_ok.2.2] at hg
              exact fin (Bool.eq_false_iff.mpr hz) s' ⟨_, hP, TRel.cons hg .nil⟩ hm
                (by simpa [tupDstGprs] using hfr)
          · by_cases h64 : w = 64
            · subst h64; dsimp only [tryLeaArithZext] at hzext
              obtain ⟨⟨base?, idx, sh, disp⟩, he1, hbind⟩ := Option.bind_eq_some_iff.mp hzext
              obtain ⟨rv, vi, hP, hi, vb, hvb, rfl⟩ :=
                extractLeaZext64_ok hA.defs hargs hwp he1
              obtain ⟨rb?, hrb, hbind⟩ := Option.bind_eq_some_iff.mp hbind
              obtain ⟨ri, hri, hbind⟩ := Option.bind_eq_some_iff.mp hbind
              obtain ⟨⟨c', cl'⟩, hlea, heq⟩ := Option.map_eq_some_iff.mp hbind
              rcases heq with ⟨rfl, rfl, rfl⟩
              obtain ⟨hri_s, hri_g⟩ := findGprFor_ok hA hri
              have hvi : GprHolds (T.mach.getGpr s ri) (.bits 32) vi := hri_g _ _ hi
              have hrb_ok : (∀ r, rb? = some r → r ∉ T.frame.scratch) ∧
                  (∀ r, rb? = some r → GprHolds (T.mach.getGpr s r) (.bits 64) vb) ∧
                  rb?.isSome = base?.isSome := by
                cases base? with
                | none =>
                  cases hrb; exact ⟨(fun _ h => by cases h), (fun _ h => by cases h), rfl⟩
                | some b =>
                  obtain ⟨rb, hfb, he⟩ := Option.map_eq_some_iff.mp hrb; subst he
                  obtain ⟨hsb, hgb⟩ := findGprFor_ok hA hfb
                  exact ⟨fun _ he => by cases he; exact hsb,
                    fun _ he => by cases he; exact hgb _ _ (hvb b rfl), rfl⟩
              refine T.gprSpec.leaArithZext_spec hlea hrb_ok.1 hri_s hrd hrb_ok.2.1 hvi hinf
                fun s' ⟨hg, hm⟩ hfr => ?_
              rw [hrb_ok.2.2] at hg
              exact fin rfl s' ⟨_, hP, TRel.cons hg .nil⟩ hm (by simpa [tupDstGprs] using hfr)
            · simp only [tryLeaArithZext] at hzext
              split at hzext
              · exfalso; apply h64; simp_all
              · simp at hzext

theorem tryReuseFlagCmp_ok {G : VCtx} {nv k : Nat}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)}
    {sig ts : List Ty} {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig}
    {args : Tup (Arg VNat) sig} {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts}
    {P : Tup Val ts → Prop} {c : List T.Directive} {clob : FlagMask}
    {flPost : Option FlagFact} {ex : Option T.Cond}
    (hA : Agree T G nv st s σ)
    (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch) (hwp : code.wp (vals args₁) P)
    (h : tryReuseFlagCmp T.toIsa st code args dsts = some (c, clob, flPost, ex)) :
    T.mach.FallsTo T.gpr.condReads host k c (tupDstGprs dsts ++ T.frame.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
          (∀ cc, ex = some cc → ∃ (ht : ts = [.bool]) (b : Bool),
            rvs = ht ▸ (b, ()) ∧ T.mach.evalCond s' cc = b)) ∧
        FlagFactOk T G s' flPost ∧ FlagFactScope nv flPost ∧
        T.mach.mem s' = T.mach.mem s) post := by
  cases hfl : st.flags with
  | none => simp [tryReuseFlagCmp, hfl] at h
  | some fl =>
    cases fl with
    | cmp w lhs rhs eqNe =>
      cases code with
      | cmp co ty mty hmty =>
        cases ty with
        | bits n =>
          cases mty with
          | bool =>
            rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
            rcases dsts with ⟨pd, ⟨⟩⟩
            cases hargs with | cons ha hb => cases hb with | cons hb _ =>
            have hP : P (co.evalBits a₁.val b₁.val, ()) := by
              simpa [OpCode.wp_cmp, vals, liftCmp] using hwp
            unfold tryReuseFlagCmp at h; rw [hfl] at h; dsimp only at h
            obtain ⟨⟨coBase, sa, sb⟩, hpair, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨coUsed, hcoU, hbind⟩ := Option.bind_eq_some_iff.mp h
            split at hbind; · simp at hbind
            rename_i hgd
            have heqNe : (!eqNe || coUsed == .eq || coUsed == .ne) = true := by
              cases eqNe <;> cases coUsed <;> simp_all
            obtain ⟨cc, hcc, hpd⟩ := Option.bind_eq_some_iff.mp hbind
            have hflOk := hA.flags_ok; have hflLt := hA.flags_lt
            rw [hfl] at hflOk hflLt
            obtain ⟨hw, va, vb, hlhsAt, hlhs, hrhsAt, hrhs, hcmp⟩ := hflOk
            obtain ⟨va', vb', hsa, hsb, hbase⟩ :=
              reuseCmpPair_ok hw hA.defs hA.ctx_uniq hlhsAt hrhsAt ha hb hpair
            have heval : T.mach.evalCond s cc = co.evalBits a₁.val b₁.val := by
              rw [hbase]
              split at hcoU
              · next hc =>
                simp only [Bool.and_eq_true, symArgEq_iff] at hc
                obtain ⟨rfl, rfl⟩ := hc
                simp only [Option.some.injEq] at hcoU; subst hcoU
                rw [hcmp coBase cc heqNe hcc,
                  symValAt_eq_symBits hsa hlhs, symValAt_eq_symBits hsb hrhs]
              · split at hcoU
                · next hc =>
                  simp only [Bool.and_eq_true, symArgEq_iff] at hc
                  obtain ⟨rfl, rfl⟩ := hc
                  simp only [Option.some.injEq] at hcoU; subst hcoU
                  rw [hcmp coBase.swap cc heqNe hcc, CmpOp.swap_evalBits,
                    symValAt_eq_symBits hsa hrhs, symValAt_eq_symBits hsb hlhs]
                · simp at hcoU
            cases pd with
            | vec _ => simp at hpd
            | flag cd =>
              dsimp only at hpd; split at hpd
              · next hc =>
                simp only [Option.some.injEq, Prod.mk.injEq] at hpd
                rcases hpd with ⟨rfl, rfl, rfl, rfl⟩
                rw [beq_iff_eq] at hc; subst hc
                intro hc' kont
                refine kont s ⟨⟨(co.evalBits a₁.val b₁.val, ()), hP,
                  .cons heval .nil, (fun _ hh => nomatch hh)⟩,
                  ?_, hflLt, rfl⟩
                  ⟨(fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl)⟩
                exact ⟨hw, va, vb, hlhsAt, hlhs, hrhsAt, hrhs, hcmp⟩
              · simp at hpd
            | gpr rd =>
              obtain ⟨⟨c0, cl0⟩, hop, hmap⟩ := Option.map_eq_some_iff.mp hpd
              simp only [Prod.mk.injEq] at hmap
              rcases hmap with ⟨rfl, rfl, rfl, rfl⟩
              intro hc' kont
              refine T.gprSpec.op_spec (P := fun r => r = (T.mach.evalCond s cc, ()))
                hop (by simp [tupArgGprs, PArg.gprs]) hdg (.cons rfl .nil)
                (by simp [OpCode.wp]) hc' fun s' ⟨⟨⟨b', ⟨⟩⟩, hb', hpd'⟩, hm⟩ hfr => ?_
              cases hb'; cases hpd' with | cons hd _ =>
              refine kont s' ⟨⟨(co.evalBits a₁.val b₁.val, ()), hP,
                .cons (heval ▸ hd) .nil, fun cc' hcc' => ?_⟩, ?_, hflLt.kill, hm⟩ hfr
              · split at hcc'
                · next hdis =>
                  simp only [Option.some.injEq] at hcc'; subst hcc'
                  exact ⟨rfl, _, rfl, (hfr.2.2 cc hdis).trans heval⟩
                · simp at hcc'
              · rw [← hfl]; exact hA.flags_ok.kill hfr
          | _ => simp [tryReuseFlagCmp, hfl] at h
        | _ => simp [tryReuseFlagCmp, hfl] at h
      | _ => simp [tryReuseFlagCmp, hfl] at h


end Lemmas

end Rega
end LeanQbe.T
