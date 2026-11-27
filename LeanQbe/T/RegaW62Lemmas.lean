module

public import LeanQbe.T.RegaLemmas1
public import LeanQbe.T.RegaLemmasCmpReuse
public import LeanQbe.T.RegaLemmas2
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.Logic.MemLemmas

/-!
# Wave 6.2-A Checked Lowering Proofs (`T.RegaW62Lemmas`)

Verifies all `RegaW62` symbolic-allocator extensions (`OPT-7` + `OPT-10`):
* Operand / address lookup (`tryGpr_ok`, `findGprFor_ok`, `tryVec_ok`, `tryFlag_ok`,
  `tryArgPref_ok`, `tryArg_ok`, `pickPArgsCode_ok`, `pickPArgs_ok`, `tryAddr_ok`, `tryAddrZext_ok`).
* Scratch-constant-aware lowering (`lowerLoadScr_ok`, `lowerStoreScr_ok`, `lowerOpScr_ok`).
* Zero-cost reg op elision (`elideRegOp?_ok`), load-truncation fusion (`tryLoadTrunc_ok`), and
  dead-low widening multiply (`tryMulHi_ok`).
* Cross-block `.gprZ` entry/parameter checking (`LocZOk`, `LiveZOk`, `ParamZVal`, `ParamsZOk`,
  `holdsZLoc_ok`, `entryZOk_ok`, `buildEntryBaseZ_ok`, `bindBlockParamsZ_ok`).
* Label-cleanliness helpers (`*_some`, `*_clean`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

/-! ## Pure helpers & Cross-Block `.gprZ` Invariants -/

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

/-- Canonical ABI zero-extension obligation for a live entry `(sa, loc)`. -/
@[expose]
def LocZOk {R V C D : Type} (M : Machine R V C D) (G : VCtx) (s : M.MData)
    (σ : List (BitVec 64)) (sa : SymArg) : Loc R V C → Prop
  | .gpr r => match sa with
    | .var _ => SymZ G (M.getGpr s r) sa
    | .immBits _ c => M.getGpr s r = c
    | .immBool b => M.getGpr s r = (if b then 1#64 else 0#64)
    | .immVec _ _ => False
  | .slot i w => w = .w64 ∧ match sa with
    | .var _ => ∃ w64, σ[i]? = some w64 ∧ SymZ G w64 sa
    | _ => False
  | .vec _ | .flag _ => False

/-- Pairwise `.gprZ` obligations across an `Entry.live` / `Entry.liveZ` list. -/
@[expose]
def LiveZOk {R V C D : Type} (M : Machine R V C D) (G : VCtx) (s : M.MData)
    (σ : List (BitVec 64)) : List (SymArg × Loc R V C) → List Bool → Prop
  | [], _ | _, [] => True
  | (sa, loc) :: rest, z :: zs => (z = true → LocZOk M G s σ sa loc) ∧ LiveZOk M G s σ rest zs

/-- Canonical ABI zero-extension obligation for a block parameter value placed at `loc`. -/
@[expose]
def ParamZVal {R V C D : Type} (M : Machine R V C D) (s : M.MData) (σ : List (BitVec 64))
    (t : Ty) (v : Val t) : Loc R V C → Prop
  | .gpr r => AbiGprHolds (M.getGpr s r) t v
  | .slot i w => w = .w64 ∧ ∃ w64, σ[i]? = some w64 ∧ AbiGprHolds w64 t v
  | .vec _ | .flag _ => False

/-- Pairwise `.gprZ` obligations across block parameters `(ts, xs, ploc, plocZ)`. -/
@[expose]
def ParamsZOk {R V C D : Type} (M : Machine R V C D) (s : M.MData) (σ : List (BitVec 64)) :
    (ts : List Ty) → Tup Val ts → List (Loc R V C) → List Bool → Prop
  | [], (), _, _ | _, _, [], _ | _, _, _, [] => True
  | t :: ts, (v, vs), loc :: locs, z :: zs =>
    (z = true → ParamZVal M s σ t v loc) ∧ ParamsZOk M s σ ts vs locs zs

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n : Nat} {Rf : Mem 64 → Prop}

/-! ## Operand and address lookups -/

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

theorem tryArgPref_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond}
    {preferReg : Bool} {t : Ty} {a₁ : Arg Val t} {a : Arg VNat t}
    {k : PArg T.Reg T.VReg T.Cond t → Option α} {res : α}
    (hrel : ArgRel G t a₁ a) (h : tryArgPref T.toIsa st pref preferReg t a k = some res) :
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
    | float _ => simp [tryArgPref] at h
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
      have regArm : tryGpr T.toIsa st.regs (.immBits w (c.setWidth 64)) (fun r => k (.gpr r)) =
            some res →
          ∃ pa, k pa = some res ∧ (∀ r ∈ pa.gprs, r ∉ T.frame.scratch) ∧
            (∀ v, pa = .vec v → v ∉ T.vec.vecScratch) ∧
            T.mach.PArgHolds s (.bits w) pa (Arg.imm c).val := by
        intro hr
        obtain ⟨r, hk, hns, hg⟩ := tryGpr_ok hA hr
        refine ⟨.gpr r, hk, by simpa [PArg.gprs] using hns, by simp, hg.1, ?_⟩
        rw [hg.2]
        exact (BitVec.setWidth_setWidth_of_le c hg.1).trans (BitVec.setWidth_eq c)
      dsimp only [tryArgPref] at h
      split at h
      · rcases orElse_eq_some h with h | h
        · exact regArm h
        · exact imm h
      · rcases orElse_eq_some h with h | h
        · exact imm h
        · split at h
          · exact regArm h
          · simp at h
    | pair a b =>
      rcases orElse_eq_some h with h | h
      · exact imm h
      split at h
      · simp at h
      · obtain ⟨v, hk, hv, hg⟩ := tryVec_ok hA h
        exact ⟨.vec v, hk, by simp [PArg.gprs], by rintro _ ⟨⟩; exact hv,
          immVec_vecHolds (vecWidth?_spec ‹_›).1 hg.2⟩
    | float _ => simp [tryArgPref] at h

theorem tryArg_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond} {t : Ty}
    {a₁ : Arg Val t} {a : Arg VNat t} {k : PArg T.Reg T.VReg T.Cond t → Option α} {res : α}
    (hrel : ArgRel G t a₁ a) (h : tryArg T.toIsa st pref t a k = some res) :
    ∃ pa, k pa = some res ∧ (∀ r ∈ pa.gprs, r ∉ T.frame.scratch) ∧
      (∀ v, pa = .vec v → v ∉ T.vec.vecScratch) ∧ T.mach.PArgHolds s t pa a₁.val :=
  tryArgPref_ok hA hrel h

theorem pickPArgsCode_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {α : Type} {pref : List T.Cond}
    {sig₀ rs₀ : List Ty} (code : OpCode sig₀ rs₀) :
    ∀ {sig : List Ty} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
      {k : Tup (PArg T.Reg T.VReg T.Cond) sig → Option α} {res : α},
    TRel (ArgRel G) args₁ args → pickPArgsCode T.toIsa st pref code args k = some res →
    ∃ pas, k pas = some res ∧ (∀ r ∈ tupArgGprs pas, r ∉ T.frame.scratch) ∧
      (∀ v ∈ tupArgVecs pas, v ∉ T.vec.vecScratch) ∧ TRel (T.mach.PArgHolds s) pas (vals args₁) :=
          by
  intro sig args₁ args k res hrel h
  induction hrel generalizing res with
  | nil => exact ⟨(), h, by simp [tupArgGprs], by simp [tupArgVecs], .nil⟩
  | cons ha _ ih =>
    simp only [pickPArgsCode] at h
    obtain ⟨pa, hk, hg, hv, hp⟩ := tryArgPref_ok hA ha h
    obtain ⟨pas, hk', hg', hv', hp'⟩ := ih (k := fun pas => k (pa, pas)) hk
    refine ⟨(pa, pas), hk', ?_, ?_, .cons hp hp'⟩
    · cases pa <;> simp_all [tupArgGprs, PArg.gprs]
    · cases pa <;> simp_all [tupArgVecs]

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
          obtain ⟨vb, hmb, hv⟩ := (hA.defs _ _ hdef).2 v hm
          exact reg hk (Or.inr ⟨_, _, hr, hmb, rfl⟩) (by simp_all [Arg.val])
        · simp at h
      · simp at h
    rcases orElse_eq_some h with h | h
    · obtain ⟨r, hr, hk⟩ := Option.bind_eq_some_iff.mp h
      exact reg hk (Or.inr ⟨_, _, hr, hm, rfl⟩) (by simp [Arg.val])
    rcases orElse_eq_some h with h | h
    · split at h
      · next base d hdef =>
        obtain ⟨rb, hr, hk⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vb, hmb, hv⟩ := (hA.defs _ _ hdef).2 v hm
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
    · split at h
      · next base idx sh d hdef =>
        obtain ⟨sc, hsc, r1⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨rb, hrb, r2⟩ := Option.bind_eq_some_iff.mp r1
        obtain ⟨ri, hri, hk⟩ := Option.bind_eq_some_iff.mp r2
        obtain ⟨vb, vi, hmb, hmi, hv⟩ := addrDefOf_ok hA.defs hdef v hm
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
    cases hdef : addrDefOf T.toIsa.gpr.addrCse st.defs x with
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
          obtain ⟨vb0, vi0, hb0, hi0, hv⟩ := addrDefOf_ok hA.defs hdef v hm
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

/-! ## Scratch-constant-aware Load / Store / Op Specs -/

theorem lowerLoadScr_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {vh : VariantHint}
    {s : T.mach.MData} {σ : List (BitVec 64)} {t : Ty} {d : T.Reg}
    {a₁ : Arg Val i64} {a : Arg VNat i64} {v : Val t}
    {c : List T.Directive} {clob : FlagMask} {scrOut : List (T.Reg × BitVec 64)} {k : Nat}
    (hA : Agree T G nv st s σ) (hrel : ArgRel G i64 a₁ a)
    (hd : d ∉ T.frame.scratch)
    (hlv : loadVal (T.mach.mem s) t a₁.val = some v)
    (hl : lowerLoadScr T.toIsa st vh t d a = some (c, clob, scrOut)) :
    T.mach.FallsTo T.gpr.condReads host k c (d :: T.frame.scratch) [] clob s
      (fun s' =>
        (if T.gpr.zeroExtLoad then AbiGprHolds (T.mach.getGpr s' d) t v
         else GprHolds (T.mach.getGpr s' d) t v) ∧
        (T.gpr.zeroUpper32Load = true → ∀ (ht : t = .bits 32),
          T.mach.getGpr s' d = (ht ▸ v).setWidth 64) ∧
        T.mach.mem s' = T.mach.mem s ∧ ScrOk T.mach T.frame.scratch scrOut s') post := by
  have runPlainAddr : ∀ {aa : AddrArg T.Reg},
      (∀ r ∈ aa.regs, r ∉ T.frame.scratch) → aa.eval (T.mach.getGpr s) = a₁.val →
      T.gpr.load t d aa = some (c, clob) → scrOut = [] →
      T.mach.FallsTo T.gpr.condReads host k c (d :: T.frame.scratch) [] clob s
        (fun s' =>
          (if T.gpr.zeroExtLoad then AbiGprHolds (T.mach.getGpr s' d) t v
           else GprHolds (T.mach.getGpr s' d) t v) ∧
          (T.gpr.zeroUpper32Load = true → ∀ (ht : t = .bits 32),
            T.mach.getGpr s' d = (ht ▸ v).setWidth 64) ∧
          T.mach.mem s' = T.mach.mem s ∧ ScrOk T.mach T.frame.scratch scrOut s') post := by
    intro aa hreg hev hld rfl
    have hlm : loadVal (T.mach.mem s) t (aa.eval (T.mach.getGpr s)) = some v := hev ▸ hlv
    by_cases hze : T.gpr.zeroExtLoad = true
    · refine (T.gprSpec.load_zext hze hld hd hreg hlm).conseq fun s' ⟨hab, hm⟩ _ => ?_
      refine ⟨by simp [hze, hab], fun _ ht => ?_, hm, scrOk_nil _ _ _⟩
      subst ht; exact hab.2
    · have hzf : T.gpr.zeroExtLoad = false := Bool.eq_false_iff.mpr hze
      by_cases hzu : T.gpr.zeroUpper32Load = true
      · by_cases ht32 : t = .bits 32
        · subst ht32
          exact (T.gprSpec.load_zero32 hzu hld hd hreg hlm).conseq fun s' ⟨h32, hm⟩ _ =>
            ⟨by simp [hzf]; exact ⟨by decide, by rw [h32]; simp⟩, fun _ _ => h32, hm,
             scrOk_nil _ _ _⟩
        · exact (T.gprSpec.load_spec hld hd hreg hlm).conseq fun s' ⟨hg, hm⟩ _ =>
            ⟨by simp [hzf, hg], fun _ ht => absurd ht ht32, hm, scrOk_nil _ _ _⟩
      · exact (T.gprSpec.load_spec hld hd hreg hlm).conseq fun s' ⟨hg, hm⟩ _ =>
          ⟨by simp [hzf, hg], fun hz => absurd hz hzu, hm, scrOk_nil _ _ _⟩
  have runPlainZext : ∀ {rb ri sc disp} {vb : BitVec 64} {vi : BitVec 32},
      rb ∉ T.frame.scratch → ri ∉ T.frame.scratch →
      GprHolds (T.mach.getGpr s rb) i64 vb → GprHolds (T.mach.getGpr s ri) (.bits 32) vi →
      vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec = a₁.val →
      T.gpr.loadZextIdx t d rb ri sc disp = some (c, clob) → scrOut = [] →
      T.mach.FallsTo T.gpr.condReads host k c (d :: T.frame.scratch) [] clob s
        (fun s' =>
          (if T.gpr.zeroExtLoad then AbiGprHolds (T.mach.getGpr s' d) t v
           else GprHolds (T.mach.getGpr s' d) t v) ∧
          (T.gpr.zeroUpper32Load = true → ∀ (ht : t = .bits 32),
            T.mach.getGpr s' d = (ht ▸ v).setWidth 64) ∧
          T.mach.mem s' = T.mach.mem s ∧ ScrOk T.mach T.frame.scratch scrOut s') post := by
    intro rb ri sc disp vb vi hrb hri hvb hvi hev hld rfl
    have hlm : loadVal (T.mach.mem s) t (vb + (vi.setWidth 64 <<< sc.shift) + disp.toBitVec) =
        some v := hev ▸ hlv
    by_cases hze : T.gpr.zeroExtLoad = true
    · refine (T.gprSpec.loadZextIdx_zext hze hld hd hrb hri hvb hvi hlm).conseq
        fun s' ⟨hab, hm⟩ _ => ?_
      refine ⟨by simp [hze, hab], fun _ ht => ?_, hm, scrOk_nil _ _ _⟩
      subst ht; exact hab.2
    · have hzf : T.gpr.zeroExtLoad = false := Bool.eq_false_iff.mpr hze
      by_cases hzu : T.gpr.zeroUpper32Load = true
      · by_cases ht32 : t = .bits 32
        · subst ht32
          exact (T.gprSpec.loadZextIdx_zero32 hzu hld hd hrb hri hvb hvi hlm).conseq
            fun s' ⟨h32, hm⟩ _ =>
              ⟨by simp [hzf]; exact ⟨by decide, by rw [h32]; simp⟩, fun _ _ => h32, hm,
               scrOk_nil _ _ _⟩
        · exact (T.gprSpec.loadZextIdx_spec hld hd hrb hri hvb hvi hlm).conseq
            fun s' ⟨hg, hm⟩ _ =>
              ⟨by simp [hzf, hg], fun _ ht => absurd ht ht32, hm, scrOk_nil _ _ _⟩
      · exact (T.gprSpec.loadZextIdx_spec hld hd hrb hri hvb hvi hlm).conseq
          fun s' ⟨hg, hm⟩ _ =>
            ⟨by simp [hzf, hg], fun hz => absurd hz hzu, hm, scrOk_nil _ _ _⟩
  unfold lowerLoadScr at hl
  rcases orElse_eq_some hl with h1 | hl
  · obtain ⟨fn, hfn, hta⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
    exact T.gprSpec.loadScr_spec hfn hk hd hreg hA.scrConsts_ok (hev ▸ hlv)
  rcases orElse_eq_some hl with h2 | h3
  · obtain ⟨fn, hfn, htz⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨rb, ri, sc, disp, vb, vi, hk, hrb, hri, hvb, hvi, hev⟩ := tryAddrZext_ok hA hrel htz
    exact T.gprSpec.loadZextIdxScr_spec hfn hk hd hrb hri hA.scrConsts_ok hvb hvi (hev ▸ hlv)
  · obtain ⟨⟨c', cl'⟩, hta, heq⟩ := Option.map_eq_some_iff.mp h3
    rcases heq with ⟨rfl, rfl, rfl⟩
    rcases orElse_eq_some hta with hta | htz
    · obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
      exact runPlainAddr hreg hev hk rfl
    · obtain ⟨rb, ri, sc, disp, vb, vi, hk, hrb, hri, hvb, hvi, hev⟩ :=
        tryAddrZext_ok hA hrel htz
      exact runPlainZext hrb hri hvb hvi hev hk rfl

theorem lowerStoreScr_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {vh : VariantHint}
    {s : T.mach.MData} {σ : List (BitVec 64)} {t : Ty}
    {pa : PArg T.Reg T.VReg T.Cond t} {v : Val t} {a₁ : Arg Val i64} {a : Arg VNat i64}
    {c : List T.Directive} {clob : FlagMask} {scrOut : List (T.Reg × BitVec 64)} {k : Nat}
    (hA : Agree T G nv st s σ) (hrel : ArgRel G i64 a₁ a)
    (hpg : ∀ r ∈ pa.gprs, r ∉ T.frame.scratch) (hp : T.mach.PArgHolds s t pa v)
    (hsok : storeOk (T.mach.mem s) t a₁.val)
    (hl : lowerStoreScr T.toIsa st vh t pa a = some (c, clob, scrOut)) :
    T.mach.FallsTo T.gpr.condReads host k c T.frame.scratch [] clob s
      (fun s' => T.mach.mem s' = storeMem (T.mach.mem s) t a₁.val v ∧
        ScrOk T.mach T.frame.scratch scrOut s') post := by
  unfold lowerStoreScr at hl
  rcases orElse_eq_some hl with h1 | hl
  · obtain ⟨fn, hfn, hta⟩ := Option.bind_eq_some_iff.mp h1
    obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
    refine (T.gprSpec.storeScr_spec hfn hk (fun r hr => (List.mem_append.mp hr).elim
      (hpg r) (hreg r)) hA.scrConsts_ok hp (hev ▸ hsok)).conseq fun s' ⟨hm, hscr⟩ _ => ?_
    rw [hev] at hm; exact ⟨hm, hscr⟩
  rcases orElse_eq_some hl with h2 | h3
  · obtain ⟨fn, hfn, htz⟩ := Option.bind_eq_some_iff.mp h2
    obtain ⟨rb, ri, sc, disp, vb, vi, hk, hrb, hri, hvb, hvi, hev⟩ := tryAddrZext_ok hA hrel htz
    refine (T.gprSpec.storeZextIdxScr_spec hfn hk hpg hrb hri hA.scrConsts_ok hp hvb hvi
      (hev ▸ hsok)).conseq fun s' ⟨hm, hscr⟩ _ => ?_
    rw [hev] at hm; exact ⟨hm, hscr⟩
  · obtain ⟨⟨c', cl'⟩, hta, heq⟩ := Option.map_eq_some_iff.mp h3
    rcases heq with ⟨rfl, rfl, rfl⟩
    rcases orElse_eq_some hta with hta | htz
    · obtain ⟨aa, hk, hreg, hev⟩ := tryAddr_ok hA hrel hta
      refine (T.gprSpec.store_spec hk (fun r hr => (List.mem_append.mp hr).elim
        (hpg r) (hreg r)) hp (hev ▸ hsok)).conseq fun s' hm _ => ?_
      rw [hev] at hm; exact ⟨hm, scrOk_nil _ _ _⟩
    · obtain ⟨rb, ri, sc, disp, vb, vi, hk, hrb, hri, hvb, hvi, hev⟩ :=
        tryAddrZext_ok hA hrel htz
      refine (T.gprSpec.storeZextIdx_spec hk hpg hrb hri hp hvb hvi
        (hev ▸ hsok)).conseq fun s' hm _ => ?_
      rw [hev] at hm; exact ⟨hm, scrOk_nil _ _ _⟩

theorem lowerOpScr_ok {G : VCtx} {nv k : Nat} {st : SymState T.toIsa} {vh : VariantHint}
    {s : T.mach.MData} {σ : List (BitVec 64)} {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg T.Reg T.VReg T.Cond) sig} {dsts : Tup (PDst T.Reg T.VReg T.Cond) rs}
    {vs : Tup Val sig} {P : Tup Val rs → Prop}
    {c : List T.Directive} {clob : FlagMask} {scrOut : List (T.Reg × BitVec 64)}
    (hA : Agree T G nv st s σ)
    (hpg : ∀ r ∈ tupArgGprs pas, r ∉ T.frame.scratch)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hph : TRel (T.mach.PArgHolds s) pas vs) (hwp : code.wp vs P)
    (hl : lowerOpScr T.toIsa st vh code pas dsts = some (c, clob, scrOut)) :
    T.mach.FallsTo T.gpr.condReads host k c (tupDstGprs dsts ++ T.frame.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
          (∀ {t0} {ht : rs = [t0]} {rd}, dsts = ht ▸ (.gpr rd, ()) →
            T.gpr.zeroExtOp code pas dsts = true →
            (∀ {h1 : rs = [.bool]}, dsts = h1 ▸ (.gpr rd, ()) →
              T.gpr.boolFlagOut? (h1 ▸ code) pas (.gpr rd) = none) →
            (∀ {w} {h1 : rs = [.bits w]}, Nat.ble w 64 = true →
              T.gpr.aluZeroOut? w (h1 ▸ code) (.gpr rd) = none) →
            (T.gpr.opScr?.isSome = true ∨
              ∀ {co w pa pb pd} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]},
                code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl) →
                pas = h1 ▸ (pa, pb, ()) → dsts = h2 ▸ (pd, ()) →
                (T.gpr.cmpFlagsOut? co w pa pb pd).isNone = true) →
            AbiGprHolds (T.mach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
          (∀ {rd} {h1 : rs = [.bits 32]}, dsts = h1 ▸ (.gpr rd, ()) →
            T.gpr.zeroUpper32Op code pas dsts = true →
            (usePlainOp T.toIsa code pas dsts ||
              T.gpr.opScr?.isNone || T.gpr.zeroExtOp code pas dsts) = true →
            T.mach.getGpr s' rd = (h1 ▸ rvs).1.setWidth 64) ∧
          (∀ {co w pa pb pd lf} {h1 : sig = [.bits w, .bits w]} {h2 : rs = [.bool]}
              {_he : code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl)},
            pas = h1 ▸ (pa, pb, ()) → dsts = h2 ▸ (pd, ()) →
            T.gpr.cmpFlagsOut? co w pa pb pd = some lf →
            FlagCmpOk T.mach T.gpr s'
              (if lf then (h1 ▸ vs).1 else (h1 ▸ vs).2.1)
              (if lf then (h1 ▸ vs).2.1 else (h1 ▸ vs).1) false) ∧
          (∀ {rd cc} {h1 : rs = [.bool]}, dsts = h1 ▸ (.gpr rd, ()) →
            isCmpOp (h1 ▸ code) = false →
            T.gpr.boolFlagOut? (h1 ▸ code) pas (.gpr rd) = some cc →
            T.mach.evalCond s' cc = (h1 ▸ rvs).1) ∧
          (∀ {w pd eqNe} {h1 : rs = [.bits w]}, Nat.ble w 64 = true → clob ≠ FlagMask.none →
            dsts = h1 ▸ (pd, ()) → T.gpr.aluZeroOut? w (h1 ▸ code) pd = some eqNe →
            FlagCmpOk T.mach T.gpr s' (h1 ▸ rvs).1 0#w eqNe)) ∧
        T.mach.mem s' = T.mach.mem s ∧ ScrOk T.mach T.frame.scratch scrOut s') post := by
  unfold lowerOpScr at hl
  by_cases hup : usePlainOp T.toIsa code pas dsts = true
  · simp only [hup, ↓reduceIte] at hl
    obtain ⟨⟨c', cl'⟩, hop, heq⟩ := Option.map_eq_some_iff.mp hl
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    cases rs with
    | nil => simp [usePlainOp] at hup
    | cons r0 rs0 =>
      cases rs0 with
      | cons _ _ => simp [usePlainOp] at hup
      | nil =>
        cases r0 with
        | float _ | pair _ _ => simp [usePlainOp] at hup
        | bool =>
          rcases dsts with ⟨pd, ⟨⟩⟩
          cases pd with
          | flag _ | vec _ => simp [usePlainOp] at hup
          | gpr rd =>
            have hbf? : (T.gpr.boolFlagOut? code pas (.gpr rd)).isSome = true := by
              dsimp only [usePlainOp] at hup
              exact ((Bool.and_eq_true _ _).mp hup).2
            obtain ⟨cc, hbf⟩ := Option.isSome_iff_exists.mp hbf?
            refine (T.gprSpec.op_boolFlag_spec hbf hop hpg hdg hph hwp).conseq
              fun s' ⟨⟨b, hP, hpd, hev⟩, hm⟩ _ => ?_
            refine ⟨⟨(b, ()), hP, .cons hpd .nil,
              (fun {t0 ht rd'} hdr' _ hnobf _ _ => by
                obtain rfl : Ty.bool = t0 := (List.cons.inj ht).1
                cases ht; cases hdr'
                have hn := hnobf (h1 := rfl) rfl; rw [hbf] at hn; cases hn),
              (fun {_ h1} => by cases h1),
              (fun {co w _ _ _ _} {h1 h2 he} => by
                cases h1; cases h2; cases he; simp [usePlainOp, isCmpOp] at hup),
              (fun {rd' cc' h1} hrd' _ hbf' => by
                cases h1; cases hrd'; rw [hbf] at hbf'; cases hbf'; exact hev),
              (fun {_ _ _ h1} => by cases h1)⟩, hm, scrOk_nil _ _ _⟩
        | bits w =>
          rcases dsts with ⟨pd, ⟨⟩⟩
          dsimp only [usePlainOp] at hup
          simp only [Bool.and_eq_true] at hup
          obtain ⟨eqNe, halu⟩ := Option.isSome_iff_exists.mp hup.2
          have hdg1 : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch :=
            fun r hr => hdg r (by simpa [tupDstGprs] using hr)
          by_cases hcl : cl' = FlagMask.none
          · by_cases hzu32 : w = 32 ∧ ∃ rd, pd = .gpr rd ∧
                T.gpr.zeroUpper32Op code pas (.gpr rd, ()) = true
            · obtain ⟨rfl, rd, rfl, hzu⟩ := hzu32
              refine (T.gprSpec.op_zero32 hzu hop rfl hpg (hdg rd (by simp [tupDstGprs]))
                hph hwp).conseq
                fun s' ⟨⟨rv, hP, h32⟩, hm⟩ _ => ?_
              have hgp : GprHolds (T.mach.getGpr s' rd) (.bits 32) rv :=
                ⟨by decide, by rw [h32, BitVec.setWidth_setWidth_of_le _ (by decide),
                  BitVec.setWidth_eq]⟩
              refine ⟨⟨(rv, ()), hP, .cons hgp .nil, ?_, ?_, ?_, ?_, ?_⟩, hm, scrOk_nil _ _ _⟩
              · intro _ ht rd' hdr' _ _ hnoalu _
                cases ht; cases hdr'; have hn := hnoalu (h1 := rfl) hup.1; rw [halu] at hn; cases hn
              · intro rd' h1 hdr' _ _; cases h1; cases hdr'; exact h32
              · rintro _ _ _ _ _ _ _ ⟨⟩
              · intro _ _ h1; cases h1
              · intro _ _ _ _ _ hne; exact absurd hcl hne
            · refine (T.gprSpec.op_spec hop hpg hdg hph hwp).conseq
                fun s' ⟨⟨rvs, hP, htr⟩, hm⟩ _ => ?_
              refine ⟨⟨rvs, hP, htr, ?_, ?_, ?_, ?_, ?_⟩, hm, scrOk_nil _ _ _⟩
              · intro _ ht rd' hdr' _ _ hnoalu _
                cases ht; cases hdr'; have hn := hnoalu (h1 := rfl) hup.1; rw [halu] at hn; cases hn
              · intro rd h1 hdr hzu _; cases h1; cases hdr; exact absurd ⟨rfl, rd, rfl, hzu⟩ hzu32
              · rintro _ _ _ _ _ _ _ ⟨⟩
              · intro _ _ h1; cases h1
              · intro _ _ _ _ _ hne; exact absurd hcl hne
          · have htd : tupDstGprs (ts := [.bits w]) (pd, ()) = pd.gprs := by simp [tupDstGprs]
            rw [htd]
            refine (T.gprSpec.op_aluZero_spec halu hcl hop hpg hdg1 hph hwp).conseq
              fun s' ⟨⟨rv, hP, hpd, h32, hfl⟩, hm⟩ _ => ?_
            refine ⟨⟨(rv, ()), hP, .cons hpd .nil, ?_, ?_, ?_, ?_, ?_⟩, hm, scrOk_nil _ _ _⟩
            · intro _ ht rd' hdr' _ _ hnoalu _
              cases ht; cases hdr'; have hn := hnoalu (h1 := rfl) hup.1; rw [halu] at hn; cases hn
            · intro rd h1 hdr hzu _; cases h1; cases hdr; exact h32 rd rfl rfl hzu
            · rintro _ _ _ _ _ _ _ ⟨⟩
            · intro _ _ h1; cases h1
            · intro w' pd' eqNe' h1 _ _ hpd' halu'
              cases h1; cases hpd'; rw [halu] at halu'; cases halu'; exact hfl
  · have hupF : usePlainOp T.toIsa code pas dsts = false := Bool.eq_false_iff.mpr hup
    simp only [hupF, Bool.false_eq_true, ↓reduceIte] at hl
    have hnoBf : ∀ {rd} {h1 : rs = [.bool]}, dsts = h1 ▸ (.gpr rd, ()) →
        isCmpOp (h1 ▸ code) = false →
        T.gpr.boolFlagOut? (h1 ▸ code) pas (.gpr rd) = none := by
      rintro rd rfl rfl hnc
      exact Option.eq_none_iff_forall_ne_some.mpr fun c hc =>
        hup (by simp [usePlainOp, hnc, hc])
    have hnoAlu : ∀ {w pd} {h1 : rs = [.bits w]}, Nat.ble w 64 = true →
        dsts = h1 ▸ (pd, ()) →
        T.gpr.aluZeroOut? w (h1 ▸ code) pd = none := by
      rintro w pd rfl hw rfl
      exact Option.eq_none_iff_forall_ne_some.mpr fun e he =>
        hup (by simp [usePlainOp, hw, he])
    cases hfn : T.gpr.opScr? with
    | some fn =>
      rw [hfn] at hl; dsimp only at hl
      refine (T.gprSpec.opScr_spec hfn hl hpg hdg hA.scrConsts_ok hph hwp).conseq
        fun s' ⟨⟨rvs, hp, htr, hz, hfc⟩, hm, hs⟩ _ => ?_
      refine ⟨⟨rvs, hp, htr, ?_, ?_, ?_, ?_, ?_⟩, hm, hs⟩
      · intro _ ht rd hdr hzb _ _ _; exact hz hdr hzb
      · intro rd h1 hdr _ hok
        cases h1; cases hdr
        simp only [hupF, Option.isNone_some, Bool.false_or] at hok
        exact (hz (ht := rfl) rfl hok).2
      · intro co w pa pb pd lf h1 h2 _he hpas hdsts hcmo
        exact @hfc co w pa pb pd lf h1 h2 _he hpas hdsts hcmo
      · intro rd cc h1 hdr hnc hc
        cases h1; cases hdr; have hn := hnoBf (h1 := rfl) rfl hnc; rw [hn] at hc; cases hc
      · intro w pd eqNe h1 hw _ hdr hc
        cases h1; cases hdr; have hn := hnoAlu (h1 := rfl) hw rfl; rw [hn] at hc; cases hc
    | none =>
      rw [hfn] at hl; dsimp only at hl
      obtain ⟨p, hop, heq⟩ := Option.map_eq_some_iff.mp hl
      rcases p with ⟨c', cl'⟩
      simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨rfl, rfl, rfl⟩
      by_cases hcmp : ∃ (co : CmpOp) (w : Nat) (pa pb : PArg T.Reg T.VReg T.Cond (.bits w))
            (pd : PDst T.Reg T.VReg T.Cond .bool) (lf : Bool)
            (h1 : sig = [.bits w, .bits w]) (h2 : rs = [.bool]),
            code = h1 ▸ h2 ▸ (.cmp co (.bits w) .bool rfl) ∧
            pas = h1 ▸ (pa, pb, ()) ∧ dsts = h2 ▸ (pd, ()) ∧
            T.gpr.cmpFlagsOut? co w pa pb pd = some lf
      · rcases hcmp with ⟨co, w, pa, pb, pd, lf, rfl, rfl, rfl, rfl, rfl, hcmo⟩
        have hP : P (co.evalBits (vs.1) (vs.2.1), ()) := by
          simpa [OpCode.wp_cmp, liftCmp] using hwp
        have hpg1 : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ T.frame.scratch := fun r hr =>
          hpg r ((List.mem_append.mp hr).elim (fun h => List.mem_append_left _ h)
            fun h => List.mem_append_right _ (by simpa [tupArgGprs] using h))
        have hdg1 : ∀ r ∈ pd.gprs, r ∉ T.frame.scratch := fun r hr =>
          hdg r (by simpa [tupDstGprs] using hr)
        rcases hph with _ | ⟨hpa, _ | ⟨hpb, -⟩⟩
        have htd : tupDstGprs (ts := [.bool]) (pd, ()) = pd.gprs := by simp [tupDstGprs]
        rw [htd]
        refine (T.gprSpec.op_cmpFlags_spec hcmo hop hpg1 hdg1 hpa hpb).conseq
          fun s' ⟨hd, hfl, hm⟩ _ => ?_
        refine ⟨⟨_, hP, .cons hd .nil, ?_, ?_, ?_, ?_, ?_⟩, hm, scrOk_nil _ _ _⟩
        · intro t0 ht rd _ _ _ _ hscr
          cases ht; rcases hscr with hscr | hscr
          · simp at hscr
          · have hc := hscr (co := co) (w := w) (pa := pa) (pb := pb) (pd := pd)
              (h1 := rfl) (h2 := rfl) rfl rfl rfl
            simp [hcmo] at hc
        · intro _ h1; cases h1
        · intro co' w' pa' pb' pd' lf' h1' h2' he' hpas' hdsts' hcmo'
          cases h1'; cases h2'; cases he'; cases hpas'; cases hdsts'
          rw [hcmo] at hcmo'; cases hcmo'; exact hfl
        · intro rd cc h1 hdr hnc hc; cases h1; cases hnc
        · intro w' pd' eqNe h1; cases h1
      · by_cases hz : ∃ t0, ∃ ht : rs = [t0], ∃ rd, dsts = ht ▸ (.gpr rd, ()) ∧
            T.gpr.zeroExtOp code pas dsts = true
        · rcases hz with ⟨t0, ht, rd, rfl, hz0⟩; subst ht
          have hrd : rd ∉ T.frame.scratch := hdg rd (by simp [tupDstGprs])
          refine (T.gprSpec.op_zext hz0 hop hpg hrd hph hwp).conseq
            fun s' ⟨⟨rv, hp, hab⟩, hm⟩ _ => ?_
          have htr : TRel (as := [t0]) (T.mach.PDstHolds s') (.gpr rd, ()) (rv, ()) :=
            .cons hab.toGprHolds .nil
          refine ⟨⟨(rv, ()), hp, htr, ?_, ?_, ?_, ?_, ?_⟩, hm, scrOk_nil _ _ _⟩
          · intro t0' ht' rd' hrd' _ _ _ _
            obtain rfl : t0 = t0' := (List.cons.inj ht').1; cases hrd'; exact hab
          · intro rd' h1 hdr' _ _
            obtain rfl : t0 = .bits 32 := (List.cons.inj h1).1; cases hdr'; exact hab.2
          · intro co w pa pb pd lf h1 h2 _he hpas' hdsts' hcmo'
            exact absurd ⟨co, w, pa, pb, pd, lf, h1, h2, _he, hpas', hdsts', hcmo'⟩ hcmp
          · intro rd' cc h1 hdr hnc hc
            cases h1; cases hdr; have hn := hnoBf (h1 := rfl) rfl hnc; rw [hn] at hc; cases hc
          · intro w' pd' eqNe h1 hw _ hdr hc
            cases h1; cases hdr; have hn := hnoAlu (h1 := rfl) hw rfl; rw [hn] at hc; cases hc
        · by_cases hz32 : ∃ (h1 : rs = [.bits 32]) (rd : T.Reg),
              dsts = h1 ▸ (.gpr rd, ()) ∧ T.gpr.zeroUpper32Op code pas dsts = true
          · rcases hz32 with ⟨rfl, rd, rfl, hzu⟩
            have hrd : rd ∉ T.frame.scratch := hdg rd (by simp [tupDstGprs])
            refine (T.gprSpec.op_zero32 hzu hop rfl hpg hrd hph hwp).conseq
              fun s' ⟨⟨rv, hp, h32⟩, hm⟩ _ => ?_
            have hgp : GprHolds (T.mach.getGpr s' rd) (.bits 32) rv :=
              ⟨by decide, by rw [h32, BitVec.setWidth_setWidth_of_le _ (by decide),
                BitVec.setWidth_eq]⟩
            refine ⟨⟨(rv, ()), hp, .cons hgp .nil, ?_, ?_, ?_, ?_, ?_⟩, hm, scrOk_nil _ _ _⟩
            · intro t0 ht rd' hdr' hzb _ _ _; exact absurd ⟨t0, ht, rd', hdr', hzb⟩ hz
            · intro rd' h1 hdr' _ _; cases h1; cases hdr'; exact h32
            · intro co w pa pb pd lf h1 h2 he hpas' hdsts' hcmo'
              exact absurd ⟨co, w, pa, pb, pd, lf, h1, h2, he, hpas', hdsts', hcmo'⟩ hcmp
            · intro rd' cc h1 hdr hnc hc; cases h1
            · intro w pd eqNe h1 hw _ hdr hc
              cases h1; cases hdr; have hn := hnoAlu (h1 := rfl) hw rfl; rw [hn] at hc; cases hc
          · refine (T.gprSpec.op_spec hop hpg hdg hph hwp).conseq
              fun s' ⟨⟨rvs, hp, htr⟩, hm⟩ _ => ?_
            refine ⟨⟨rvs, hp, htr, ?_, ?_, ?_, ?_, ?_⟩, hm, scrOk_nil _ _ _⟩
            · intro t0 ht rd hdr' hzb _ _ _; exact absurd ⟨t0, ht, rd, hdr', hzb⟩ hz
            · intro rd h1 hdr hzu _; exact absurd ⟨h1, rd, hdr, hzu⟩ hz32
            · intro co w pa pb pd lf h1 h2 he hpas' hdsts' hcmo'
              exact absurd ⟨co, w, pa, pb, pd, lf, h1, h2, he, hpas', hdsts', hcmo'⟩ hcmp
            · intro rd cc h1 hdr hnc hc
              cases h1; cases hdr; have hn := hnoBf (h1 := rfl) rfl hnc; rw [hn] at hc; cases hc
            · intro w pd eqNe h1 hw _ hdr hc
              cases h1; cases hdr; have hn := hnoAlu (h1 := rfl) hw rfl; rw [hn] at hc; cases hc

/-! ## `elideRegOp?_ok`, `tryLoadTrunc_ok`, `tryMulHi_ok` (`OPT-10b` / `OPT-10c`) -/

theorem hasVarGprW_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {x : Nat} {rd : T.Reg}
    (h : hasVarGprW T.toIsa st.regs x rd = true) :
    GprSym G (T.mach.getGpr s rd) (.var x) := by
  simp only [hasVarGprW, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨sa', rl'⟩, hmem, he1, he2⟩ := h
  obtain rfl := symArgEq_iff.mp he1
  have h0 := hA.regs _ hmem
  cases rl' with
  | gpr r' => simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0
  | gprZ r' => simp only [regLocMatchesGpr, beq_iff_eq] at he2; subst he2; exact h0.1
  | _ => simp [regLocMatchesGpr] at he2

theorem holdsVarGprZ_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {x : Nat} {rd : T.Reg}
    (h : holdsVarGprZ T.toIsa st.regs x rd = true) :
    GprSym G (T.mach.getGpr s rd) (.var x) ∧ SymZ G (T.mach.getGpr s rd) (.var x) := by
  simp only [holdsVarGprZ, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨sa', rl'⟩, hmem, he1, he2⟩ := h
  obtain rfl := symArgEq_eq he1
  obtain rfl := regLocEq_eq he2
  exact hA.regs _ hmem

theorem setWidth_widen_64 {w l : Nat} (x : BitVec w) (h : w ≤ l) :
    (x.setWidth l).setWidth 64 = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp only [BitVec.getLsbD_setWidth]
  by_cases hjw : j < w
  · simp [hjw, show j < l by omega]
  · simp [BitVec.getLsbD_of_ge x j (by omega)]

theorem elideRegOp?_ok {zl : Bool} {G : VCtx} {nv : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64} {ts sig : List Ty}
    {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {rd : T.Reg} {isZ addZ32 : Bool} {goal : Prop}
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hargs : TRel (ArgRel G) args₁ args) (hwp : code.wp (vals args₁) P)
    (hel : elideRegOp? T.toIsa st code args dsts = some (rd, isZ, addZ32))
    (kont : ∀ (rvs : Tup Val ts), P rvs →
      Agree T (Tup.zip rvs (Tup.levels ts nv) ++ G) (nv + ts.length)
        { st with
          regs := match ts with
            | [_] => (.var nv, if isZ then RegLoc.gprZ rd else .gpr rd) :: st.regs
            | _ => st.regs
          defs := match recordDefC T.toIsa.gpr.addrCse st.defs code args with
            | some df => st.defs.insert nv df | none => st.defs
          zeroExt32 := if addZ32 && !st.zeroExt32.contains rd then rd :: st.zeroExt32
                       else st.zeroExt32 } s σ →
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st.memDefs →
      Inv T hints s₀ ra n Rf m s σ zl →
      goal) :
    goal := by
  let G' : Tup Val ts → VCtx := fun rvs => Tup.zip rvs (Tup.levels ts nv) ++ G
  have hMgrow : ∀ rvs : Tup Val ts,
      MemDefsOk (G' rvs) m (nv + ts.length) st.memDefs := fun rvs =>
    hM.grow (Nat.le_add_right _ _)
      (fun p hp => (zip_levels_mem hp).imp id (·.1))
      (fun _ h => List.mem_append_right _ h)
  have hwp' : code.wp (vals args₁) (fun rvs => P rvs ∧
      ∀ df, recordDefC T.toIsa.gpr.addrCse st.defs code args = some df →
        0 < ts.length ∧ DefOk (G' rvs) nv df) := by
    cases hd : recordDefC T.toIsa.gpr.addrCse st.defs code args with
    | none => exact OpCode.wp_mono code _ (fun r hp => ⟨hp, by simp⟩) hwp
    | some df =>
      exact OpCode.wp_mono code _ (fun r hp => ⟨hp.1, fun df' he => by cases he; exact hp.2⟩)
        (wp_recordDefC hA.defs hargs hA.ctx_lt hwp hd)
  have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
    Option.eq_none_iff_forall_ne_some.mpr fun w h => absurd (hA.vw_lt _ _ h) (Nat.not_lt.mpr hx)
  have finish1 : ∀ {t0 : Ty} (ht : ts = [t0]) (rv : Val t0)
      (hnp : ∀ a b, t0 ≠ .pair a b) (hP : P (ht ▸ (rv, ())))
      (hdef : ∀ df, recordDefC T.toIsa.gpr.addrCse st.defs code args = some df →
        0 < 1 ∧ DefOk (G' (ht ▸ (rv, ()))) nv df)
      (hreg : RegLocOk T.mach (G' (ht ▸ (rv, ()))) s (.var nv)
        (if isZ then RegLoc.gprZ rd else .gpr rd))
      (hz32 : addZ32 = true → T.mach.getGpr s rd = ((T.mach.getGpr s rd).setWidth 32).setWidth 64),
      goal := by
    intro t0 ht rv hnp hP hdef hreg hz32
    subst ht
    have hA0 : Agree T (⟨t0, rv, nv⟩ :: G) (nv + 1) st s σ :=
      hA.extend (Nat.le_succ nv)
        (fun p hp => (List.mem_cons.mp hp).elim (fun h => Or.inr (h ▸ Nat.le_refl _)) Or.inl)
        (fun p hp => (List.mem_cons.mp hp).elim (fun h => h ▸ Nat.lt_succ_self _)
          fun h => Nat.lt_succ_of_lt (hA.ctx_lt p h))
        (fun _ h => List.mem_cons_of_mem _ h) (ctx_uniq_cons hA.ctx_lt hA.ctx_uniq)
        (fun _ _ => rfl) (fun x w hx hle => absurd (hnone x hle) (by simp [hx]))
        (fun p hp hle _ => by
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hnp
          · exact absurd (hA.ctx_lt p hp) (Nat.not_lt.mpr hle))
    have hd1 : ∀ y d, Trie.find? (match recordDefC T.toIsa.gpr.addrCse st.defs code args with
        | some df => st.defs.insert nv df | none => st.defs) y = some d →
        DefOk (G' (rv, ())) y d ∧ y < nv + 1 := by
      intro y d hy; split at hy
      · rw [Trie.find?_insert] at hy; split at hy
        · cases hy; subst_vars; exact ⟨(hdef _ ‹_›).2, Nat.lt_succ_self _⟩
        · exact ⟨hA0.defs y d hy, hA0.defs_lt y d hy⟩
      · exact ⟨hA0.defs y d hy, hA0.defs_lt y d hy⟩
    have hzk : ∀ r ∈ (if addZ32 && !st.zeroExt32.contains rd then rd :: st.zeroExt32
        else st.zeroExt32), T.mach.getGpr s r = ((T.mach.getGpr s r).setWidth 32).setWidth 64 := by
      intro r hr; split at hr
      · next ha =>
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact hz32 ((Bool.and_eq_true _ _).mp ha).1
        · exact hA0.zeroExt32_ok r hr'
      · exact hA0.zeroExt32_ok r hr
    refine kont (rv, ()) hP ?_ (hMgrow _) hI
    exact { hA0 with
      regs := fun p hp => (List.mem_cons.mp hp).elim (fun h => h ▸ hreg) (hA0.regs p)
      regs_lt := fun p hp => (List.mem_cons.mp hp).elim (fun h => h ▸ by simp [symArgScopeOk])
        (hA0.regs_lt p)
      defs := fun y d hy => (hd1 y d hy).1
      defs_lt := fun y d hy => (hd1 y d hy).2
      zeroExt32_ok := hzk }
  cases code with
  | zext m0 n0 =>
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
    cases a with
    | imm _ => simp [elideRegOp?] at hel
    | var x =>
      cases d0 with
      | vec _ => simp [elideRegOp?] at hel
      | gpr rd0 =>
        dsimp only [elideRegOp?] at hel; split at hel
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hel
          rcases hel with ⟨rfl, rfl, rfl⟩
          simp only [Bool.and_eq_true, Nat.ble_eq, Bool.or_eq_true, Nat.beq_eq] at hc
          obtain ⟨⟨hn, _⟩, hsrc⟩ := hc
          rcases args₁ with ⟨a₁, ⟨⟩⟩; cases hargs with | cons ha₁ _ =>
          cases ha₁ with | var hmG =>
          rename_i vx
          simp only [OpCode.wp, vals, Arg.val] at hwp'
          obtain ⟨hmn, hP, hdef⟩ := hwp'
          have hw : T.mach.getGpr s rd0 = (vx.setWidth n0).setWidth 64 := by
            rcases hsrc with hgz | ⟨⟨rfl, hzer⟩, hhas⟩
            · have hz := (holdsVarGprZ_ok hA hgz).2 _ vx hmG
              rw [hz.2, setWidth_widen_64 vx hmn]
            · have hgs := (hasVarGprW_ok hA hhas) (.bits 32) vx hmG
              have hzk := hA.zeroExt32_ok rd0 (List.contains_iff_mem.mp hzer)
              rw [hzk, hgs.2, ← setWidth_widen_64 vx hmn]
          refine finish1 rfl (vx.setWidth n0) (fun _ _ h => by cases h) hP hdef ?_ ?_
          · exact ⟨fun t' v' hm' => by
              cases mem_cons_top hA.ctx_lt hm'
              exact ⟨hn, by rw [hw, BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq]⟩,
              fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hw⟩⟩
          · intro h32
            obtain rfl : n0 = 32 := Nat.beq_eq.mp h32
            rw [hw, setWidth_32_64_val]
        · simp at hel
  | trunc m0 n0 =>
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
    cases a with
    | imm _ => simp [elideRegOp?] at hel
    | var x =>
      cases d0 with
      | vec _ => simp [elideRegOp?] at hel
      | gpr rd0 =>
        dsimp only [elideRegOp?] at hel; split at hel; · simp at hel
        rename_i hc
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Nat.ble_eq] at hc
        obtain ⟨⟨hnm, hn⟩, hhas⟩ := hc
        rcases args₁ with ⟨a₁, ⟨⟩⟩; cases hargs with | cons ha₁ _ =>
        cases ha₁ with | var hmG =>
        rename_i vx
        simp only [OpCode.wp, vals, Arg.val] at hwp'
        obtain ⟨-, hP, hdef⟩ := hwp'
        have hgs := (hasVarGprW_ok hA hhas) (.bits m0) vx hmG
        have hw : (T.mach.getGpr s rd0).setWidth n0 = vx.setWidth n0 := by
          rw [← BitVec.setWidth_setWidth_of_le (T.mach.getGpr s rd0) hnm, hgs.2]
        have hzkCase : n0 = 32 → st.zeroExt32.contains rd0 = true →
            T.mach.getGpr s rd0 = ((vx.setWidth 32).setWidth 64) := by
          rintro rfl hzer
          have hzk := hA.zeroExt32_ok rd0 (List.contains_iff_mem.mp hzer)
          rw [hzk, ← BitVec.setWidth_setWidth_of_le (T.mach.getGpr s rd0) hnm, hgs.2]
        split at hel
        · split at hel
          · rename_i hzer
            simp only [Option.some.injEq, Prod.mk.injEq] at hel
            rcases hel with ⟨rfl, rfl, rfl⟩
            have h32 : n0 = 32 := by
              have : _ := ‹(T.toIsa.gpr.elideZext32 && Nat.beq n0 32 && _) = true›
              simp only [Bool.and_eq_true, Nat.beq_eq] at this; exact this.1.2
            subst h32
            have hab : T.mach.getGpr s rd0 = (vx.setWidth 32).setWidth 64 := hzkCase rfl hzer
            refine finish1 rfl (vx.setWidth 32) (fun _ _ h => by cases h) hP hdef ?_ ?_
            · exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hw⟩,
                fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hab⟩⟩
            · intro _; exact hA.zeroExt32_ok rd0 (List.contains_iff_mem.mp hzer)
          · simp at hel
        · simp only [Option.some.injEq, Prod.mk.injEq] at hel
          rcases hel with ⟨rfl, rfl, rfl⟩
          by_cases hz : (Nat.beq n0 32 && st.zeroExt32.contains rd0) = true
          · simp only [Bool.and_eq_true, Nat.beq_eq] at hz
            obtain ⟨rfl, hzer⟩ := hz
            have hab : T.mach.getGpr s rd0 = (vx.setWidth 32).setWidth 64 := hzkCase rfl hzer
            refine finish1 rfl (vx.setWidth 32) (fun _ _ h => by cases h) hP hdef ?_ ?_
            · simp only [hzer]
              exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hw⟩,
                fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hab⟩⟩
            · intro _; exact hA.zeroExt32_ok rd0 (List.contains_iff_mem.mp hzer)
          · have hzf : (Nat.beq n0 32 && st.zeroExt32.contains rd0) = false :=
              Bool.eq_false_iff.mpr hz
            refine finish1 rfl (vx.setWidth n0) (fun _ _ h => by cases h) hP hdef ?_
              (fun h => absurd h hz)
            simp only [hzf]
            exact fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hw⟩
  | ofBool n0 =>
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
    cases a with
    | imm _ => simp [elideRegOp?] at hel
    | var x =>
      cases d0 with
      | vec _ => simp [elideRegOp?] at hel
      | gpr rd0 =>
        dsimp only [elideRegOp?] at hel; split at hel
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hel
          rcases hel with ⟨rfl, rfl, rfl⟩
          simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
          rcases args₁ with ⟨a₁, ⟨⟩⟩; cases hargs with | cons ha₁ _ =>
          cases ha₁ with | var hmG =>
          rename_i b
          simp only [OpCode.wp, vals, Arg.val] at hwp'
          obtain ⟨hP, hdef⟩ := hwp'
          have hzb := (holdsVarGprZ_ok hA hc.2).2 .bool b hmG
          have hw : T.mach.getGpr s rd0 = (BitVec.ofNat n0 b.toNat).setWidth 64 := by
            rw [hzb]; cases b
            · simp
            · have hpow : (1 : Nat) < 2 ^ n0 :=
                Nat.lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide) hc.1.1)
              apply BitVec.eq_of_toNat_eq
              simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hpow]
          refine finish1 rfl (BitVec.ofNat n0 b.toNat) (fun _ _ h => by cases h) hP hdef ?_ ?_
          · exact ⟨fun t' v' hm' => by
              cases mem_cons_top hA.ctx_lt hm'
              exact ⟨hc.1.2,
                by rw [hw, BitVec.setWidth_setWidth_of_le _ hc.1.2, BitVec.setWidth_eq]⟩,
              fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hc.1.2, hw⟩⟩
          · intro h32
            obtain rfl : n0 = 32 := Nat.beq_eq.mp h32
            rw [hw, setWidth_32_64_val]
        · simp at hel
  | copy t0 =>
    cases t0 with
    | float _ | pair _ _ => simp [elideRegOp?] at hel
    | bits n0 =>
      rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
      cases a with
      | imm _ => simp [elideRegOp?] at hel
      | var x =>
        cases d0 with
        | vec _ => simp [elideRegOp?] at hel
        | gpr rd0 =>
          dsimp only [elideRegOp?] at hel; split at hel; · simp at hel
          rename_i hn
          replace hn : n0 ≤ 64 := by simpa [Nat.ble_eq] using hn
          rcases args₁ with ⟨a₁, ⟨⟩⟩; cases hargs with | cons ha₁ _ =>
          cases ha₁ with | var hmG =>
          rename_i vx
          simp only [OpCode.wp, vals, Arg.val] at hwp'
          obtain ⟨hP, hdef⟩ := hwp'
          split at hel
          · rename_i hgz
            simp only [Option.some.injEq, Prod.mk.injEq] at hel
            rcases hel with ⟨rfl, rfl, rfl⟩
            have hzv := (holdsVarGprZ_ok hA hgz).2 (.bits n0) vx hmG
            refine finish1 rfl vx (fun _ _ h => by cases h) hP hdef ?_ ?_
            · exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hzv.toGprHolds,
                fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hzv⟩
            · intro h32
              obtain rfl : n0 = 32 := Nat.beq_eq.mp h32
              rw [hzv.2, setWidth_32_64_val]
          split at hel; · simp at hel
          rename_i hhas
          replace hhas : hasVarGprW T.toIsa st.regs x rd0 = true := by simpa using hhas
          have hgs := (hasVarGprW_ok hA hhas) (.bits n0) vx hmG
          split at hel
          · split at hel
            · rename_i hzer
              simp only [Option.some.injEq, Prod.mk.injEq] at hel
              rcases hel with ⟨rfl, rfl, rfl⟩
              have h32 : n0 = 32 := by
                have : _ := ‹(T.toIsa.gpr.elideZext32 && Nat.beq n0 32 && _) = true›
                simp only [Bool.and_eq_true, Nat.beq_eq] at this; exact this.1.2
              subst h32
              have hzk := hA.zeroExt32_ok rd0 (List.contains_iff_mem.mp hzer)
              have hab : T.mach.getGpr s rd0 = vx.setWidth 64 := by
                rw [hzk, hgs.2]
              refine finish1 rfl vx (fun _ _ h => by cases h) hP hdef ?_ (fun _ => hzk)
              exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hgs,
                fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hab⟩⟩
            · simp at hel
          · simp only [Option.some.injEq, Prod.mk.injEq] at hel
            rcases hel with ⟨rfl, rfl, rfl⟩
            by_cases hz : (Nat.beq n0 32 && st.zeroExt32.contains rd0) = true
            · simp only [Bool.and_eq_true, Nat.beq_eq] at hz
              obtain ⟨rfl, hzer⟩ := hz
              have hzk := hA.zeroExt32_ok rd0 (List.contains_iff_mem.mp hzer)
              have hab : T.mach.getGpr s rd0 = vx.setWidth 64 := by rw [hzk, hgs.2]
              refine finish1 rfl vx (fun _ _ h => by cases h) hP hdef ?_ (fun _ => hzk)
              simp only [hzer]
              exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hgs,
                fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hab⟩⟩
            · have hzf : (Nat.beq n0 32 && st.zeroExt32.contains rd0) = false :=
                Bool.eq_false_iff.mpr hz
              refine finish1 rfl vx (fun _ _ h => by cases h) hP hdef ?_
                (fun h => absurd h hz)
              simp only [hzf]
              exact fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hgs
    | bool =>
      rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
      cases a with
      | imm _ => simp [elideRegOp?] at hel
      | var x =>
        cases d0 with
        | vec _ | flag _ => simp [elideRegOp?] at hel
        | gpr rd0 =>
          dsimp only [elideRegOp?] at hel
          rcases args₁ with ⟨a₁, ⟨⟩⟩; cases hargs with | cons ha₁ _ =>
          cases ha₁ with | var hmG =>
          rename_i b
          simp only [OpCode.wp, vals, Arg.val] at hwp'
          obtain ⟨hP, hdef⟩ := hwp'
          split at hel
          · rename_i hgz
            simp only [Option.some.injEq, Prod.mk.injEq] at hel
            rcases hel with ⟨rfl, rfl, rfl⟩
            have hzb := (holdsVarGprZ_ok hA hgz).2 .bool b hmG
            refine finish1 rfl b (fun _ _ h => by cases h) hP hdef ?_ (fun h => by cases h)
            exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hzb.toGprHolds,
              fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hzb⟩
          · split at hel
            · rename_i hc
              simp only [Bool.and_eq_true] at hc
              simp only [Option.some.injEq, Prod.mk.injEq] at hel
              rcases hel with ⟨rfl, rfl, rfl⟩
              have hgs := (hasVarGprW_ok hA hc.1) .bool b hmG
              refine finish1 rfl b (fun _ _ h => by cases h) hP hdef ?_ (fun h => by cases h)
              exact fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hgs
            · simp at hel
  | bitcast t0 u0 hsz =>
    cases t0 <;> cases u0 <;> try (simp [elideRegOp?] at hel; done)
    rename_i m0 n0
    rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
    cases a with
    | imm _ => simp [elideRegOp?] at hel
    | var x =>
      cases d0 with
      | vec _ => simp [elideRegOp?] at hel
      | gpr rd0 =>
        dsimp only [elideRegOp?] at hel; split at hel; · simp at hel
        rename_i hc
        simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Nat.beq_eq,
          Nat.ble_eq] at hc
        obtain ⟨rfl, hn⟩ := hc
        rcases args₁ with ⟨a₁, ⟨⟩⟩; cases hargs with | cons ha₁ _ =>
        cases ha₁ with | var hmG =>
        rename_i vx
        simp only [OpCode.wp, vals, Arg.val, toBits, ofBits, BitVec.cast_eq] at hwp'
        obtain ⟨hP, hdef⟩ := hwp'
        split at hel
        · rename_i hgz
          simp only [Option.some.injEq, Prod.mk.injEq] at hel
          rcases hel with ⟨rfl, rfl, rfl⟩
          have hzv := (holdsVarGprZ_ok hA hgz).2 (.bits m0) vx hmG
          refine finish1 rfl vx (fun _ _ h => by cases h) hP hdef ?_ ?_
          · exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hzv.toGprHolds,
              fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hzv⟩
          · intro h32
            obtain rfl : m0 = 32 := Nat.beq_eq.mp h32
            rw [hzv.2, setWidth_32_64_val]
        split at hel; · simp at hel
        rename_i hhas
        replace hhas : hasVarGprW T.toIsa st.regs x rd0 = true := by simpa using hhas
        have hgs := (hasVarGprW_ok hA hhas) (.bits m0) vx hmG
        split at hel
        · split at hel
          · rename_i hzer
            simp only [Option.some.injEq, Prod.mk.injEq] at hel
            rcases hel with ⟨rfl, rfl, rfl⟩
            have h32 : m0 = 32 := by
              have : _ := ‹(T.toIsa.gpr.elideZext32 && Nat.beq m0 32 && _) = true›
              simp only [Bool.and_eq_true, Nat.beq_eq] at this; exact this.1.2
            subst h32
            have hzk := hA.zeroExt32_ok rd0 (List.contains_iff_mem.mp hzer)
            have hab : T.mach.getGpr s rd0 = vx.setWidth 64 := by rw [hzk, hgs.2]
            refine finish1 rfl vx (fun _ _ h => by cases h) hP hdef ?_ (fun _ => hzk)
            exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hgs,
              fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hab⟩⟩
          · simp at hel
        · simp only [Option.some.injEq, Prod.mk.injEq] at hel
          rcases hel with ⟨rfl, rfl, rfl⟩
          by_cases hz : (Nat.beq m0 32 && st.zeroExt32.contains rd0) = true
          · simp only [Bool.and_eq_true, Nat.beq_eq] at hz
            obtain ⟨rfl, hzer⟩ := hz
            have hzk := hA.zeroExt32_ok rd0 (List.contains_iff_mem.mp hzer)
            have hab : T.mach.getGpr s rd0 = vx.setWidth 64 := by rw [hzk, hgs.2]
            refine finish1 rfl vx (fun _ _ h => by cases h) hP hdef ?_ (fun _ => hzk)
            simp only [hzer]
            exact ⟨fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hgs,
              fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact ⟨hn, hab⟩⟩
          · have hzf : (Nat.beq m0 32 && st.zeroExt32.contains rd0) = false :=
              Bool.eq_false_iff.mpr hz
            refine finish1 rfl vx (fun _ _ h => by cases h) hP hdef ?_
              (fun h => absurd h hz)
            simp only [hzf]
            exact fun t' v' hm' => by cases mem_cons_top hA.ctx_lt hm'; exact hgs
  | _ => simp [elideRegOp?] at hel

theorem tryLoadTrunc_ok {zl : Bool} {G : VCtx} {nv k : Nat} {vh : VariantHint}
    {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    {sig ts : List Ty} {code : OpCode sig ts} {args₁ : Tup (Arg Val) sig}
    {args : Tup (Arg VNat) sig} {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts}
    {P : Tup Val ts → Prop} {c : List T.Directive} {clob : FlagMask}
    {isZ z32 : Bool} {scrOut : List (T.Reg × BitVec 64)}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch) (hwp : code.wp (vals args₁) P)
    (h : tryLoadTrunc T.toIsa st vh code args dsts = some (c, clob, isZ, z32, scrOut)) :
    T.mach.FallsTo T.gpr.condReads host k c (tupDstGprs dsts ++ T.frame.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs ∧
          (isZ = true → ∃ (t0 : Ty) (ht : ts = [t0]) (rd : T.Reg),
            dsts = ht ▸ (.gpr rd, ()) ∧ AbiGprHolds (T.mach.getGpr s' rd) t0 (ht ▸ rvs).1) ∧
          (z32 = true → ∃ (ht : ts = [.bits 32]) (rd : T.Reg),
            dsts = ht ▸ (.gpr rd, ()) ∧ T.mach.getGpr s' rd = (ht ▸ rvs).1.setWidth 64)) ∧
        T.mach.mem s' = T.mach.mem s ∧ ScrOk T.mach T.frame.scratch scrOut s') post := by
  cases code <;> try (simp [tryLoadTrunc] at h; done)
  rename_i m0 n0
  rcases args with ⟨a, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
  cases a with
  | imm _ => simp [tryLoadTrunc] at h
  | var x =>
    cases d0 with
    | vec _ => simp [tryLoadTrunc] at h
    | gpr rd =>
      dsimp only [tryLoadTrunc] at h; split at h; · simp at h
      rename_i hc
      simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, Bool.or_eq_true,
        Nat.beq_eq, Nat.blt_eq] at hc
      obtain ⟨⟨⟨hm, hn⟩, hnm⟩, hgt⟩ := hc
      cases hmd : st.memDefs.find? x with
      | none => simp [hmd] at h
      | some p =>
        rcases p with ⟨tm, addr⟩
        cases tm with
        | bool | float _ | pair _ _ => simp [hmd] at h
        | bits m' =>
          simp only [hmd] at h
          split at h
          · rename_i hm'
            obtain rfl : m' = m0 := Nat.beq_eq.mp hm'
            obtain ⟨⟨c0, cl0, scr0⟩, hl, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he
            rcases he with ⟨rfl, rfl, rfl, rfl, rfl⟩
            rcases args₁ with ⟨a₁, ⟨⟩⟩; cases hargs with | cons ha₁ _ =>
            cases ha₁ with | var hmx =>
            rename_i vx
            obtain ⟨-, hlv0⟩ := hM x (.bits m') addr hmd
            obtain ⟨b₁, hb₁, hlv⟩ := hlv0 vx hmx
            have hlvS : loadVal (T.mach.mem s) (.bits n0) b₁.val = some (vx.setWidth n0) :=
              loadVal_bits_truncate (or_assoc.mp hm) (or_assoc.mp hn) hnm
                (loadVal_frame hI.2.2.2.1 hlv)
            have hrd : rd ∉ T.frame.scratch := hdg rd (by simp [tupDstGprs])
            simp only [OpCode.wp, vals, Arg.val] at hwp
            refine fun hinf kont =>
              (lowerLoadScr_ok hA hb₁ hrd hlvS hl) hinf fun s' ⟨hgr, hzu, hm0, hscr⟩ hfr =>
              kont s' ⟨⟨(vx.setWidth n0, ()), hwp.2, ?_, ?_, ?_⟩, hm0, hscr⟩
                (by simpa [tupDstGprs] using hfr)
            · by_cases hze : T.gpr.zeroExtLoad = true
              · simp only [hze, ↓reduceIte] at hgr; exact .cons hgr.toGprHolds .nil
              · have hzf : T.gpr.zeroExtLoad = false := Bool.eq_false_iff.mpr hze
                simp only [hzf, Bool.false_eq_true, ↓reduceIte] at hgr; exact .cons hgr .nil
            · intro hz
              simp only [Bool.or_eq_true] at hz
              refine ⟨.bits n0, rfl, rd, rfl, ?_⟩
              rcases hz with hze | hzu
              · simpa [hze] using hgr
              · simp only [Bool.and_eq_true, Nat.beq_eq] at hzu
                obtain ⟨rfl, hzu'⟩ := hzu
                exact ⟨by decide, hzu hzu' rfl⟩
            · intro hzu
              simp only [Bool.and_eq_true, Nat.beq_eq] at hzu
              obtain ⟨rfl, hzu'⟩ := hzu
              exact ⟨rfl, rd, rfl, hzu hzu' rfl⟩
          · simp at h

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

theorem tryMulHi_ok {zl : Bool} (hsv : ∀ r ∈ hints.saved, r ∈ T.frame.calleeSaved)
    {G : VCtx} {nv k : Nat} {st : SymState T.toIsa} {s : T.mach.MData} {σ : List (BitVec 64)}
    {m : Mem 64} {ts sig : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig} {P : Tup Val ts → Prop}
    {c : List T.Directive} {clob : FlagMask} {dhi : T.Reg}
    (hA : Agree T G nv st s σ) (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hargs : TRel (ArgRel G) args₁ args) (hwp : code.wp (vals args₁) P)
    (h : tryMulHi T.toIsa hints st nv code args = some (c, clob, dhi))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (kont : ∀ (rvs : Tup Val ts) s', P rvs →
      Agree T (Tup.zip rvs (Tup.levels ts nv) ++ G) (nv + ts.length)
        { st with
          regs := (.var (nv + 1), .gpr dhi) ::
            killRegs T.toIsa (dhi :: T.frame.scratch) [] clob st.regs
          zeroExt32 := killZeroExt (dhi :: T.frame.scratch) st.zeroExt32
          flags := killFlags T.toIsa clob st.flags
          scrConsts := [] } s' σ →
      MemDefsOk (Tup.zip rvs (Tup.levels ts nv) ++ G) m (nv + ts.length) st.memDefs →
      Inv T hints s₀ ra n Rf m s' σ zl → T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have finishMul : ∀ {n0 : Nat} {ht : ts = [.bits n0, .bits n0]} {lo hi : BitVec n0}
      {s' : T.mach.MData}
      (hs : hints.dest.find? (nv + 1) = some (.gpr dhi))
      (hdg : isAllocGpr T.toIsa hints.saved dhi = true)
      (hP : P (ht ▸ (lo, hi, ())))
      (hg : GprHolds (T.mach.getGpr s' dhi) (.bits n0) hi)
      (hm' : T.mach.mem s' = T.mach.mem s)
      (hfr : T.mach.Frame T.gpr.condReads s s' (dhi :: T.frame.scratch) [] clob),
      T.mach.Run host (k + c.length) s' post := by
    intro n0 ht lo hi s' _ hdg hP hg hm' hfr
    subst ht
    let G' : VCtx := Tup.zip (lo, hi, ()) (Tup.levels [.bits n0, .bits n0] nv) ++ G
    have hMgrow : MemDefsOk G' m (nv + 2) st.memDefs :=
      hM.grow (by omega) (fun p hp => (zip_levels_mem hp).imp id (·.1))
        (fun _ hp => List.mem_append_right _ hp)
    have hK := hA.kill hfr
    have hnone : ∀ x, nv ≤ x → st.vecWidths.find? x = none := fun x hx =>
      Option.eq_none_iff_forall_ne_some.mpr fun w hw => absurd (hA.vw_lt _ _ hw) (by omega)
    have hA1 := hK.extend (G' := G') (nv' := nv + 2) (by omega)
      (fun p hp => (zip_levels_mem hp).imp id (·.1))
      (fun p hp => (zip_levels_mem hp).elim
        (fun h => Nat.lt_trans (hA.ctx_lt p h) (by omega)) (fun h => h.2))
      (fun _ hp => List.mem_append_right _ hp)
      (ctx_uniq_zip hA.ctx_lt hA.ctx_uniq [.bits n0, .bits n0] (lo, hi, ()) nv (Nat.le_refl _))
      (fun x _ => rfl)
      (fun x w hx hle => absurd (hnone x hle) (by simp [hx]))
      (fun p hp hle _ => by
        simp only [G', Tup.zip, Tup.levels, List.cons_append, List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · intro a b hc; cases hc
        · intro a b hc; cases hc
        · exact absurd (hA.ctx_lt p hp) (Nat.not_lt.mpr hle))
    have hreg : RegLocOk T.mach G' s' (.var (nv + 1)) (.gpr dhi) := by
      intro t' v' hm''
      simp only [G', Tup.zip, Tup.levels, List.cons_append, List.mem_cons] at hm''
      rcases hm'' with hm1 | hm2 | hmG
      · cases hm1
      · cases hm2; exact hg
      · exact absurd (hA.ctx_lt _ hmG) (Nat.not_lt.mpr (Nat.le_succ nv))
    have hA2 : Agree T G' (nv + 2)
        { regs := (.var (nv + 1), .gpr dhi) ::
            killRegs T.toIsa (dhi :: T.frame.scratch) [] clob st.regs
          slots := st.slots, defs := st.defs, vecWidths := st.vecWidths
          memDefs := st.memDefs
          zeroExt32 := killZeroExt (dhi :: T.frame.scratch) st.zeroExt32
          flags := killFlags T.toIsa clob st.flags, scrConsts := [] } s' σ :=
      { hA1 with
        regs := fun p hp => (List.mem_cons.mp hp).elim (fun e => e ▸ hreg) (hA1.regs p)
        regs_lt := fun p hp => (List.mem_cons.mp hp).elim
          (fun e => e ▸ by simp [symArgScopeOk]) (hA1.regs_lt p) }
    have halloc : ∀ r ∈ [dhi], isAllocGpr T.toIsa hints.saved r = true := by simpa using hdg
    exact kont (lo, hi, ()) s' hP hA2 hMgrow (hI.keep hm' (keep_of_frame hfr.1 halloc))
  cases hmh : T.gpr.mulHi? with
  | none => simp [tryMulHi, hmh] at h
  | some fn =>
    cases code with
    | umulw n0 =>
      rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
      cases hargs with | cons ha hb => cases hb with | cons hb _ =>
      dsimp only [tryMulHi] at h; rw [hmh] at h; dsimp only at h
      cases hd : hints.dest.find? (nv + 1) with
      | none => rw [hd] at h; cases h
      | some loc =>
        rw [hd] at h
        cases loc with
        | vec _ | flag _ | slot _ _ => cases h
        | gpr rd =>
          dsimp only at h
          by_cases hgd : (isAllocGpr T.toIsa hints.saved rd && isGprTy T.toIsa (.bits n0)) = true
          · simp only [hgd, ↓reduceIte] at h
            simp only [Bool.and_eq_true] at hgd
            obtain ⟨pa, hka, hpa, -, hpaH⟩ := tryArg_ok hA ha h
            obtain ⟨pb, hkb, hpb, -, hpbH⟩ := tryArg_ok hA hb hka
            obtain ⟨⟨c0, cl0⟩, hm, he⟩ := Option.map_eq_some_iff.mp hkb
            simp only [Prod.mk.injEq] at he; rcases he with ⟨rfl, rfl, rfl⟩
            have hrd : rd ∉ T.frame.scratch := not_scratch_of_isAllocGpr hsv hgd.1
            have hargsS : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ T.frame.scratch :=
              fun r hr => (List.mem_append.mp hr).elim (hpa r) (hpb r)
            refine T.gprSpec.mulHi_spec hmh hm hargsS hrd hpaH hpbH hc fun s' ⟨hg, hm'⟩ hfr => ?_
            simp only [OpCode.wp, vals] at hwp
            exact finishMul (ht := rfl) hd hgd.1 hwp hg hm' hfr
          · simp [hgd] at h
    | smulw n0 =>
      rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
      cases hargs with | cons ha hb => cases hb with | cons hb _ =>
      dsimp only [tryMulHi] at h; rw [hmh] at h; dsimp only at h
      cases hd : hints.dest.find? (nv + 1) with
      | none => rw [hd] at h; cases h
      | some loc =>
        rw [hd] at h
        cases loc with
        | vec _ | flag _ | slot _ _ => cases h
        | gpr rd =>
          dsimp only at h
          by_cases hgd : (isAllocGpr T.toIsa hints.saved rd && isGprTy T.toIsa (.bits n0)) = true
          · simp only [hgd, ↓reduceIte] at h
            simp only [Bool.and_eq_true] at hgd
            obtain ⟨pa, hka, hpa, -, hpaH⟩ := tryArg_ok hA ha h
            obtain ⟨pb, hkb, hpb, -, hpbH⟩ := tryArg_ok hA hb hka
            obtain ⟨⟨c0, cl0⟩, hm, he⟩ := Option.map_eq_some_iff.mp hkb
            simp only [Prod.mk.injEq] at he; rcases he with ⟨rfl, rfl, rfl⟩
            have hrd : rd ∉ T.frame.scratch := not_scratch_of_isAllocGpr hsv hgd.1
            have hargsS : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ T.frame.scratch :=
              fun r hr => (List.mem_append.mp hr).elim (hpa r) (hpb r)
            refine T.gprSpec.mulHi_spec hmh hm hargsS hrd hpaH hpbH hc fun s' ⟨hg, hm'⟩ hfr => ?_
            simp only [OpCode.wp, vals] at hwp
            exact finishMul (ht := rfl) hd hgd.1 hwp hg hm' hfr
          · simp [hgd] at h
    | _ => simp [tryMulHi, hmh] at h

end Lemmas

end Rega
end LeanQbe.T
