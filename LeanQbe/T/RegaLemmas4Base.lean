module

public import LeanQbe.T.RegaLemmas2
public import LeanQbe.T.RegaLemmas3

/-!
# `RegaLemmas` Part 4: `Wf.induct` Correctness of `lowerExpr`, `lowerBlocks`, and `lowerFn`

* `LabJ`/`makeLabJs`/`DOk`: join points are interpreted as "running from the block label is safe
  for every machine state agreeing with the block `Entry`" (avoiding a separate
  pending-label pass).
* `lowerExpr_correct` by `Wf.induct`, `lowerBlocks_closed` by induction on `WfB`.
* `lowerFn_correct : ... → T.FnSpec host f.name (Func.spec Γ f.body) n nX`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

section Defs
variable (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (fn : Sym)
  (s₀ : T.mach.MData) (ra : T.mach.Addr) (n nX : Nat) (Rf : Mem 64 → Prop) {rs : List Ty}
  (Q : Post rs) (X : XPost)

/-- Machine meaning of block label `codeℓ` for join point `entryℓ` declared in value context `G`. -/
@[expose] def LabJ (G : VCtx) (codeℓ entryℓ : Nat) {ts : List Ty} : Cont ts := fun xs m =>
  ∃ k en, (T.mach.prog host)[k]? = some (T.frame.label (lname fn codeℓ)) ∧
    hints.entry.find? entryℓ = some en ∧
    ∀ s σ, (∀ p ∈ en.live, LocOk T.mach G s σ p.1 p.2) → ParamsOk T.mach s σ ts xs en.ploc →
      LiveZOk T.mach G s σ en.live en.liveZ → ParamsZOk T.mach s σ ts xs en.ploc en.plocZ →
      Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E) →
      T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X)

@[expose] def makeLabJs (fwd : Trie Nat) (G : VCtx) : (sig : List (List Ty)) → Nat → Tup Cont sig
  | [], _ => ()
  | ts :: sig, lid =>
    (LabJ T host hints E fn s₀ ra n nX Rf Q X G (tgtLab fwd lid) lid (ts := ts),
      makeLabJs fwd G sig (lid + 1))

/-- Every join point in scope is a `LabJ` of an enclosing context routed through `fwd`. -/
@[expose] def DOk (fwd : Trie Nat) (G : VCtx) (D : Ctx Cont LNat) : Prop :=
  ∀ ts (J : Cont ts) (ℓ : Nat), ⟨ts, J, ℓ⟩ ∈ D →
    (∃ k : Nat, (T.mach.prog host)[k]? = some (T.frame.label (lname fn (tgtLab fwd ℓ)))) ∧
    ∃ G', (∀ p ∈ G', p ∈ G) ∧ J = LabJ T host hints E fn s₀ ra n nX Rf Q X G' (tgtLab fwd ℓ) ℓ

/-- Scope bound on logical labels in `D`. -/
@[expose] def DScope (nl : Nat) (D : Ctx Cont LNat) : Prop :=
  ∀ ts (J : Cont ts) (ℓ : Nat), ⟨ts, J, ℓ⟩ ∈ D → ℓ < nl

/-- Target/key well-formedness for jump-to-jump forwarding maps. -/
@[expose] def FwdBound (nl : Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool) : Prop :=
  (∀ x y, fwd.find? x = some y → x < nl ∧ fwd.find? y = none ∧ fwdTgts.find? y = some true) ∧
  (∀ x, fwdTgts.find? x = some true → fwd.find? x = none)

/-- Fallthrough obligation: code following position `k` starts with label `ft`. -/
@[expose] def FT (ft : Option Nat) (k : Nat) : Prop :=
  ∀ j, ft = some j → (T.mach.prog host)[k]? = some (T.frame.label (lname fn j))

end Defs

section Basic
variable {T : Target} {host : T.mach.Host} {hints : T.toIsa.Hints} {E : Ext} {fn : Sym}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n nX : Nat} {Rf : Mem 64 → Prop} {rs : List Ty}
  {Q : Post rs} {X : XPost}

theorem labelAddr_of_unique (hu : T.LabelsUnique host) {j : Nat} {l : Sym}
    (hj : (T.mach.prog host)[j]? = some (T.frame.label l)) :
    T.mach.labelAddr host l = T.mach.addrOf host j :=
  T.frameSpec.labelAddr_eq hj fun j' hj' e => by have := hu _ _ _ e hj; omega

theorem FwdBound.mono {nl nl' : Nat} {fwd : Trie Nat} {fwdTgts : Trie Bool}
    (hle : nl ≤ nl') (h : FwdBound nl fwd fwdTgts) : FwdBound nl' fwd fwdTgts :=
  ⟨fun x y hx => have ⟨h1, h2⟩ := h.1 x y hx; ⟨Nat.lt_of_lt_of_le h1 hle, h2⟩, h.2⟩

theorem DScope.mono {nl nl' : Nat} {D : Ctx Cont LNat} (hle : nl ≤ nl') (h : DScope nl D) :
    DScope nl' D := fun ts J ℓ hJ => Nat.lt_of_lt_of_le (h ts J ℓ hJ) hle

theorem DScope_makeLabJs {fwd : Trie Nat} {G : VCtx} :
    ∀ (sig : List (List Ty)) (lid : Nat) {D : Ctx Cont LNat},
    DScope lid D →
    DScope (lid + sig.length)
      (Tup.zip (makeLabJs T host hints E fn s₀ ra n nX Rf Q X fwd G sig lid)
        (Tup.levels sig lid) ++ D)
  | [], lid, D, hD => by simpa [makeLabJs, Tup.levels, Tup.zip] using hD
  | ts :: sig, lid, D, hD => by
    intro ts' J' ℓ hmem
    simp only [makeLabJs, Tup.levels, Tup.zip, List.cons_append, List.mem_cons] at hmem
    rcases hmem with hhd | htl
    · cases hhd; simp
    · have ih := DScope_makeLabJs sig (lid + 1) (hD.mono (Nat.le_succ _)) ts' J' ℓ htl
      simp only [List.length_cons] at ih ⊢; omega

theorem DOk.weaken {fwd : Trie Nat} {G G' : VCtx} {D : Ctx Cont LNat} (hsub : ∀ p ∈ G, p ∈ G')
    (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D) :
    DOk T host hints E fn s₀ ra n nX Rf Q X fwd G' D := by
  intro ts J ℓ hJ
  obtain ⟨hk, G'', hG'', rfl⟩ := hD ts J ℓ hJ
  exact ⟨hk, G'', fun p hp => hsub p (hG'' p hp), rfl⟩

theorem DOk_fwd_mono {fwd fwd' : Trie Nat} {nl : Nat} {G : VCtx} {D : Ctx Cont LNat}
    (hSc : DScope nl D) (hf : ∀ x < nl, fwd'.find? x = fwd.find? x)
    (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D) :
    DOk T host hints E fn s₀ ra n nX Rf Q X fwd' G D := by
  intro ts J ℓ hJ
  have hlt := hSc ts J ℓ hJ
  have htg : tgtLab fwd' ℓ = tgtLab fwd ℓ := by simp [tgtLab, Trie.getD, hf ℓ hlt]
  simpa [htg] using hD ts J ℓ hJ

theorem makeLabJs_dok {fwd : Trie Nat} {G : VCtx} :
    ∀ (sig : List (List Ty)) (lid : Nat) {D : Ctx Cont LNat},
    (∀ i, i < sig.length → ∃ k : Nat,
      (T.mach.prog host)[k]? = some (T.frame.label (lname fn (tgtLab fwd (lid + i))))) →
    DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D →
    DOk T host hints E fn s₀ ra n nX Rf Q X fwd G
      (Tup.zip (makeLabJs T host hints E fn s₀ ra n nX Rf Q X fwd G sig lid)
        (Tup.levels sig lid) ++ D)
  | [], _, _, _, hD => by simpa [makeLabJs, Tup.levels, Tup.zip] using hD
  | ts :: sig, lid, D, hl, hD => by
    intro ts' J ℓ hmem
    simp only [makeLabJs, Tup.levels, Tup.zip, List.cons_append, List.mem_cons] at hmem
    rcases hmem with hhd | htl
    · cases hhd; exact ⟨by simpa using hl 0 (by simp), G, fun _ hp => hp, rfl⟩
    · exact makeLabJs_dok sig (lid + 1)
        (fun i hi => by simpa [Nat.add_assoc, Nat.add_comm 1] using hl (i + 1) (by simp; omega)) hD
        ts' J ℓ htl

theorem LocOk.frame {G : VCtx} {s s' : T.mach.MData} {σ : List (BitVec 64)} {sa : SymArg}
    {loc : T.toIsa.Loc} {g : List T.Reg} {v : List T.VReg} {f : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' g v f) (hok : LocOk T.mach G s σ sa loc)
    (hg : ∀ r, loc = .gpr r → r ∉ g) (hv : ∀ vr, loc = .vec vr → vr ∉ v)
    (hf : ∀ c, loc = .flag c → FlagMask.disjoint (T.gpr.condReads c) f = true) :
    LocOk T.mach G s' σ sa loc := by
  cases loc with
  | gpr r => simp only [LocOk] at hok ⊢; rwa [hfr.1 r (hg r rfl)]
  | vec vr => simp only [LocOk] at hok ⊢; rwa [hfr.2.1 vr (hv vr rfl)]
  | flag c => simp only [LocOk] at hok ⊢; rwa [hfr.2.2 c (hf c rfl)]
  | slot i w => exact hok

theorem jumpLocOk_spec {nslots : Nat} {loc : T.toIsa.Loc}
    (h : jumpLocOk T.toIsa nslots loc = true) :
    (∀ r, loc = .gpr r → r ∉ T.frame.scratch) ∧ (∀ vr, loc = .vec vr → vr ∉ T.vec.vecScratch) := by
  cases loc <;> simp_all [jumpLocOk]

/-- `Agree` for the block-entry base state (lexical `defs`/`vw` of the enclosing group). -/
theorem Agree.base {G : VCtx} {nvg nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nvg st s σ) (hle : nvg ≤ nv) (s' : T.mach.MData)
    (σ' : List (BitVec 64)) :
    Agree T G nv
      { regs := [], slots := .empty, defs := st.defs, vecWidths := st.vecWidths } s' σ' where
  ctx_lt p hp := Nat.lt_of_lt_of_le (hA.ctx_lt p hp) hle
  ctx_uniq := hA.ctx_uniq
  regs p hp := by simp at hp
  slots i se h := by simp [Trie.find?] at h
  defs := hA.defs
  vw := hA.vw
  regs_lt p hp := by simp at hp
  slots_lt i se h := by simp [Trie.find?] at h
  defs_lt x d h := Nat.lt_of_lt_of_le (hA.defs_lt x d h) hle
  zeroExt32_ok r hr := by simp at hr
  vw_lt x w h := Nat.lt_of_lt_of_le (hA.vw_lt x w h) hle
  vt := hA.vt
  flags_ok := trivial
  flags_lt := trivial
  scrConsts_ok := scrOk_nil _ _ _

theorem paramsZOk_frame_jump {s s' : T.mach.MData} {σ : List (BitVec 64)}
    {g : List T.Reg} {v : List T.VReg} {f : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' g v f) :
    ∀ {ts : List Ty} {args : Tup (Arg VNat) ts} {xs : Tup Val ts}
      {ploc : List T.toIsa.Loc} {plocZ : List Bool} {argTgts : List (SymArg × T.toIsa.Loc)},
    jumpTargets T.toIsa args ploc = some argTgts →
    (∀ p ∈ argTgts, ∀ r, p.2 = .gpr r → r ∉ g) →
    ParamsZOk T.mach s σ ts xs ploc plocZ → ParamsZOk T.mach s' σ ts xs ploc plocZ
  | [], (), (), [], _, _, _, _, _ => trivial
  | [], (), (), _ :: _, _, _, hj, _, _ => by simp [jumpTargets] at hj
  | _ :: _, _, _, [], _, _, hj, _, _ => by simp [jumpTargets] at hj
  | _ :: _, (_, _), (_, _), _ :: _, [], _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), loc :: locs, _ :: zs, argTgts, hj, hloc, ⟨h1, h2⟩ => by
    dsimp only [jumpTargets] at hj
    split at hj
    · rename_i sa rest hsa hrest
      simp only [Option.some.injEq] at hj; subst hj
      refine ⟨fun hz => ?_, paramsZOk_frame_jump hfr hrest
        (fun p hp => hloc p (List.mem_cons_of_mem _ hp)) h2⟩
      have hpz := h1 hz
      cases loc with
      | gpr r => simpa [ParamZVal, hfr.1 r (hloc _ List.mem_cons_self r rfl)] using hpz
      | slot _ _ | vec _ | flag _ => exact hpz
    · simp at hj

private theorem buildEntryBaseZ_memDefs {I : Isa} {nslots : Nat} {vw : Trie SlotWidth} :
    ∀ {xs : List (SymArg × I.Loc)} {zs : List Bool} {st0 st' : SymState I},
    buildEntryBaseZ I nslots vw xs zs st0 = some st' → st'.memDefs = st0.memDefs
  | [], _, _, _, h => by simp only [buildEntryBaseZ, Option.some.injEq] at h; rw [h]
  | (_, loc) :: _, zs, _, _, h => by
    cases loc <;> simp only [buildEntryBaseZ] at h
    · split at h; · simpa using buildEntryBaseZ_memDefs h
      · simp at h
    · split at h; · simpa using buildEntryBaseZ_memDefs h
      · simp at h
    · simpa using buildEntryBaseZ_memDefs h
    · split at h; · simp at h
      · obtain ⟨_, -, h'⟩ := Option.bind_eq_some_iff.mp h; simpa using buildEntryBaseZ_memDefs h'

private theorem bindBlockParamsZ_memDefs {I : Isa} {nslots : Nat} :
    ∀ {ts : List Ty} {locs : List I.Loc} {zs : List Bool} {nv0 : Nat} {st0 st' : SymState I},
    bindBlockParamsZ I nslots ts locs zs nv0 st0 = some st' → st'.memDefs = st0.memDefs
  | [], [], _, _, _, _, h => by simp only [bindBlockParamsZ, Option.some.injEq] at h; rw [h]
  | t :: _, loc :: _, _, _, _, _, h => by
    cases loc <;> simp only [bindBlockParamsZ] at h
    · split at h; · simpa using bindBlockParamsZ_memDefs h
      · simp at h
    · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h; · simpa using bindBlockParamsZ_memDefs h
      · simp at h
    · cases t <;> simp at h; simpa using bindBlockParamsZ_memDefs h
    · split at h; · simp at h
      · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; simpa using bindBlockParamsZ_memDefs h
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h => by simp [bindBlockParamsZ] at h

theorem symArgEq_var {sa : SymArg} {x : Nat} (h : symArgEq sa (.var x) = true) : sa = .var x := by
  cases sa <;> simp_all [symArgEq]

theorem symArgMatchesGpr_var {sa : SymArg} {x : Nat} (h : symArgMatchesGpr sa (.var x) = true) :
    sa = .var x := by
  unfold symArgMatchesGpr at h
  split at h
  · exact symArgEq_var ‹_›
  · cases sa <;> simp_all

theorem findSome_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {b : β}, l.findSome? f = some b → ∃ a ∈ l, f a = some b
  | [], _, h => by simp at h
  | a :: l, b, h => by
    simp only [List.findSome?_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; obtain ⟨a', ha', h'⟩ := findSome_mem h; exact ⟨a', .tail _ ha', h'⟩
    | some b' => rw [ha] at h; cases h; exact ⟨a, .head _, ha⟩

private theorem findGprFor_var_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {x : Nat} {g : T.Reg}
    (hg : findGprFor T.toIsa true st.regs (.var x) = some g) :
    g ∉ T.frame.scratch ∧ GprSym G (T.mach.getGpr s g) (.var x) := by
  unfold findGprFor at hg
  obtain ⟨⟨sa, rl⟩, hp, he⟩ := findSome_mem hg
  cases rl with
  | gpr g' =>
    simp only at he; split at he
    · cases he; rename_i hc
      simp only [Bool.and_eq_true] at hc
      have h1 := hA.regs _ hp
      simp only [RegLocOk, symArgMatchesGpr_var hc.2] at h1
      exact ⟨fun hm => by simp [hm] at hc, h1⟩
    · cases he
  | gprZ g' =>
    simp only at he; split at he
    · cases he; rename_i hc
      simp only [Bool.and_eq_true] at hc
      have h1 := (hA.regs _ hp).1
      simp only [symArgMatchesGpr_var hc.2] at h1
      exact ⟨fun hm => by simp [hm] at hc, h1⟩
    · cases he
  | _ => simp at he

/-- `widenZextCmp?` soundness: a narrow unsigned/equality compare of a canonical `.gprZ` value
against `0` agrees with the 64-bit compare of the whole register. -/
theorem widenZextCmp_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {co : CmpOp} {w y : Nat} {g : T.Reg}
    {va : BitVec w} {cv : Bool} (hwz : widenZextCmp? T.toIsa st.regs co w y g = true)
    (hmy : (⟨.bits w, va, y⟩ : (t : Ty) × Val t × VNat t) ∈ G) (hcv : cv = co.evalBits va 0#w) :
    ∃ va' : BitVec 64, GprHolds (T.mach.getGpr s g) (.bits 64) va' ∧
      cv = co.evalBits va' 0#64 := by
  simp only [widenZextCmp?, Bool.and_eq_true, Nat.blt_eq] at hwz
  obtain ⟨⟨⟨-, hw⟩, hco⟩, hz⟩ := hwz
  simp only [hasVarGprZ, List.any_eq_true, Bool.and_eq_true] at hz
  obtain ⟨⟨sa', rl'⟩, hmem, hsa⟩ := hz
  have heq1 := symArgEq_eq hsa.1; have heq2 := regLocEq_eq hsa.2
  subst heq1; subst heq2
  have hzv := (hA.regs _ hmem).2 (.bits w) va hmy
  refine ⟨va.setWidth 64, ⟨Nat.le_refl _, by rw [hzv.2, BitVec.setWidth_eq]⟩, ?_⟩
  rw [hcv]
  have h0 := cmpOp_evalBits_zeroExtend hw hco va 0#64 (by simp)
  simp only [BitVec.truncate_eq_setWidth, BitVec.setWidth_zero] at h0
  exact h0.symm

/-- `jnz` condition lookup. -/
theorem findJnzCond_ok {zl : Bool} {G : VCtx} {nv : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hM : MemDefsOk G m nv st.memDefs) {cv : Bool} {cx : Nat}
    (hmem : (⟨.bool, cv, cx⟩ : (t : Ty) × Val t × VNat t) ∈ G) :
    ∀ {r}, findJnzCond T.toIsa hints.nslots st cx = some r →
    match r with
    | .flag c => T.mach.evalCond s c = cv
    | .gpr g => g ∉ T.frame.scratch ∧ GprHolds (T.mach.getGpr s g) .bool cv
    | .slot idx =>
      idx < hints.nslots ∧ ∃ w, σ[idx]? = some w ∧ GprHolds w .bool cv
    | .cmpZero co w g =>
      g ∉ T.frame.scratch ∧ ∃ va : BitVec w, GprHolds (T.mach.getGpr s g) (.bits w) va ∧
        cv = co.evalBits va 0#w
    | .cmpZeroMem co w x aa cc =>
      w ≤ 64 ∧ x < nv ∧ (∀ r ∈ aa.regs, r ∉ T.frame.scratch) ∧
      ∃ va : BitVec w, loadVal (T.mach.mem s) (.bits w) (aa.eval (T.mach.getGpr s)) = some va ∧
        cv = co.evalBits va 0#w ∧ ⟨.bits w, va, x⟩ ∈ G ∧ SymBits G w va (.var x) ∧
        T.gpr.condOfCmp? co = some cc ∧
        (∃ c cl, T.gpr.cmpMem co w aa (.imm 0#w) (.flag cc) = some (c, cl))
    | .cmpZeroFlag co w x g cc =>
      w ≤ 64 ∧ x < nv ∧ g ∉ T.frame.scratch ∧
      ∃ va : BitVec w, GprHolds (T.mach.getGpr s g) (.bits w) va ∧
        cv = co.evalBits va 0#w ∧ ⟨.bits w, va, x⟩ ∈ G ∧ SymBits G w va (.var x) ∧
        T.gpr.condOfCmp? co = some cc ∧
        (∃ c cl, T.gpr.op (.cmp co (.bits w)) (.gpr g, .imm 0#w, ()) (.flag cc, ()) .default =
          some (c, cl))
    | .testImm neg w g mask =>
      g ∉ T.frame.scratch ∧ ∃ va : BitVec w, GprHolds (T.mach.getGpr s g) (.bits w) va ∧
        cv = (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& mask) 0#w := by
  intro r hr
  unfold findJnzCond at hr
  rcases orElse_eq_some hr with hf | hr
  · obtain ⟨c, hf', he⟩ := Option.map_eq_some_iff.mp hf
    cases he
    unfold findFlagFor at hf'
    obtain ⟨⟨sa, rl⟩, hp, he'⟩ := findSome_mem hf'
    cases rl with
    | flag c' =>
      simp only at he'; split at he'
      · cases he'
        have h1 := hA.regs _ hp
        simp only [RegLocOk, symArgEq_var ‹_›, FlagSym] at h1
        exact (h1 _ _ hmem).symm
      · cases he'
    | _ => simp at he'
  rcases orElse_eq_some hr with hdfl | hr
  · cases hdx : st.defs.find? cx with
    | none => simp [hdx] at hdfl
    | some df =>
      have hdef := hA.defs cx df hdx
      cases df with
      | cmpZeroVar co w y =>
        simp only [hdx] at hdfl
        obtain ⟨c, hcf, heq⟩ := Option.map_eq_some_iff.mp hdfl
        subst heq; dsimp only
        obtain ⟨va, hmy, hcv⟩ := hdef.2 cv hmem
        rw [hcv]
        exact cmpZeroFlagCond_ok hA hmy hcf
      | _ => simp [hdx] at hdfl
  rcases orElse_eq_some hr with hg | hr
  · obtain ⟨g, hg', he⟩ := Option.map_eq_some_iff.mp hg
    cases he
    have ⟨hns, hsym⟩ := findGprFor_var_ok hA hg'
    exact ⟨hns, hsym _ _ hmem⟩
  rcases orElse_eq_some hr with hd | hs
  · cases hdx : st.defs.find? cx with
    | none => simp [hdx] at hd
    | some df =>
      have hdef := hA.defs cx df hdx
      cases df with
      | cmpZeroVar co w y =>
        simp only [hdx] at hd
        obtain ⟨va, hmy, hcv⟩ := hdef.2 cv hmem
        rcases orElse_eq_some hd with hm | hg
        · cases hmd : st.memDefs.find? y with
          | none => simp [hmd] at hm
          | some p =>
            rcases p with ⟨tm, addr⟩
            cases tm with
            | bits w' =>
              simp only [hmd] at hm
              split at hm
              · rename_i hgd
                simp only [Bool.and_eq_true, Nat.beq_eq] at hgd
                obtain ⟨rfl, hstd⟩ := hgd
                have hw64 : w' ≤ 64 := by
                  simp only [isStdBitWidth, Bool.or_eq_true, Nat.beq_eq] at hstd
                  rcases hstd with ((rfl | rfl) | rfl) | rfl <;> omega
                obtain ⟨cc, hcc, hm⟩ := Option.bind_eq_some_iff.mp hm
                obtain ⟨-, hlv0⟩ := hM y (.bits w') addr hmd
                obtain ⟨a₁, ha₁, hlv⟩ := hlv0 va hmy
                obtain ⟨aa, hk, hreg, haev⟩ := tryAddr_ok hA ha₁ hm
                obtain ⟨⟨c0, cl0⟩, hcm, heq⟩ := Option.map_eq_some_iff.mp hk
                cases heq
                have hlm : loadVal (T.mach.mem s) (.bits w')
                    (aa.eval (T.mach.getGpr s)) = some va := by
                  rw [haev]; exact loadVal_frame hI.2.2.2.1 hlv
                have hsymY : SymBits G w' va (.var y) := memDefs_tryAddr_symBits hA hM hmd hmy hm
                exact ⟨hw64, hA.ctx_lt _ hmy, hreg, va, hlm, hcv, hmy, hsymY, hcc, c0, cl0, hcm⟩
              · simp at hm
            | _ => simp [hmd] at hm
        · obtain ⟨g, hgy, hd'⟩ := Option.bind_eq_some_iff.mp hg
          have ⟨hns, hsym⟩ := findGprFor_var_ok hA hgy
          split at hd'
          · rename_i hwz
            simp only [Option.some.injEq] at hd'; subst hd'
            simp only [Bool.and_eq_true] at hwz
            exact ⟨hns, widenZextCmp_ok hA hwz.1 hmy hcv⟩
          split at hd'
          · simp only [Option.some.injEq] at hd'; subst hd'
            exact ⟨hns, va, hsym _ _ hmy, hcv⟩
          · split at hd'
            · rename_i hstd
              have hw64 : w ≤ 64 := by
                simp only [isStdBitWidth, Bool.or_eq_true, Nat.beq_eq] at hstd
                rcases hstd with ((rfl | rfl) | rfl) | rfl <;> omega
              obtain ⟨cc, hcc, hd'⟩ := Option.bind_eq_some_iff.mp hd'
              obtain ⟨⟨c0, cl0⟩, hop, heq⟩ := Option.map_eq_some_iff.mp hd'
              cases heq
              have hsymY : SymBits G w va (.var y) := fun v hv => by
                rw [← (hsym (.bits w) v hv).2, (hsym (.bits w) _ hmy).2]
              exact ⟨hw64, hA.ctx_lt _ hmy, hns, va, hsym _ _ hmy, hcv, hmy, hsymY,
                hcc, c0, cl0, hop⟩
            · simp at hd'
      | testBitVar neg w y c =>
        simp only [hdx] at hd
        obtain ⟨g, hgy, heq⟩ := Option.map_eq_some_iff.mp hd
        subst heq
        have ⟨hns, hsym⟩ := findGprFor_var_ok hA hgy
        obtain ⟨va, hmy, hcv⟩ := hdef.2 cv hmem
        exact ⟨hns, va, hsym _ _ hmy, hcv⟩
      | _ => simp [hdx] at hd
  · obtain ⟨idx, hs', he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨hlt, w, hσ, hgpr⟩ := findSlotGpr_ok hA hs'
    exact ⟨hlt, w, hσ, hgpr _ _ hmem⟩

end Basic

/-! ## The main induction -/


section Main
variable {T : Target} {host : T.mach.Host} {hints : T.toIsa.Hints} {E : Ext} {Γ : Env} {fn : Sym}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n nX : Nat} {Rf : Mem 64 → Prop} {bound : Sym → Nat}
  {rs : List Ty} {Q : Post rs} {X : XPost}

/-- The `Wf.induct` motive. -/
@[expose]
def Motive (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (Γ : Env) (fn : Sym)
    (s₀ : T.mach.MData) (ra : T.mach.Addr) (n nX : Nat) (Rf : Mem 64 → Prop) {rs : List Ty}
    (Q : Post rs) (X : XPost) (G : VCtx) (D : Ctx Cont LNat)
    (e₁ : Expr Val Cont rs) (e₂ : Expr VNat LNat rs) : Prop :=
  ∀ (nv nl ip : Nat) (st : SymState T.toIsa) (ft : Option Nat)
    (fwd : Trie Nat) (fwdTgts : Trie Bool)
    (c : List T.Directive) (nv' nl' ip' k : Nat) (s : T.mach.MData) (σ : List (BitVec 64))
    (m : Mem 64),
  lowerExpr T.toIsa hints E fn e₂ nv nl ip st ft fwd fwdTgts = .ok (c, nv', nl', ip') →
  c.IsInfixAt (T.mach.prog host) k → FT T host fn ft (k + c.length) →
  FwdBound nl fwd fwdTgts → DScope nl D →
  DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D → Agree T G nv st s σ →
  MemDefsOk G m nv st.memDefs →
  Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E) → wp Γ Q X e₁ m →
  T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X)

/-- Jump to a join point `J = LabJ G' codeℓ entryℓ` after targets hold. -/
theorem enter_labJ (hy : Hyps T host hints E Γ s₀ n nX bound) {G G' : VCtx} (hGs : ∀ p ∈ G', p ∈ G)
    {ts : List Ty} {args₁ : Tup (Arg Val) ts} {args : Tup (Arg VNat) ts}
    (hargs : TRel (ArgRel G) args₁ args)
    {codeℓ entryℓ k : Nat} {en : Entry T.Reg T.VReg T.Cond} {argTgts : List (SymArg × T.toIsa.Loc)}
    (hen : hints.entry.find? entryℓ = some en)
    (hjt : jumpTargets T.toIsa args en.ploc = some argTgts)
    {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    (hok : ∀ p ∈ en.live ++ argTgts, LocOk T.mach G s σ p.1 p.2)
    (hokZ : LiveZOk T.mach G s σ en.live en.liveZ)
    (hpZ : ParamsZOk T.mach s σ ts (vals args₁) en.ploc en.plocZ)
    (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    (hlab : (T.mach.prog host)[k]? = some (T.frame.label (lname fn codeℓ)))
    (hJ : LabJ T host hints E fn s₀ ra n nX Rf Q X G' codeℓ entryℓ (vals args₁) m) :
    T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X) := by
  obtain ⟨kℓ, en', hlab', hen', hrun⟩ := hJ
  rw [hen] at hen'; cases hen'
  have hk := hy.unique _ _ _ hlab hlab'
  subst hk
  refine hrun s σ (fun p hp => LocOk.mono hGs (hok p (List.mem_append_left _ hp))) ?_
    (LiveZOk.mono hGs hokZ) hpZ hI
  exact paramsOk_of_jumpTargets hargs hjt fun p hp => hok p (List.mem_append_right _ hp)

theorem lowerBlocks_labelPos {I : Isa} {h : I.Hints} {E : Ext} {prog : List I.Directive} :
    ∀ {sig : List (List Ty)} (bs : Blocks VNat LNat rs sig) (lid nv nl ip : Nat)
      (defs : Trie DefFact)
      (vw : Trie SlotWidth) (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool)
      (cb : List I.Directive) (nv' nl' ip' kb : Nat),
    lowerBlocks I h E fn bs lid nv nl ip defs vw ft fwd fwdTgts = .ok (cb, nv', nl', ip') →
    cb.IsInfixAt prog kb →
    (∀ i, i < sig.length → fwd.find? (lid + i) = none →
      ∃ k : Nat, prog[k]? = some (I.frame.label (lname fn (lid + i)))) ∧
    ((∀ j, ft = some j → prog[kb + cb.length]? = some (I.frame.label (lname fn j))) →
      ∀ j, firstNonFwd fwd bs lid ft = some j → prog[kb]? = some (I.frame.label (lname fn j)))
  | _, .nil, _, _, _, _, _, _, ft, fwd, _, cb, _, _, _, kb, hl, _ => by
    simp only [lowerBlocks, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, -⟩ := hl
    refine ⟨fun _ hi _ => by simp at hi, fun hft j hj => ?_⟩
    simp only [firstNonFwd] at hj
    simpa using hft j hj
  | _ :: _, .cons b bs, lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts, cb, nv', nl', ip', kb,
      hl, hc => by
    simp only [lowerBlocks] at hl
    cases hfw : fwd.find? lid with
    | some fwdTgt =>
      rw [hfw] at hl; dsimp only at hl
      cases hbt : blockTrampoline? I h defs vw lid nv ip b with
      | none => simp [hbt] at hl
      | some j' =>
        rw [hbt] at hl; dsimp only at hl
        split at hl
        · simp at hl
        · have ih := lowerBlocks_labelPos bs (lid + 1) _ _ _ defs vw ft fwd fwdTgts cb nv' nl' ip'
            kb hl hc
          refine ⟨fun i hi hni => ?_, fun hft j hj => ?_⟩
          · cases i with
            | zero => simp [hfw] at hni
            | succ i =>
              obtain ⟨k, hk⟩ := ih.1 i (by simp at hi; omega)
                (by simpa [Nat.add_assoc, Nat.add_comm 1] using hni)
              exact ⟨k, by simpa [Nat.add_assoc, Nat.add_comm 1] using hk⟩
          · simp only [firstNonFwd, hfw, Option.isSome_some, ↓reduceIte] at hj
            exact ih.2 hft j hj
    | none =>
      rw [hfw] at hl; dsimp only at hl
      split at hl; · simp at hl
      split at hl; · simp at hl
      split at hl; · simp at hl
      split at hl; · simp at hl
      split at hl; · simp at hl
      obtain ⟨cr, hr, rfl⟩ := prepend_ok hl
      have hhead := (List.IsInfixAt.cons (List.IsInfixAt.append hc).1).1
      have ih := lowerBlocks_labelPos bs (lid + 1) _ _ _ defs vw ft fwd fwdTgts cr nv' nl' ip' _
        hr (List.IsInfixAt.append hc).2
      refine ⟨fun i hi hni => ?_, fun _ j hj => ?_⟩
      · cases i with
        | zero => exact ⟨kb, by simpa using hhead⟩
        | succ i =>
          obtain ⟨k, hk⟩ := ih.1 i (by simp at hi; omega)
            (by simpa [Nat.add_assoc, Nat.add_comm 1] using hni)
          exact ⟨k, by simpa [Nat.add_assoc, Nat.add_comm 1] using hk⟩
      · simp only [firstNonFwd, hfw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq] at hj
        subst hj; exact hhead

private theorem wf_jump_right {G : VCtx} {D : Ctx Cont LNat}
    {e₁ : Expr Val Cont rs} {ts : List Ty} {j₂ : Nat} {args₂ : Tup (Arg VNat) ts}
    (h : Wf G D e₁ (.jump j₂ args₂)) :
    ∃ (J₁ : Cont ts) (args₁ : Tup (Arg Val) ts),
      e₁ = .jump J₁ args₁ ∧ ⟨ts, J₁, j₂⟩ ∈ D ∧ TRel (ArgRel G) args₁ args₂ := by
  cases h with | jump hj hargs => exact ⟨_, _, rfl, hj, hargs⟩

theorem lowerBlocks_closed (hy : Hyps T host hints E Γ s₀ n nX bound)
    {G : VCtx} {D' : Ctx Cont LNat}
    {fwd : Trie Nat} {fwdTgts : Trie Bool}
    (hD' : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D') {nvg : Nat} {stg : SymState T.toIsa}
    {sg : T.mach.MData} {σg : List (BitVec 64)} (hAg : Agree T G nvg stg sg σg) :
    ∀ {sig : List (List Ty)} {bs₁ : Blocks Val Cont rs sig} {bs₂ : Blocks VNat LNat rs sig},
    WfB G D' bs₁ bs₂ →
    (∀ {ts} (i : Member ts sig) (xs₁ : Tup Val ts) (xs₂ : Tup VNat ts),
      Motive T host hints E Γ fn s₀ ra n nX Rf Q X (Tup.zip xs₁ xs₂ ++ G) D'
        (bs₁.get i xs₁) (bs₂.get i xs₂)) →
    ∀ (lid nv nl ip : Nat) (ft : Option Nat) (cb : List T.Directive) (nv' nl' ip' kb : Nat),
    nvg ≤ nv → FwdBound nl fwd fwdTgts → DScope nl D' →
    lowerBlocks T.toIsa hints E fn bs₂ lid nv nl ip stg.defs stg.vecWidths ft fwd fwdTgts =
      .ok (cb, nv', nl', ip') →
    cb.IsInfixAt (T.mach.prog host) kb → FT T host fn ft (kb + cb.length) →
    Closed Γ Q X bs₁ (makeLabJs T host hints E fn s₀ ra n nX Rf Q X fwd G sig lid)
  | [], .nil, .nil, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | ts :: _, .cons b₁ bs₁, .cons b₂ bs₂, .cons hb0 hbs', ihb, lid, nv, nl, ip, ft, cb,
      nv', nl', ip', kb, hle, hFb, hSc, hpb, hcode, hft => by
    simp only [lowerBlocks] at hpb
    cases hfw : fwd.find? lid with
    | some fwdTgt =>
      rw [hfw] at hpb; dsimp only at hpb
      cases hbt : blockTrampoline? T.toIsa hints stg.defs stg.vecWidths lid nv ip b₂ with
      | none => simp [hbt] at hpb
      | some j' =>
        rw [hbt] at hpb; dsimp only at hpb
        split at hpb; · simp at hpb
        rename_i hgd
        have htgtEq : tgtLab fwd j' = fwdTgt := by
          by_cases hbeq : (Nat.beq (tgtLab fwd j') fwdTgt && (fwd.find? fwdTgt).isNone) = true
          · simp only [Bool.and_eq_true, Nat.beq_eq] at hbeq; exact hbeq.1
          · exact absurd (by simp [hbeq]) hgd
        simp only [Closed, makeLabJs]
        refine ⟨?_, lowerBlocks_closed hy hD' hAg hbs' (fun i => ihb (.there i)) (lid + 1)
          (nv + ts.length) nl (ip + 1) ft cb nv' nl' ip' kb
          (Nat.le_trans hle (Nat.le_add_right _ _)) hFb hSc hpb hcode hft⟩
        intro xs₁ m' hwpb
        unfold blockTrampoline? at hbt
        cases hen : hints.entry.find? lid with
        | none => simp [hen] at hbt
        | some en =>
          rw [hen] at hbt; dsimp only at hbt
          by_cases hsc : entryScopeOk nv en = true
          · simp only [hsc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hbt
            cases hbe : buildEntryBaseZ T.toIsa hints.nslots stg.vecWidths en.live en.liveZ
                { regs := [], slots := .empty, defs := stg.defs, vecWidths := stg.vecWidths } with
            | none => simp [hbe] at hbt
            | some baseSt =>
              rw [hbe] at hbt; dsimp only at hbt
              cases hbp : bindBlockParamsZ T.toIsa hints.nslots ts en.ploc en.plocZ nv baseSt with
              | none => simp [hbp] at hbt
              | some initSt =>
                rw [hbp] at hbt; dsimp only at hbt
                cases heqb : b₂ (Tup.levels ts nv) with
                | jump j'' args' =>
                  rw [heqb] at hbt
                  cases hpre : stepPre T.toIsa hints ip initSt with
                  | none => simp [hpre] at hbt
                  | some p1 =>
                    rcases p1 with ⟨mc, st1⟩
                    cases mc with
                    | cons _ _ => simp [hpre] at hbt
                    | nil =>
                      cases hen' : hints.entry.find? j'' with
                      | none => simp [hpre, hen'] at hbt
                      | some en' =>
                        simp only [hpre, hen'] at hbt
                        cases hjt : jumpTargets T.toIsa args' en'.ploc with
                        | none => simp [hjt] at hbt
                        | some argTgts =>
                          rw [hjt] at hbt; dsimp only at hbt
                          split at hbt; · simp at hbt
                          rename_i hall
                          cases hsh : shuffle T.toIsa hints.nslots hints.saved st1
                              (en'.live ++ argTgts) with
                          | none => simp [hsh] at hbt
                          | some p2 =>
                            rcases p2 with ⟨sc, st2⟩
                            cases sc with
                            | cons _ _ => simp [hsh] at hbt
                            | nil =>
                              rw [hsh] at hbt; dsimp only at hbt
                              split at hbt
                              · rename_i hez
                                simp only [Option.some.injEq] at hbt
                                subst hbt
                                have hwf := hb0 xs₁ (Tup.levels ts nv)
                                rw [heqb] at hwf
                                obtain ⟨J₁, args₁, he1, hj1, hargs1⟩ := wf_jump_right hwf
                                rw [he1] at hwpb
                                obtain ⟨⟨kj', hlabj'⟩, G'', hG'', rfl⟩ := hD' _ J₁ j'' hj1
                                have hlabF : (T.mach.prog host)[kj']? =
                                    some (T.frame.label (lname fn (tgtLab fwd lid))) := by
                                  have h1 : tgtLab fwd lid = fwdTgt := by
                                    simp [tgtLab, Trie.getD, hfw]
                                  rw [h1, ← htgtEq]
                                  exact hlabj'
                                refine ⟨kj', en, hlabF, hen,
                                  fun s σ hlive hparams hliveZ hparamsZ hI => ?_⟩
                                have hσ : σ.length = hints.nslots := hI.1
                                have hlt : ∀ p ∈ en.live, symArgScopeOk nv p.1 = true := by
                                  simpa [entryScopeOk, List.all_eq_true] using hsc
                                have hA0 := buildEntryBaseZ_ok hbe hlive hliveZ hlt hσ
                                  (hAg.base hle s σ)
                                have hA1 := bindBlockParamsZ_ok hbp hparams hparamsZ hσ hA0
                                refine stepPre_ok hy.spE hpre List.nil_prefix hA1 hI
                                  fun s1 σ1 hA2 hI2 => ?_
                                refine shuffle_ok hy.spE hsh List.nil_prefix hA2 hI2
                                  fun s2 σ2 hok hA3 hI3 => ?_
                                simp only [List.length_nil, Nat.add_zero] at *
                                obtain ⟨hlZ, hpZ⟩ := entryZOk_ok hA3 hargs1 hjt hez
                                exact enter_labJ hy (fun p hp => List.mem_append_right _ (hG''
                                  p hp))
                                  hargs1 hen' hjt hok hlZ hpZ hI3 hlabj' hwpb
                              · simp at hbt
                | _ => simp [heqb] at hbt
          · simp [hsc] at hbt
    | none =>
      rw [hfw] at hpb; dsimp only at hpb
      cases hen : hints.entry.find? lid with
      | none => simp [hen] at hpb
      | some en =>
        simp only [hen] at hpb
        by_cases hsc : entryScopeOk nv en = true
        · simp only [hsc, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpb
          cases hbe : buildEntryBaseZ T.toIsa hints.nslots stg.vecWidths en.live en.liveZ
              { regs := [], slots := .empty, defs := stg.defs, vecWidths := stg.vecWidths } with
          | none => simp [hbe] at hpb
          | some baseSt =>
            simp only [hbe] at hpb
            cases hbp : bindBlockParamsZ T.toIsa hints.nslots ts en.ploc en.plocZ nv baseSt with
            | none => simp [hbp] at hpb
            | some initSt =>
              simp only [hbp] at hpb
              split at hpb
              · simp at hpb
              · rename_i cbb nv1 nl1 ip1 hlb
                obtain ⟨cr, hpr, rfl⟩ := prepend_ok hpb
                have hhead := (List.IsInfixAt.append hcode).1
                have hlab := (List.IsInfixAt.cons hhead).1
                have hcbb := (List.IsInfixAt.cons hhead).2
                have hrest := (List.IsInfixAt.append hcode).2
                have hle' := lowerExpr_nv_le hlb
                have hnv1 : nv ≤ nv1 := by omega
                have hnl1 : nl ≤ nl1 := hle'.2
                simp only [Closed, makeLabJs]
                refine ⟨?_, ?_⟩
                · intro xs₁ m' hwpb
                  refine ⟨kb, en, by simpa [tgtLab, Trie.getD, hfw] using hlab, hen,
                    fun s σ hlive hparams hliveZ hparamsZ hI => ?_⟩
                  refine T.frameSpec.label_spec hlab ?_
                  have hσ : σ.length = hints.nslots := hI.1
                  have hlt : ∀ p ∈ en.live, symArgScopeOk nv p.1 = true := by
                    simpa [entryScopeOk, List.all_eq_true] using hsc
                  have hA0 := buildEntryBaseZ_ok hbe hlive hliveZ hlt hσ (hAg.base hle s σ)
                  have hA1 := bindBlockParamsZ_ok hbp hparams hparamsZ hσ hA0
                  have hmd : initSt.memDefs = .empty :=
                    (bindBlockParamsZ_memDefs hbp).trans (buildEntryBaseZ_memDefs hbe)
                  have hlabsR := lowerBlocks_labelPos (prog := T.mach.prog host) bs₂ (lid + 1)
                    nv1 nl1 ip1 stg.defs stg.vecWidths ft fwd fwdTgts cr nv' nl' ip'
                    (kb + (T.frame.label (lname fn lid) :: cbb).length) hpr hrest
                  refine ihb .here xs₁ (Tup.levels ts nv) (nv + ts.length) nl ip initSt _ fwd
                    fwdTgts
                    cbb nv1 nl1 ip1 (kb + 1) s σ m' hlb hcbb ?_ hFb hSc
                    (hD'.weaken fun _ hp => List.mem_append_right _ hp)
                    hA1 (hmd ▸ MemDefsOk.empty _ _ _) hI hwpb
                  intro j hj
                  have h1 := hlabsR.2 (fun j' hj' => by
                    have heq1 : kb + (T.frame.label (lname fn lid) :: cbb).length + cr.length =
                        kb + (T.frame.label (lname fn lid) :: cbb ++ cr).length := by
                      simp only [List.length_cons, List.length_append]; omega
                    rw [heq1]; exact hft j' hj') j hj
                  have heq2 : kb + 1 + cbb.length =
                      kb + (T.frame.label (lname fn lid) :: cbb).length := by
                    simp only [List.length_cons]; omega
                  rwa [heq2]
                · exact lowerBlocks_closed hy hD' hAg hbs' (fun i => ihb (.there i)) (lid + 1)
                    nv1 nl1 ip1 ft cr nv' nl' ip'
                    (kb + (T.frame.label (lname fn lid) :: cbb).length)
                    (Nat.le_trans hle hnv1) (hFb.mono hnl1) (hSc.mono hnl1) hpr hrest (by
                      have e : kb + (T.frame.label (lname fn lid) :: cbb).length + cr.length =
                          kb + (T.frame.label (lname fn lid) :: cbb ++ cr).length := by
                        simp only [List.length_append, List.length_cons]; omega
                      rw [e]; exact hft)
        · simp [hsc] at hpb


theorem run_congr {a b : Nat} {s : T.mach.MData} {p : T.mach.State → Prop} (h : a = b)
    (hr : T.mach.Run host a s p) : T.mach.Run host b s p := h ▸ hr

theorem jnzMode_spec {I : Isa} {h : I.Hints} {ipT ipE : Nat} {st : SymState I} {canInv : Bool}
    {t e : Expr VNat LNat rs} {ft : Option Nat} {fwd : Trie Nat} {inv : Bool} {j : Nat}
    (hm : jnzMode I h ipT ipE st canInv t e ft fwd = (inv, some j)) :
    (inv = false → zeroMoveJump? I h ipT st t = some j) ∧
    (inv = true → zeroMoveJump? I h ipE st e = some j) := by
  unfold jnzMode at hm
  split at hm <;> (try split at hm) <;> simp_all

/-- A zero-move threaded jump (`jnz` taken branch straight to a join point). -/
theorem thread_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx} {D : Ctx Cont LNat}
    {fwd : Trie Nat} {tb₁ : Expr Val Cont rs} {tb₂ : Expr VNat LNat rs} (hwf : Wf G D tb₁ tb₂)
    (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D)
    {ip : Nat} {stB : SymState T.toIsa} {j : Nat} {m : Mem 64}
    (hz : zeroMoveJump? T.toIsa hints ip stB tb₂ = some j) :
    ∃ kj, (T.mach.prog host)[kj]? = some (T.frame.label (lname fn (tgtLab fwd j))) ∧
      (wp Γ Q X tb₁ m → ∀ nv s σ, Agree T G nv stB s σ →
        Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E) →
        T.mach.Run host kj s (FnPost T host s₀ ra n nX Rf Q X)) := by
  cases hwf with
  | @jump _ _ ts j₁ j₂ args₁ args₂ hj hargs =>
    simp only [zeroMoveJump?] at hz
    split at hz
    · simp at hz
    · cases hen : hints.entry.find? j₂ with
      | none => simp [hen] at hz
      | some en =>
        cases hjt : jumpTargets T.toIsa args₂ en.ploc with
        | none => simp [hen, hjt] at hz
        | some argTgts =>
          simp only [hen, hjt, Option.bind_some] at hz
          split at hz
          · rename_i hall
            simp only [Bool.and_eq_true] at hall
            simp only [Option.some.injEq] at hz; subst hz
            obtain ⟨⟨kℓ, hlab⟩, G', hGs, rfl⟩ := hD ts j₁ j₂ hj
            refine ⟨kℓ, hlab, fun hwp nv s σ hA hI => ?_⟩
            simp only [wp] at hwp
            have hJ := hwp
            obtain ⟨hlZ, hpZ⟩ := entryZOk_ok hA hargs hjt hall.2
            refine enter_labJ hy hGs hargs hen hjt (fun p hp => ?_) hlZ hpZ hI hlab hJ
            have := List.all_eq_true.mp hall.1 p hp
            simp only [Bool.and_eq_true] at this
            exact holdsLoc_ok hA this.2
          · simp at hz
  | _ => simp [zeroMoveJump?] at hz

theorem keep_of_frame_scratch {s s' : T.mach.MData} {v : List T.VReg} {f : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' T.frame.scratch v f) :
    ∀ r, isMoveGpr T.toIsa hints.saved r = false → T.mach.getGpr s' r = T.mach.getGpr s r :=
  fun r hr => hfr.1 r fun hm => by simp [isMoveGpr, hm] at hr


theorem FT_congr {a b : Nat} {ft : Option Nat} (h : a = b) (hf : FT T host fn ft a) :
    FT T host fn ft b :=
  h ▸ hf

theorem FT_none (k : Nat) : FT T host fn none k := fun _ h => nomatch h

theorem Agree.mono_nv {G : VCtx} {nv nv' : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) (hle : nv ≤ nv') : Agree T G nv' st s σ :=
  hA.extend hle (fun _ hp => .inl hp) (fun _ hp => Nat.lt_of_lt_of_le (hA.ctx_lt _ hp) hle)
    (fun _ hp => hp) hA.ctx_uniq (vw' := st.vecWidths) (fun _ _ => rfl)
    (fun x _ h hx => absurd (hA.vw_lt x _ h) (Nat.not_lt.mpr hx))
    (fun p hp hx => absurd (hA.ctx_lt p hp) (Nat.not_lt.mpr hx))

theorem finishJnzBranch_some {I : Isa} {fn : Sym} {nl j : Nat} {b : Expr VNat LNat rs}
    {br cft ctk cf : List I.Directive} {nv2 nl2 ip2 nv' nl' ip' : Nat}
    (h : finishJnzBranch I fn nl (some j) b br cft ctk nv2 nl2 ip2 = .ok (cf, nv', nl', ip')) :
    cf = br ++ cft ∧ nv' = nv2 ∧ nl' = nl2 ∧ ip' = ip2 := by
  simp only [finishJnzBranch] at h
  split at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
    · cases h
  · cases h

theorem finishJnzBranch_none {I : Isa} {fn : Sym} {nl : Nat} {b : Expr VNat LNat rs}
    {br cft ctk cf : List I.Directive} {nv2 nl2 ip2 nv' nl' ip' : Nat}
    (h : finishJnzBranch I fn nl none b br cft ctk nv2 nl2 ip2 = .ok (cf, nv', nl', ip')) :
    cf = br ++ (cft ++ ([I.frame.label (lname fn nl)] ++ ctk)) ∧
      nv' = nv2 ∧ nl' = nl2 ∧ ip' = ip2 := by
  simp only [finishJnzBranch, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨by rw [← h.1]; simp [List.append_assoc], h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

private theorem threadFusedArm_spec {I : Isa} {h : I.Hints} {fn : Sym} {ipA : Nat}
    {st1 : SymState I} {emit : Sym → Option (List I.Directive × FlagMask)}
    {arm : Expr VNat LNat rs} {fwd : Trie Nat} {j : Nat} {br : List I.Directive} {stB : SymState I}
    (ht : threadFusedArm I h fn ipA st1 emit arm fwd = some (j, br, stB)) :
    zeroMoveJump? I h ipA stB arm = some j ∧ stB.memDefs = st1.memDefs ∧
      ∃ cl, emit (lname fn (tgtLab fwd j)) = some (br, cl) ∧
        stB = { st1 with
          regs := killRegs I I.frame.scratch [] cl st1.regs
          zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
          flags := killFlags I cl st1.flags
          scrConsts := [] } := by
  unfold threadFusedArm at ht
  split at ht
  · simp only [Option.bind_eq_some_iff] at ht
    obtain ⟨⟨br', cl'⟩, hem, hif⟩ := ht
    split at hif
    · rename_i hzm
      simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨rfl, rfl, rfl⟩ := hif
      rw [beq_iff_eq] at hzm
      exact ⟨hzm, rfl, cl', hem, rfl⟩
    · simp at hif
  · simp at ht

private theorem fuseJnzChoice_spec {I : Isa} {h : I.Hints} {fn : Sym} {nl ipT ipE : Nat}
    {st1 : SymState I} {t e : Expr VNat LNat rs} {ft : Option Nat}
    {emit : Bool → Sym → Option (List I.Directive × FlagMask)} {fwd : Trie Nat} {inv : Bool}
    {tgt : Option Nat} {br : List I.Directive} {stBr : SymState I}
    (hf : fuseJnzChoice I h fn nl ipT ipE st1 t e ft emit fwd = some (inv, tgt, br, stBr)) :
    stBr.memDefs = st1.memDefs ∧
    (∃ cl, emit inv (lname fn (match tgt with | some j => tgtLab fwd j | none => nl)) =
        some (br, cl) ∧
      stBr = { st1 with
        regs := killRegs I I.frame.scratch [] cl st1.regs
        zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
        flags := killFlags I cl st1.flags
        scrConsts := [] }) ∧
    (∀ j, tgt = some j →
      (inv = false → zeroMoveJump? I h ipT stBr t = some j) ∧
      (inv = true → zeroMoveJump? I h ipE stBr e = some j)) := by
  unfold fuseJnzChoice at hf
  obtain ⟨⟨brNl, clNl⟩, heNl, hm⟩ := Option.map_eq_some_iff.mp hf
  cases hfwd : threadFusedArm I h fn ipT st1 (emit false) t fwd with
  | none =>
    cases hinv : threadFusedArm I h fn ipE st1 (emit true) e fwd with
    | none =>
      rw [hfwd, hinv] at hm; simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      exact ⟨rfl, ⟨clNl, heNl, rfl⟩, fun _ hj => nomatch hj⟩
    | some pE =>
      obtain ⟨je, brI, stI⟩ := pE
      rw [hfwd, hinv] at hm; simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      have hs := threadFusedArm_spec hinv
      exact ⟨hs.2.1, hs.2.2, fun j hj => by
        cases hj; exact ⟨(fun h => nomatch h), fun _ => hs.1⟩⟩
  | some pF =>
    obtain ⟨jt, brF, stF⟩ := pF
    cases hinv : threadFusedArm I h fn ipE st1 (emit true) e fwd with
    | none =>
      rw [hfwd, hinv] at hm; simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      have hs := threadFusedArm_spec hfwd
      exact ⟨hs.2.1, hs.2.2, fun j hj => by
        cases hj; exact ⟨fun _ => hs.1, (fun h => nomatch h)⟩⟩
    | some pE =>
      obtain ⟨je, brI, stI⟩ := pE
      rw [hfwd, hinv] at hm
      dsimp only at hm; split at hm <;> simp only [Prod.mk.injEq] at hm <;>
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
      · have hs := threadFusedArm_spec hinv
        exact ⟨hs.2.1, hs.2.2, fun j hj => by
          cases hj; exact ⟨(fun h => nomatch h), fun _ => hs.1⟩⟩
      · have hs := threadFusedArm_spec hfwd
        exact ⟨hs.2.1, hs.2.2, fun j hj => by
          cases hj; exact ⟨fun _ => hs.1, (fun h => nomatch h)⟩⟩

theorem jnzSetup_thread {I : Isa} {h : I.Hints} {nl ipT ipE : Nat} {st1 : SymState I}
    {t e : Expr VNat LNat rs} {ft : Option Nat} {cond : JnzCond I} {fwd : Trie Nat}
    {inv : Bool} {j : Nat} {br : List I.Directive} {stBr : SymState I}
    (hs : jnzSetup I h fn nl ipT ipE st1 t e ft cond fwd = some (inv, some j, br, stBr)) :
    (inv = false → zeroMoveJump? I h ipT stBr t = some j) ∧
    (inv = true → zeroMoveJump? I h ipE stBr e = some j) := by
  cases cond with
  | flag cc =>
    simp only [jnzSetup, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨h1, h2, -, rfl⟩ := hs
    exact jnzMode_spec (Prod.ext h1 h2)
  | gpr r =>
    dsimp only [jnzSetup] at hs
    cases hfn : I.gpr.jnzGprInv? with
    | some jnzFn =>
      rw [hfn] at hs; exact (fuseJnzChoice_spec hs).2.2 j rfl
    | none =>
      rw [hfn] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, h2, -, rfl⟩ := hs
      refine ⟨fun _ => ?_, fun h => nomatch h⟩
      have htgEq := h2
      cases harm : t with
      | jump j' args =>
        rw [harm] at h2; dsimp only [gprThread?] at h2
        have hj : j' = j := by
          simp only [zeroMoveJump?] at h2
          split at h2
          · simp at h2
          · cases hen : h.entry.find? j' with
            | none => simp [hen] at h2
            | some en =>
              cases hjt : jumpTargets I args en.ploc with
              | none => simp [hen, hjt] at h2
              | some at' =>
                simp only [hen, hjt, Option.bind_some] at h2
                split at h2 <;> simp_all
        subst hj
        rw [harm] at htgEq
        rw [htgEq]
        exact h2
      | _ => rw [harm] at h2; simp [gprThread?] at h2
  | slot idx =>
    simp only [jnzSetup, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨_, _⟩, -, hc⟩ := hs
    split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨h1, h2, -, rfl⟩ := hc
      exact jnzMode_spec (Prod.ext h1 h2)
    · simp at hc
  | cmpZero co w r =>
    simp only [jnzSetup] at hs
    exact (fuseJnzChoice_spec hs).2.2 j rfl
  | cmpZeroMem co w x aa cc =>
    simp only [jnzSetup] at hs
    obtain ⟨⟨_, _⟩, _, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [finishCmpJnz, Prod.mk.injEq] at he
    obtain ⟨h1, h2, -, rfl⟩ := he
    exact jnzMode_spec (Prod.ext h1 h2)
  | cmpZeroFlag co w x r cc =>
    simp only [jnzSetup] at hs
    obtain ⟨⟨_, _⟩, _, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [finishCmpJnz, Prod.mk.injEq] at he
    obtain ⟨h1, h2, -, rfl⟩ := he
    exact jnzMode_spec (Prod.ext h1 h2)
  | testImm neg w r mask =>
    simp only [jnzSetup] at hs
    exact (fuseJnzChoice_spec hs).2.2 j rfl

theorem jnzSetup_memDefs {I : Isa} {h : I.Hints} {nl ipT ipE : Nat} {st1 : SymState I}
    {t e : Expr VNat LNat rs} {ft : Option Nat} {cond : JnzCond I} {fwd : Trie Nat}
    {inv : Bool} {tgt : Option Nat} {br : List I.Directive} {stBr : SymState I}
    (hs : jnzSetup I h fn nl ipT ipE st1 t e ft cond fwd = some (inv, tgt, br, stBr)) :
    stBr.memDefs = st1.memDefs := by
  cases cond with
  | flag _ => simp only [jnzSetup, Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.2.2.2]
  | gpr _ =>
    dsimp only [jnzSetup] at hs
    cases hfn : I.gpr.jnzGprInv? with
    | some jnzFn => rw [hfn] at hs; exact (fuseJnzChoice_spec hs).1
    | none =>
      rw [hfn] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.2.2.2]
  | slot _ =>
    simp only [jnzSetup, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨_, _⟩, -, hc⟩ := hs
    split at hc
    · simp only [Option.some.injEq, Prod.mk.injEq] at hc
      rw [← hc.2.2.2]
    · simp at hc
  | cmpZero _ _ _ | testImm _ _ _ _ => simp only [jnzSetup] at hs; exact (fuseJnzChoice_spec hs).1
  | cmpZeroMem _ _ _ _ _ | cmpZeroFlag _ _ _ _ _ =>
    simp only [jnzSetup] at hs
    obtain ⟨⟨_, _⟩, _, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [finishCmpJnz, Prod.mk.injEq] at he
    rw [← he.2.2.2]

/-- Branch on the `jnz` condition (`jcc`, `jnzGpr`, `jnzMem`, `cmpZeroJcc`, or `testJcc`). -/
theorem branch_ok {zl : Bool} (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {nv nl ipT ipE : Nat} {st1 stBr : SymState T.toIsa} {s1 : T.mach.MData}
    {σ1 : List (BitVec 64)} {m : Mem 64} {cv : Bool} {cx : Nat}
    (hmem : (⟨.bool, cv, cx⟩ : (t : Ty) × Val t × VNat t) ∈ G)
    (hA1 : Agree T G nv st1 s1 σ1) (hI1 : Inv T hints s₀ ra n Rf m s1 σ1 zl)
    (hM1 : MemDefsOk G m nv st1.memDefs)
    {cond : JnzCond T.toIsa} (hfc : findJnzCond T.toIsa hints.nslots st1 cx = some cond)
    {t e : Expr VNat LNat rs} {ft : Option Nat} {fwd : Trie Nat} {inv : Bool} {tgt : Option Nat}
    {br : List T.Directive}
    {kb kT : Nat} {post : T.mach.State → Prop} (hbr : br.IsInfixAt (T.mach.prog host) kb)
    (hlab : (T.mach.prog host)[kT]? =
      some (T.frame.label (lname fn (match tgt with | some j => tgtLab fwd j | none => nl))))
    (hs : jnzSetup T.toIsa hints fn nl ipT ipE st1 t e ft cond fwd = some (inv, tgt, br, stBr))
    (kont : ∀ s', Agree T G nv stBr s' σ1 → Inv T hints s₀ ra n Rf m s' σ1 zl →
      ((if inv then !cv else cv) = true → T.mach.Run host kT s' post) ∧
      ((if inv then !cv else cv) = false → T.mach.Run host (kb + br.length) s' post)) :
    T.mach.Run host kb s1 post := by
  have hc := findJnzCond_ok hA1 hI1 hM1 hmem hfc
  have hla := labelAddr_of_unique hy.unique hlab
  cases cond with
  | flag cc =>
    simp only at hc
    simp only [jnzSetup, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    refine T.gprSpec.jcc_spec hbr hla fun s' hfr hm => ?_
    have := kont s' (hA1.kill hfr) (hI1.keep hm (keep_of_frame_scratch hfr))
    have hev : T.mach.evalCond s1 (if (jnzMode T.toIsa hints ipT ipE
        { st1 with
          regs := killRegs T.toIsa T.frame.scratch [] FlagMask.none st1.regs
          zeroExt32 := killZeroExt T.frame.scratch st1.zeroExt32
          flags := killFlags T.toIsa FlagMask.none st1.flags
          scrConsts := [] } true t e ft fwd).1
        then T.gpr.negCond cc else cc) =
        (if (jnzMode T.toIsa hints ipT ipE
        { st1 with
          regs := killRegs T.toIsa T.frame.scratch [] FlagMask.none st1.regs
          zeroExt32 := killZeroExt T.frame.scratch st1.zeroExt32
          flags := killFlags T.toIsa FlagMask.none st1.flags
          scrConsts := [] } true t e ft fwd).1
        then !cv else cv) := by
      split <;> simp_all [T.gprSpec.negCond_eval]
    rw [hev]; exact this
  | gpr r =>
    simp only at hc
    dsimp only [jnzSetup] at hs
    cases hfn : T.gpr.jnzGprInv? with
    | some jnzFn =>
      rw [hfn] at hs
      obtain ⟨-, ⟨cl, hem, rfl⟩, -⟩ := fuseJnzChoice_spec hs
      simp only [Option.some.injEq] at hem
      have hbr' : br = _ := congrArg Prod.fst hem.symm
      have hcl' : cl = _ := congrArg Prod.snd hem.symm
      rw [hbr'] at hbr
      refine T.gprSpec.jnzGprInv_spec hfn hbr hla hc.1 hc.2 fun s' hfr hm => ?_
      have := kont s' (by simpa [hcl'] using hA1.kill hfr) (hI1.keep hm (keep_of_frame_scratch hfr))
      simpa [hbr'] using this
    | none =>
      rw [hfn] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
      refine T.gprSpec.jnzGpr_spec hbr hla hc.1 hc.2 fun s' hfr hm => ?_
      have := kont s' (hA1.kill hfr) (hI1.keep hm (keep_of_frame_scratch hfr))
      simpa using this
  | slot idx =>
    simp only at hc
    simp only [jnzSetup, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨br', cl'⟩, hjbr, hcl⟩ := hs
    split at hcl
    · rename_i hclAll
      simp only [Option.some.injEq, Prod.mk.injEq] at hcl
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hcl
      obtain rfl : cl' = FlagMask.all := beq_iff_eq.mp hclAll
      obtain ⟨w64, hσ, hgpr⟩ := hc.2
      obtain ⟨v8, hlv, hv8⟩ := spAddr_load_bool hc.1 hI1 hσ hgpr
      have hsp : ∀ r ∈ (spAddr T.toIsa idx).regs, r ∉ T.frame.scratch := fun r hr => by
        simp only [spAddr, AddrArg.regs, List.mem_singleton] at hr; subst hr
        exact T.frameSpec.sp_disj.1
      refine T.gprSpec.jnzMem_spec hjbr hbr hla hsp hlv hv8 fun s' hfr hm => ?_
      exact kont s' (hA1.kill hfr) (hI1.keep hm (keep_of_frame_scratch hfr))
    · cases hcl
  | cmpZero co w r =>
    obtain ⟨hns, va, hgp, hcv⟩ := hc
    simp only [jnzSetup] at hs
    obtain ⟨-, ⟨cl, hem, rfl⟩, -⟩ := fuseJnzChoice_spec hs
    refine T.gprSpec.cmpZeroJcc_spec hem hbr hla hns hgp fun s' hfr hm => ?_
    have := kont s' (hA1.kill hfr) (hI1.keep hm (keep_of_frame_scratch hfr))
    cases inv <;> simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
    · rw [← hcv]; exact this
    · rw [CmpOp.neg_evalBits, ← hcv]; exact this
  | cmpZeroMem co w x aa cc =>
    obtain ⟨hw64, hxlt, hreg, va, hlm, hcv, hmx, hvar, hcc, -, -, -⟩ := hc
    simp only [jnzSetup] at hs
    obtain ⟨⟨cmpCode, cl⟩, hcm, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [finishCmpJnz, Prod.mk.injEq] at he
    obtain ⟨hinv, htgt, rfl, rfl⟩ := he
    obtain ⟨hbr1, hbr2⟩ := List.IsInfixAt.append hbr
    rw [hinv, htgt] at hbr2
    have hzero : SymBits G w 0#w (.immBits w 0#64) :=
      ⟨rfl, BitVec.eq_of_getLsbD_eq fun j hj => by simp [hj]⟩
    have hvarLt : symArgScopeOk nv (.var x) = true := by
      simp [symArgScopeOk, Nat.ble_eq]; exact hxlt
    have hzeroLt : symArgScopeOk nv (.immBits w 0#64) = true := by simp [symArgScopeOk]
    cases hcmo : T.gpr.cmpMemFlagsOut? co (.flag cc) with
    | none =>
      refine T.gprSpec.cmpMem_spec (s := s1) hcm (by simpa [PArg.gprs] using hreg)
        (by simp) hlm (rfl : T.mach.PArgHolds s1 (.bits w) (.imm 0#w) 0#w) hbr1
        fun sCmp ⟨hd, hm1⟩ hfr1 => ?_
      have hA_cmp : Agree T G nv { st1 with
          regs := killRegs T.toIsa T.frame.scratch [] cl st1.regs
          zeroExt32 := killZeroExt T.frame.scratch st1.zeroExt32
          flags := (cmpMemRes T.toIsa st1 co w (.var x) (.immBits w 0#64)
            (.flag cc) cmpCode cl).2.2.1
          scrConsts := [] } sCmp σ1 := by
        simpa [cmpMemRes, hcmo] using hA1.kill hfr1
      have hI_cmp := hI1.keep hm1 (keep_of_frame_scratch hfr1)
      have hev1 : T.mach.evalCond sCmp cc = cv := by
        dsimp only [Machine.PDstHolds] at hd; rw [hd, ← hcv]
      refine T.gprSpec.jcc_spec hbr2 hla fun s' hfr2 hm2 => ?_
      have hk := kont s' (hA_cmp.kill hfr2) (hI_cmp.keep hm2 (keep_of_frame_scratch hfr2))
      simp only [hinv, htgt, List.length_append, Nat.add_assoc] at hk ⊢
      cases inv <;> simp_all [T.gprSpec.negCond_eval]
    | some lf =>
      refine T.gprSpec.cmpMem_flags_spec (s := s1) hcmo hcm (by simpa [PArg.gprs] using hreg)
        (by simp) hlm (rfl : T.mach.PArgHolds s1 (.bits w) (.imm 0#w) 0#w) hbr1
        fun sCmp ⟨hd, hfl, hm1⟩ hfr1 => ?_
      have hflOk : FlagFactOk T G sCmp (cmpMemRes T.toIsa st1 co w (.var x) (.immBits w 0#64)
          (.flag cc) cmpCode cl).2.2.1 := by
        simp only [cmpMemRes, hcmo]
        refine ⟨hw64, if lf then va else 0#w, if lf then 0#w else va, ?_, ?_, ?_, ?_, hfl⟩
        · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
          · exact hzero
          · exact hmx
        · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
          · exact hzero
          · exact hvar
        · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
          · exact hmx
          · exact hzero
        · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
          · exact hvar
          · exact hzero
      have hflLt : FlagFactScope nv (cmpMemRes T.toIsa st1 co w (.var x) (.immBits w 0#64)
          (.flag cc) cmpCode cl).2.2.1 := by
        simp only [cmpMemRes, hcmo]
        exact ⟨by cases lf <;> simp [hvarLt, hzeroLt], by cases lf <;> simp [hvarLt, hzeroLt]⟩
      have hA_cmp : Agree T G nv { st1 with
          regs := killRegs T.toIsa T.frame.scratch [] cl st1.regs
          zeroExt32 := killZeroExt T.frame.scratch st1.zeroExt32
          flags := (cmpMemRes T.toIsa st1 co w (.var x) (.immBits w 0#64)
            (.flag cc) cmpCode cl).2.2.1
          scrConsts := [] } sCmp σ1 :=
        { hA1.kill hfr1 with flags_ok := hflOk, flags_lt := hflLt }
      have hI_cmp := hI1.keep hm1 (keep_of_frame_scratch hfr1)
      have hev1 : T.mach.evalCond sCmp cc = cv := by
        dsimp only [Machine.PDstHolds] at hd; rw [hd, ← hcv]
      refine T.gprSpec.jcc_spec hbr2 hla fun s' hfr2 hm2 => ?_
      have hk := kont s' (hA_cmp.kill hfr2) (hI_cmp.keep hm2 (keep_of_frame_scratch hfr2))
      simp only [hinv, htgt, List.length_append, Nat.add_assoc] at hk ⊢
      cases inv <;> simp_all [T.gprSpec.negCond_eval]
  | cmpZeroFlag co w x r cc =>
    obtain ⟨hw64, hxlt, hns, va, hgp, hcv, hmx, hvar, hcc, -, -, -⟩ := hc
    simp only [jnzSetup] at hs
    obtain ⟨⟨cmpCode, cl⟩, hop, he⟩ := Option.map_eq_some_iff.mp hs
    simp only [finishCmpJnz, Prod.mk.injEq] at he
    obtain ⟨hinv, htgt, rfl, rfl⟩ := he
    obtain ⟨hbr1, hbr2⟩ := List.IsInfixAt.append hbr
    rw [hinv, htgt] at hbr2
    have hzero : SymBits G w 0#w (.immBits w 0#64) :=
      ⟨rfl, BitVec.eq_of_getLsbD_eq fun j hj => by simp [hj]⟩
    have hvarLt : symArgScopeOk nv (.var x) = true := by
      simp [symArgScopeOk, Nat.ble_eq]; exact hxlt
    have hzeroLt : symArgScopeOk nv (.immBits w 0#64) = true := by simp [symArgScopeOk]
    cases hcmo : T.gpr.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
    | none =>
      refine T.gprSpec.op_spec (s := s1) (P := fun res => res = (co.evalBits va 0#w, ())) hop
        (by simpa [tupArgGprs, PArg.gprs] using hns) (by simp [tupDstGprs])
        (.cons hgp (.cons rfl .nil)) (by simp [OpCode.wp_cmp, liftCmp]) hbr1
        fun sCmp ⟨⟨⟨b, ⟨⟩⟩, hb, hpd⟩, hm1⟩ hfr1 => ?_
      cases hb; cases hpd with | cons hd _ =>
      have hwBle : Nat.ble w 64 = true := Nat.ble_eq.mpr hw64
      have hA_cmp : Agree T G nv { st1 with
          regs := killRegs T.toIsa T.frame.scratch [] cl st1.regs
          zeroExt32 := killZeroExt T.frame.scratch st1.zeroExt32
          flags := if Nat.ble w 64 then
            match T.gpr.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
            | some lf => some (.cmp w (if lf then .var x else .immBits w 0#64)
                                       (if lf then .immBits w 0#64 else .var x) false)
            | none => killFlags T.toIsa cl st1.flags
          else killFlags T.toIsa cl st1.flags
          scrConsts := [] } sCmp σ1 := by
        simpa [hwBle, hcmo] using hA1.kill (by simpa [tupDstGprs] using hfr1)
      have hI_cmp := hI1.keep hm1 (keep_of_frame_scratch hfr1)
      have hev1 : T.mach.evalCond sCmp cc = cv := by
        dsimp only [Machine.PDstHolds] at hd; rw [hd, ← hcv]
      refine T.gprSpec.jcc_spec hbr2 hla fun s' hfr2 hm2 => ?_
      have hk := kont s' (hA_cmp.kill hfr2) (hI_cmp.keep hm2 (keep_of_frame_scratch hfr2))
      simp only [hinv, htgt, List.length_append, Nat.add_assoc] at hk ⊢
      cases inv <;> simp_all [T.gprSpec.negCond_eval]
    | some lf =>
      refine T.gprSpec.op_cmpFlags_spec (s := s1) hcmo hop (by simpa [PArg.gprs] using hns)
        (by simp) hgp (rfl : T.mach.PArgHolds s1 (.bits w) (.imm 0#w) 0#w) hbr1
        fun sCmp ⟨hd, hfl, hm1⟩ hfr1 => ?_
      have hwBle : Nat.ble w 64 = true := Nat.ble_eq.mpr hw64
      have hflOk : FlagFactOk T G sCmp (if Nat.ble w 64 then
          match T.gpr.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
          | some lf => some (.cmp w (if lf then .var x else .immBits w 0#64)
                                     (if lf then .immBits w 0#64 else .var x) false)
          | none => killFlags T.toIsa cl st1.flags
        else killFlags T.toIsa cl st1.flags) := by
        simp only [hwBle, ↓reduceIte, hcmo]
        refine ⟨hw64, if lf then va else 0#w, if lf then 0#w else va, ?_, ?_, ?_, ?_, hfl⟩
        · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
          · exact hzero
          · exact hmx
        · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
          · exact hzero
          · exact hvar
        · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
          · exact hmx
          · exact hzero
        · cases lf <;> simp only [↓reduceIte, Bool.false_eq_true]
          · exact hvar
          · exact hzero
      have hflLt : FlagFactScope nv (if Nat.ble w 64 then
          match T.gpr.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
          | some lf => some (.cmp w (if lf then .var x else .immBits w 0#64)
                                     (if lf then .immBits w 0#64 else .var x) false)
          | none => killFlags T.toIsa cl st1.flags
        else killFlags T.toIsa cl st1.flags) := by
        simp only [hwBle, ↓reduceIte, hcmo]
        exact ⟨by cases lf <;> simp [hvarLt, hzeroLt], by cases lf <;> simp [hvarLt, hzeroLt]⟩
      have hA_cmp : Agree T G nv { st1 with
          regs := killRegs T.toIsa T.frame.scratch [] cl st1.regs
          zeroExt32 := killZeroExt T.frame.scratch st1.zeroExt32
          flags := if Nat.ble w 64 then
            match T.gpr.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
            | some lf => some (.cmp w (if lf then .var x else .immBits w 0#64)
                                       (if lf then .immBits w 0#64 else .var x) false)
            | none => killFlags T.toIsa cl st1.flags
          else killFlags T.toIsa cl st1.flags
          scrConsts := [] } sCmp σ1 :=
        { hA1.kill hfr1 with flags_ok := hflOk, flags_lt := hflLt }
      have hI_cmp := hI1.keep hm1 (keep_of_frame_scratch hfr1)
      have hev1 : T.mach.evalCond sCmp cc = cv := by
        dsimp only [Machine.PDstHolds] at hd; rw [hd, ← hcv]
      refine T.gprSpec.jcc_spec hbr2 hla fun s' hfr2 hm2 => ?_
      have hk := kont s' (hA_cmp.kill hfr2) (hI_cmp.keep hm2 (keep_of_frame_scratch hfr2))
      simp only [hinv, htgt, List.length_append, Nat.add_assoc] at hk ⊢
      cases inv <;> simp_all [T.gprSpec.negCond_eval]
  | testImm neg w r mask =>
    obtain ⟨hns, va, hgp, hcv⟩ := hc
    simp only [jnzSetup] at hs
    obtain ⟨-, ⟨cl, hem, rfl⟩, -⟩ := fuseJnzChoice_spec hs
    refine T.gprSpec.testJcc_spec hem hbr hla hns hgp fun s' hfr hm => ?_
    have := kont s' (hA1.kill hfr) (hI1.keep hm (keep_of_frame_scratch hfr))
    cases inv <;>
      simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
    · rw [← hcv]; exact this
    · have hflip : (if !neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& mask) 0#w = !cv := by
        rw [hcv]; cases neg <;> simp [CmpOp.evalBits]
      rw [hflip]; exact this


end Main

end Rega
end LeanQbe.T
