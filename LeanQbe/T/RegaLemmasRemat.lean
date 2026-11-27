module

public import LeanQbe.T.RegaLemmas3a

/-!
# Soundness and Label-Cleanliness for `Base + ConstDisp` Rematerialization (`T.RegaLemmasRemat`)

Verifies:
* `rematAddImm64_ok`, `rematAddImm64_clean`
* `execShufMove_memDefs`, `execShufMoves_memDefs`, `shuffle_memDefs`
* `execShufMove_ok`, `execShufMoves_ok`, `shuffle_ok`
* `tryRematDirect_ok`, `tryRematCmpEqImm_ok`, `tryRematAdd64SameDst_ok`
* `tryRematDirect_clean`, `tryRematCmpEqImm_clean`, `tryRematAdd64SameDst_clean`
* `findMissingRematArg_ok`, `rematTempCands_isAllocGpr`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

section Lemmas
variable {T : Target} {host : T.mach.Host} {post : T.mach.State → Prop} {hints : T.toIsa.Hints}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n : Nat} {Rf : Mem 64 → Prop}

private theorem rematAddImm64_spec {I : Isa} {rb rd : I.Reg} {disp : BitVec 64}
    {c : List I.Directive} (h : rematAddImm64 I rb rd disp = some c) :
    I.gpr.op (.add (.bits 64)) (.gpr rb, .imm disp, ()) (.gpr rd, ())
      (.disp (Int64.ofBitVec disp)) = some (c, FlagMask.none) := by
  unfold rematAddImm64 at h
  cases hop : I.gpr.op (.add (.bits 64)) (.gpr rb, .imm disp, ()) (.gpr rd, ())
      (.disp (Int64.ofBitVec disp)) with
  | none => simp [hop] at h
  | some p =>
    rcases p with ⟨c', cl⟩
    simp only [hop] at h
    split at h
    · rename_i hcl
      simp only [Option.some.injEq] at h
      have hcl' : cl = FlagMask.none := by simpa using hcl
      rw [← h, ← hcl']
    · simp at h

private theorem rematBaseOf?_spec {I : Isa} {st : SymState I} {x base : Nat}
    {disp : BitVec 64} {rb : I.Reg} (h : rematBaseOf? I st x = some (base, disp, rb)) :
    st.defs.find? x = some (.addImm64 base disp) ∧
    findGprFor I true st.regs (.var base) = some rb := by
  unfold rematBaseOf? at h
  cases hdef : st.defs.find? x with
  | none => rw [hdef] at h; cases h
  | some df =>
    rw [hdef] at h
    cases df with
    | addImm64 b d =>
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨r, hr, h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3
      exact ⟨rfl, hr⟩
    | _ => cases h

private theorem symArgMatchesGpr_var {sa : SymArg} {x : Nat}
    (h : symArgMatchesGpr sa (.var x) = true) : sa = .var x := by
  unfold symArgMatchesGpr at h
  split at h
  · exact symArgEq_iff.mp ‹_›
  · cases sa <;> simp at h

private theorem findGprFor_var_lt {G : VCtx} {nv x : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {noScr : Bool} {r : T.Reg}
    (hA : Agree T G nv st s σ) (h : findGprFor T.toIsa noScr st.regs (.var x) = some r) :
    x < nv := by
  obtain ⟨⟨sa', rl⟩, hmem, hb⟩ := List.exists_of_findSome?_eq_some h
  cases rl with
  | gpr r' | gprZ r' =>
    dsimp only at hb; split at hb
    · rename_i hc
      simp only [Bool.and_eq_true, Option.some.injEq] at hc hb
      have hlt := hA.regs_lt _ hmem
      rw [symArgMatchesGpr_var hc.2] at hlt
      have hle : x + 1 ≤ nv := by simpa [symArgScopeOk, Nat.blt_eq] using hlt
      omega
    · cases hb
  | _ => cases hb

theorem rematAddImm64_ok {zl : Bool} {G : VCtx} {nv x base k : Nat} {disp : BitVec 64}
    {rb d : T.Reg} {st : SymState T.toIsa} {c : List T.Directive} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64}
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (hd : isAllocGpr T.toIsa hints.saved d = true)
    (hdef : st.defs.find? x = some (.addImm64 base disp))
    (hrb : findGprFor T.toIsa true st.regs (.var base) = some rb)
    (hrm : rematAddImm64 T.toIsa rb d disp = some c)
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (kont : ∀ s',
      Agree T G nv
        { st with
          regs := (.var x, .gpr d) ::
            killRegs T.toIsa (d :: T.frame.scratch) [] FlagMask.none st.regs
          zeroExt32 := killZeroExt (d :: T.frame.scratch) st.zeroExt32
          scrConsts := [] } s' σ →
      Inv T hints s₀ ra n Rf m s' σ zl → T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  have hop := rematAddImm64_spec hrm
  obtain ⟨hrb_ns, hgb⟩ := findGprFor_ok hA hrb
  have hd_ns : d ∉ T.frame.scratch := not_scratch_of_isAllocGpr hI.2.2.2.2.1 hd
  have hpa : ∀ r ∈ tupArgGprs (V := T.VReg) (C := T.Cond) (ts := [.bits 64, .bits 64])
      (PArg.gpr rb, PArg.imm disp, ()), r ∉ T.frame.scratch := by
    intro r hr; simp [tupArgGprs, tupFlatMap, PArg.gprs] at hr; subst hr; exact hrb_ns
  have hpd : ∀ r ∈ tupDstGprs (V := T.VReg) (C := T.Cond) (ts := [.bits 64])
      (PDst.gpr d, ()), r ∉ T.frame.scratch := by
    intro r hr; simp [tupDstGprs, tupFlatMap, PDst.gprs] at hr; subst hr; exact hd_ns
  have hrel : TRel (T.mach.PArgHolds s) (as := [.bits 64, .bits 64])
      (PArg.gpr rb, PArg.imm disp, ()) (T.mach.getGpr s rb, disp, ()) := by
    refine .cons ?_ (.cons rfl .nil)
    exact ⟨by decide, BitVec.setWidth_eq _⟩
  have hwp : (OpCode.add (.bits 64)).wp (T.mach.getGpr s rb, disp, ())
      (fun rvs => rvs = (T.mach.getGpr s rb + disp, ())) := by
    simp [OpCode.wp, lift2, Ty.hasFloat]
  refine T.gprSpec.op_spec hop hpa hpd hrel hwp hc fun s' ⟨⟨rvs, hrvs, hdh⟩, hm⟩ hfr => ?_
  subst hrvs
  rcases hdh with _ | ⟨hd0, -⟩
  have hrd : T.mach.getGpr s' d = T.mach.getGpr s rb + disp := by
    simpa [Machine.PDstHolds, GprHolds, BitVec.setWidth_eq] using hd0.2
  have hfr' : T.mach.Frame T.gpr.condReads s s' (d :: T.frame.scratch) [] FlagMask.none := by
    simpa [tupDstGprs, tupFlatMap, PDst.gprs] using hfr
  have hxGpr : GprSym G (T.mach.getGpr s' d) (.var x) := by
    intro t v hmx
    have hti : t = i64 := (hA.defs x _ hdef).1 t v hmx
    subst hti
    obtain ⟨vb, hmb, rfl⟩ := (hA.defs x _ hdef).2 v hmx
    have hvb : T.mach.getGpr s rb = vb := by
      simpa [GprHolds, BitVec.setWidth_eq] using (hgb i64 vb hmb).2
    exact ⟨by decide, by rw [hrd, hvb, BitVec.setWidth_eq]⟩
  have hxLt : symArgScopeOk nv (.var x) = true := by
    have := hA.defs_lt x _ hdef
    simp only [symArgScopeOk, Nat.ble_eq]; omega
  have hA' : Agree T G nv
      { st with
        regs := (.var x, .gpr d) ::
          killRegs T.toIsa (d :: T.frame.scratch) [] FlagMask.none st.regs
        zeroExt32 := killZeroExt (d :: T.frame.scratch) st.zeroExt32
        scrConsts := [] } s' σ :=
    { hA with
      regs := fun p hp => (List.mem_cons.mp hp).elim
        (fun h => h ▸ hxGpr) (fun hp' => (kill_ok hA hfr' hp').1)
      regs_lt := fun p hp => (List.mem_cons.mp hp).elim
        (fun h => h ▸ hxLt) (fun hp' => (kill_ok hA hfr' hp').2)
      zeroExt32_ok := zeroExt32_frame hA hfr'
      flags_ok := hA.flags_ok.frame hfr' rfl
      scrConsts_ok := scrOk_nil _ _ _ }
  have hI' : Inv T hints s₀ ra n Rf m s' σ zl :=
    inv_of_frame hI hm hfr'.1 fun r hr =>
      (List.mem_cons.mp hr).elim (fun h => h ▸ isMoveGpr_of_alloc hd) isMoveGpr_scratch
  exact kont s' hA' hI'

theorem execShufMove_memDefs {I : Isa} {nslots : Nat} {saved : List I.Reg}
    {mv : ShufMove I.Reg I.VReg I.Cond} {st st' : SymState I} {deadHint : Bool}
    {c : List I.Directive}
    (h : execShufMove I nslots saved mv st deadHint = some (c, st')) :
    st'.memDefs = st.memDefs := by
  cases mv with
  | base m => exact execMove_memDefs h
  | rematAdd x base disp d =>
    simp only [execShufMove] at h
    repeat' (split at h <;> try (simp at h; done))
    obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, -, h⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at h; rw [← h.2]

theorem execShufMoves_memDefs {I : Isa} {nslots : Nat} {saved : List I.Reg} {deadHint : Bool} :
    ∀ {mvs : List (ShufMove I.Reg I.VReg I.Cond)} {st st' : SymState I} {c : List I.Directive},
    execShufMoves I nslots saved mvs st deadHint = some (c, st') → st'.memDefs = st.memDefs
  | [], _, _, _, h => by
    simp only [execShufMoves, Option.some.injEq, Prod.mk.injEq] at h
    exact congrArg SymState.memDefs h.2.symm
  | _ :: _, _, _, _, h => by
    simp only [execShufMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨⟨_, _⟩, h1, ⟨_, _⟩, h2, he⟩ := h
    simp only [Prod.mk.injEq] at he; rw [← he.2]
    exact (execShufMoves_memDefs h2).trans (execShufMove_memDefs h1)

theorem shuffle_memDefs {I : Isa} {nslots : Nat} {saved : List I.Reg} {st st' : SymState I}
    {tgts : List (SymArg × I.Loc)} {deadHint : Bool} {c : List I.Directive}
    (hs : shuffle I nslots saved st tgts deadHint = some (c, st')) : st'.memDefs = st.memDefs := by
  unfold shuffle at hs; split at hs
  · simp only [Option.some.injEq, Prod.mk.injEq] at hs; exact congrArg SymState.memDefs hs.2.symm
  · dsimp only at hs
    cases hem : execShufMoves I nslots saved
        (pmoveAux I nslots saved (3 * tgts.length + 4) st tgts []) st deadHint with
    | none => simp [hem] at hs
    | some p =>
      rcases p with ⟨code, st1⟩
      simp only [hem] at hs
      split at hs
      · simp only [Option.some.injEq, Prod.mk.injEq] at hs; rw [← hs.2]
        exact execShufMoves_memDefs hem
      · simp at hs

theorem execShufMove_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    {G : VCtx} {nv : Nat} {m : Mem 64} {mv : ShufMove T.Reg T.VReg T.Cond}
    {st st' : SymState T.toIsa} {deadHint : Bool} {c : List T.Directive} {k : Nat}
    {s : T.mach.MData} {σ : List (BitVec 64)}
    (he : execShufMove T.toIsa hints.nslots hints.saved mv st deadHint = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (kont : ∀ s' σ', Agree T G nv st' s' σ' → Inv T hints s₀ ra n Rf m s' σ' zl →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  cases mv with
  | base m' => exact execMove_ok hspE he hc hA hI kont
  | rematAdd x base disp d =>
    simp only [execShufMove] at he
    split at he; · simp at he
    rename_i hd
    have hd' : isAllocGpr T.toIsa hints.saved d = true := by simpa using hd
    cases hdef : st.defs.find? x with
    | none => rw [hdef] at he; cases he
    | some df =>
      rw [hdef] at he
      cases df with
      | addImm64 base' disp' =>
        dsimp only at he
        split at he
        · rename_i heq
          simp only [Bool.and_eq_true, Nat.beq_eq, beq_iff_eq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨rb, hrb, hrm⟩ := Option.bind_eq_some_iff.mp he
          obtain ⟨c0, hc0, hp⟩ := Option.map_eq_some_iff.mp hrm
          simp only [Prod.mk.injEq] at hp
          obtain ⟨rfl, rfl⟩ := hp
          exact rematAddImm64_ok hA hI hd' hdef hrb hc0 hc fun s' hA' hI' => kont s' σ hA' hI'
        · simp at he
      | _ => cases he

theorem execShufMoves_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp))
    {G : VCtx} {nv : Nat} {m : Mem 64} {deadHint : Bool} :
    ∀ (mvs : List (ShufMove T.Reg T.VReg T.Cond)) (st st' : SymState T.toIsa)
      (c : List T.Directive) (k : Nat) (s : T.mach.MData) (σ : List (BitVec 64)),
    execShufMoves T.toIsa hints.nslots hints.saved mvs st deadHint = some (c, st') →
    c.IsInfixAt (T.mach.prog host) k → Agree T G nv st s σ →
    Inv T hints s₀ ra n Rf m s σ zl →
    (∀ s' σ', Agree T G nv st' s' σ' → Inv T hints s₀ ra n Rf m s' σ' zl →
      T.mach.Run host (k + c.length) s' post) →
    T.mach.Run host k s post
  | [], st, st', c, k, s, σ, he, _, hA, hI, kont => by
    simp only [execShufMoves, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he; simpa using kont s σ hA hI
  | mv :: mvs, st, st', c, k, s, σ, he, hc, hA, hI, kont => by
    simp only [execShufMoves, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨⟨c1, st1⟩, h1, ⟨c2, st2⟩, h2, rfl, rfl⟩ := he
    have hc' := hc.append
    exact execShufMove_ok hspE h1 hc'.1 hA hI fun s1 σ1 hA1 hI1 =>
      execShufMoves_ok hspE mvs st1 st2 c2 (k + c1.length) s1 σ1 h2 hc'.2 hA1 hI1
        fun s2 σ2 hA2 hI2 => by simpa [Nat.add_assoc] using kont s2 σ2 hA2 hI2

theorem shuffle_ok {zl : Bool} (hspE : T.frameSpec.spEntry (T.mach.getGpr s₀ T.frame.sp)) {G : VCtx}
    {nv : Nat} {m : Mem 64} {st st' : SymState T.toIsa} {tgts : List (SymArg × T.toIsa.Loc)}
    {deadHint : Bool} {c : List T.Directive} {k : Nat} {s : T.mach.MData} {σ : List (BitVec 64)}
    (hs : shuffle T.toIsa hints.nslots hints.saved st tgts deadHint = some (c, st'))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ zl)
    (kont : ∀ s' σ', (∀ p ∈ tgts, LocOk T.mach G s' σ' p.1 p.2) → Agree T G nv st' s' σ' →
      Inv T hints s₀ ra n Rf m s' σ' zl → T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  unfold shuffle at hs; split at hs
  · rename_i hall
    simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
    simpa using kont s σ (fun ⟨_, _⟩ hp => holdsLoc_ok hA (List.all_eq_true.mp hall _ hp)) hA hI
  · dsimp only at hs; split at hs
    · simp at hs
    · rename_i code st'' he; split at hs
      · rename_i hall
        simp only [Option.some.injEq, Prod.mk.injEq] at hs; obtain ⟨rfl, rfl⟩ := hs
        exact execShufMoves_ok hspE _ st _ code k s σ he hc hA hI fun s' σ' hA' hI' =>
          kont s' σ' (fun ⟨_, _⟩ hp => holdsLoc_ok hA' (List.all_eq_true.mp hall _ hp)) hA' hI'
      · simp at hs

theorem tryRematDirect_ok {G : VCtx} {nv k : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {cl : FlagMask}
    (hA : Agree T G nv st s σ) (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hwp : code.wp (vals args₁) P) (hc : c.IsInfixAt (T.mach.prog host) k)
    (h : tryRematDirect T.toIsa st
      (recordDefC T.toIsa.gpr.addrCse st.defs code args) dsts = some (c, cl))
    (kont : ∀ s', (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs) ∧
        T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] cl →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  cases ts with
  | nil => simp [tryRematDirect] at h
  | cons t0 ts0 =>
    cases ts0 with
    | cons _ _ => simp [tryRematDirect] at h
    | nil =>
      cases t0 with
      | bits w =>
        by_cases hw : w = 64
        · subst hw
          rcases dsts with ⟨d0, ⟨⟩⟩
          cases d0 with
          | vec _ => simp [tryRematDirect] at h
          | gpr rd =>
            cases hd : recordDefC T.toIsa.gpr.addrCse st.defs code args with
            | none => simp [tryRematDirect, hd] at h
            | some df =>
              cases df with
              | addImm64 base disp =>
                simp only [tryRematDirect, hd] at h
                obtain ⟨rb, hrb, hrm⟩ := Option.bind_eq_some_iff.mp h
                obtain ⟨c0, hc0, hp⟩ := Option.map_eq_some_iff.mp hrm
                simp only [Prod.mk.injEq] at hp
                obtain ⟨rfl, rfl⟩ := hp
                obtain ⟨w', hw', rvs, hP, hdef⟩ :=
                  recordDefC_elide_ok hA.defs hargs hA.ctx_lt hwp hd
                have h64 : w' = 64 := by cases hw'; rfl
                subst h64
                rcases rvs with ⟨rv, ⟨⟩⟩
                obtain ⟨hrb_ns, hgb⟩ := findGprFor_ok hA hrb
                have hbase_lt : base < nv := findGprFor_var_lt hA hrb
                obtain ⟨vb, hmb', hrv⟩ := hdef.2 rv (by simp [Tup.zip, Tup.levels])
                have hmb : ⟨i64, vb, base⟩ ∈ G := by
                  rcases List.mem_cons.mp hmb' with h | h
                  · cases h; exact absurd hbase_lt (Nat.lt_irrefl _)
                  · exact h
                have hvb : T.mach.getGpr s rb = vb := by
                  simpa [GprHolds, BitVec.setWidth_eq] using (hgb i64 vb hmb).2
                have hop := rematAddImm64_spec hc0
                have hpa : ∀ r ∈ tupArgGprs (V := T.VReg) (C := T.Cond) (ts := [.bits 64, .bits 64])
                    (PArg.gpr rb, PArg.imm disp, ()), r ∉ T.frame.scratch := by
                  intro r hr; simp [tupArgGprs, tupFlatMap, PArg.gprs] at hr; subst hr; exact hrb_ns
                have hrel : TRel (T.mach.PArgHolds s) (as := [.bits 64, .bits 64])
                    (PArg.gpr rb, PArg.imm disp, ()) (vb, disp, ()) := by
                  refine .cons ?_ (.cons rfl .nil)
                  exact ⟨by decide, by rw [hvb, BitVec.setWidth_eq]⟩
                have hwp' : (OpCode.add (.bits 64)).wp (vb, disp, ())
                    (fun rvs => rvs = (vb + disp, ())) := by
                  simp [OpCode.wp, lift2, Ty.hasFloat]
                refine T.gprSpec.op_spec hop hpa hdg hrel hwp' hc
                  fun s' ⟨⟨rvs', hrvs', hdh'⟩, hm⟩ hfr => ?_
                subst hrvs'; rw [← hrv] at hdh'
                exact kont s' ⟨⟨(rv, ()), hP, hdh'⟩, hm⟩ hfr
              | _ => simp [tryRematDirect, hd] at h
        · unfold tryRematDirect at h; split at h
          · cases ‹[Ty.bits w] = [Ty.bits 64]›; exact absurd rfl hw
          · simp at h
      | _ => simp [tryRematDirect] at h

private theorem evalBits_eq_ne_add_sub {co : CmpOp} (hco : co = .eq ∨ co = .ne)
    (vb disp c : BitVec 64) :
    co.evalBits (vb + disp) c = co.evalBits vb (c - disp) ∧
    co.evalBits c (vb + disp) = co.evalBits vb (c - disp) := by
  have heq : (vb + disp == c) = (vb == c - disp) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    constructor
    · intro h; rw [← h]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add]; omega
    · intro h; rw [h, BitVec.sub_add_cancel]
  have heq2 : (c == vb + disp) = (vb == c - disp) := by
    rw [← heq]; apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; exact eq_comm
  rcases hco with rfl | rfl
  · exact ⟨heq, heq2⟩
  · have h1 : CmpOp.ne.evalBits (vb + disp) c = !(vb + disp == c) := rfl
    have h2 : CmpOp.ne.evalBits c (vb + disp) = !(c == vb + disp) := rfl
    have h3 : CmpOp.ne.evalBits vb (c - disp) = !(vb == c - disp) := rfl
    rw [h1, h2, h3, heq, heq2]; exact ⟨rfl, rfl⟩

theorem tryRematCmpEqImm_ok {G : VCtx} {nv k : Nat} {st : SymState T.toIsa} {vh : VariantHint}
    {s : T.mach.MData} {σ : List (BitVec 64)} {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {cl : FlagMask}
    (hA : Agree T G nv st s σ) (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hwp : code.wp (vals args₁) P) (hc : c.IsInfixAt (T.mach.prog host) k)
    (h : tryRematCmpEqImm T.toIsa st vh code args dsts = some (c, cl))
    (kont : ∀ s', (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs) ∧
        T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] cl →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  cases code with
  | cmp co ty mty hmty =>
    cases ty with
    | bits w =>
      cases mty with
      | bool =>
        by_cases hw : w = 64
        · subst hw
          rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
          simp only [tryRematCmpEqImm] at h
          split at h; · simp at h
          rename_i hco_b
          have hco : co = .eq ∨ co = .ne := by cases co <;> simp at hco_b ⊢
          rcases hargs with _ | ⟨ha, _ | ⟨hb, -⟩⟩
          have step : ∀ (x : Nat) (vx imm : BitVec 64) (hmx : ⟨i64, vx, x⟩ ∈ G)
              (hres : co.evalBits a₁.val b₁.val = co.evalBits vx imm →
                P (co.evalBits vx imm, ()))
              (hEq : co.evalBits a₁.val b₁.val = co.evalBits vx imm),
              (if (findGprFor T.toIsa true st.regs (.var x)).isSome then none
               else (rematBaseOf? T.toIsa st x).bind fun (_, disp, rb) =>
                 T.gpr.op (.cmp co (.bits 64)) (.gpr rb, .imm (imm - disp), ()) (pd, ()) vh) =
              some (c, cl) → T.mach.Run host k s post := by
            intro x vx imm hmx hP_ev hEq hrun
            split at hrun; · simp at hrun
            obtain ⟨⟨base, disp, rb⟩, hrem, hop⟩ := Option.bind_eq_some_iff.mp hrun
            obtain ⟨hdef, hrb⟩ := rematBaseOf?_spec hrem
            obtain ⟨vb, hmb, hvx⟩ := (hA.defs x _ hdef).2 vx hmx
            obtain ⟨hrb_ns, hgb⟩ := findGprFor_ok hA hrb
            have hvb : T.mach.getGpr s rb = vb := by
              simpa [GprHolds, BitVec.setWidth_eq] using (hgb i64 vb hmb).2
            have hpa : ∀ r ∈ tupArgGprs (V := T.VReg) (C := T.Cond) (ts := [.bits 64, .bits 64])
                (PArg.gpr rb, PArg.imm (imm - disp), ()), r ∉ T.frame.scratch := by
              intro r hr; simp [tupArgGprs, tupFlatMap, PArg.gprs] at hr; subst hr; exact hrb_ns
            have hrel : TRel (T.mach.PArgHolds s) (as := [.bits 64, .bits 64])
                (PArg.gpr rb, PArg.imm (imm - disp), ()) (vb, imm - disp, ()) := by
              refine .cons ?_ (.cons rfl .nil)
              exact ⟨by decide, by rw [hvb, BitVec.setWidth_eq]⟩
            have hP' : P (co.evalBits vb (imm - disp), ()) := by
              rw [← (evalBits_eq_ne_add_sub hco vb disp imm).1, ← hvx]; exact hP_ev hEq
            have hwp' : (OpCode.cmp co (.bits 64)).wp (vb, imm - disp, ()) P := by
              simpa [OpCode.wp, lift2, liftCmp] using hP'
            exact T.gprSpec.op_spec hop hpa hdg hrel hwp' hc kont
          simp only [OpCode.wp_cmp, vals, liftCmp, Ty.hasFloat, Bool.false_eq_true,
            ite_false, cast_eq] at hwp
          cases a with
          | var x =>
            cases b with
            | imm imm =>
              cases ha with | var hmx => cases hb with | imm =>
              rename_i vx
              exact step x vx imm hmx (fun _ => hwp) rfl h
            | var _ => simp at h
          | imm imm =>
            cases b with
            | var x =>
              cases ha with | imm => cases hb with | var hmx =>
              rename_i vx
              have hcomm : co.evalBits imm vx = co.evalBits vx imm := by
                have heq : (imm == vx) = (vx == imm) := by
                  apply Bool.eq_iff_iff.mpr; simp only [beq_iff_eq]; exact eq_comm
                rcases hco with rfl | rfl
                · exact heq
                · change (!(imm == vx)) = !(vx == imm); rw [heq]
              exact step x vx imm hmx (fun he => by rw [← he]; exact hwp) hcomm h
            | imm _ => simp at h
        · unfold tryRematCmpEqImm at h; split at h
          · cases ‹[Ty.bits w, Ty.bits w] = [Ty.bits 64, Ty.bits 64]›; exact absurd rfl hw
          · simp at h
      | _ => simp [tryRematCmpEqImm] at h
    | _ => simp [tryRematCmpEqImm] at h
  | _ => simp [tryRematCmpEqImm] at h

theorem tryRematAdd64SameDst_ok {G : VCtx} {nv k : Nat} {st : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg Val) sig} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst T.Reg T.VReg T.Cond) ts} {P : Tup Val ts → Prop}
    {c : List T.Directive} {cl : FlagMask}
    (hA : Agree T G nv st s σ) (hargs : TRel (ArgRel G) args₁ args)
    (hdg : ∀ r ∈ tupDstGprs dsts, r ∉ T.frame.scratch)
    (hwp : code.wp (vals args₁) P) (hc : c.IsInfixAt (T.mach.prog host) k)
    (h : tryRematAdd64SameDst T.toIsa st code args dsts = some (c, cl))
    (kont : ∀ s', (∃ rvs, P rvs ∧ TRel (T.mach.PDstHolds s') dsts rvs) ∧
        T.mach.mem s' = T.mach.mem s →
      T.mach.Frame T.gpr.condReads s s' (tupDstGprs dsts ++ T.frame.scratch) [] cl →
      T.mach.Run host (k + c.length) s' post) :
    T.mach.Run host k s post := by
  cases code with
  | add ty =>
    cases ty with
    | bits w =>
      by_cases hw : w = 64
      · subst hw
        rcases args with ⟨a, b, ⟨⟩⟩; rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩; rcases dsts with ⟨d0, ⟨⟩⟩
        cases a with
        | imm _ => simp [tryRematAdd64SameDst] at h
        | var x =>
          cases b with
          | imm _ => simp [tryRematAdd64SameDst] at h
          | var y =>
            cases d0 with
            | vec _ => simp [tryRematAdd64SameDst] at h
            | gpr rd =>
              simp only [tryRematAdd64SameDst] at h
              rcases hargs with _ | ⟨ha, _ | ⟨hb, -⟩⟩
              cases ha with | var hmx => cases hb with | var hmy =>
              rename_i vx vy
              simp only [OpCode.wp_add, vals, Arg.val, lift2, Ty.hasFloat, Bool.false_eq_true,
                ite_false] at hwp
              have run_ok : ∀ (remVar otherVar : Nat) (vrem voth : BitVec 64),
                  ⟨i64, vrem, remVar⟩ ∈ G → ⟨i64, voth, otherVar⟩ ∈ G →
                  vrem + voth = vx + vy →
                  (if (findGprFor T.toIsa true st.regs (.var remVar)).isSome then none
                   else (rematBaseOf? T.toIsa st remVar).bind fun (_, disp, rb) =>
                     (findGprFor T.toIsa true st.regs (.var otherVar)).bind fun ry =>
                       (T.gpr.op (.add (.bits 64)) (.gpr rb, .gpr ry, ())
                           (.gpr rd, ()) .default).bind
                         fun (c1, cl1) =>
                           (rematAddImm64 T.toIsa rd rd disp).map fun c2 => (c1 ++ c2, cl1)) =
                  some (c, cl) → T.mach.Run host k s post := by
                intro remVar otherVar vrem voth hmrem hmoth hsum hrun
                split at hrun; · simp at hrun
                obtain ⟨⟨base, disp, rb⟩, hrem, hrun⟩ := Option.bind_eq_some_iff.mp hrun
                obtain ⟨ry, hry, hrun⟩ := Option.bind_eq_some_iff.mp hrun
                obtain ⟨⟨c1, cl1⟩, hop1, hrun⟩ := Option.bind_eq_some_iff.mp hrun
                obtain ⟨c2, hrm2, hp⟩ := Option.map_eq_some_iff.mp hrun
                simp only [Prod.mk.injEq] at hp
                obtain ⟨rfl, rfl⟩ := hp
                obtain ⟨hdef, hrb⟩ := rematBaseOf?_spec hrem
                obtain ⟨vb, hmb, hvrem⟩ := (hA.defs remVar _ hdef).2 vrem hmrem
                obtain ⟨hrb_ns, hgb⟩ := findGprFor_ok hA hrb
                obtain ⟨hry_ns, hgy⟩ := findGprFor_ok hA hry
                have hvb : T.mach.getGpr s rb = vb := by
                  simpa [GprHolds, BitVec.setWidth_eq] using (hgb i64 vb hmb).2
                have hvoth : T.mach.getGpr s ry = voth := by
                  simpa [GprHolds, BitVec.setWidth_eq] using (hgy i64 voth hmoth).2
                have hpa1 : ∀ r ∈ tupArgGprs (V := T.VReg) (C := T.Cond)
                    (ts := [.bits 64, .bits 64]) (PArg.gpr rb, PArg.gpr ry, ()),
                    r ∉ T.frame.scratch := by
                  intro r hr; simp [tupArgGprs, tupFlatMap, PArg.gprs] at hr
                  rcases hr with rfl | rfl <;> assumption
                have hrel1 : TRel (T.mach.PArgHolds s) (as := [.bits 64, .bits 64])
                    (PArg.gpr rb, PArg.gpr ry, ()) (vb, voth, ()) := by
                  refine .cons ?_ (.cons ?_ .nil)
                  · exact ⟨by decide, by rw [hvb, BitVec.setWidth_eq]⟩
                  · exact ⟨by decide, by rw [hvoth, BitVec.setWidth_eq]⟩
                have hwp1 : (OpCode.add (.bits 64)).wp (vb, voth, ())
                    (fun rvs => rvs = (vb + voth, ())) := by
                  simp [OpCode.wp, lift2, Ty.hasFloat]
                have hc' := hc.append
                refine T.gprSpec.op_spec hop1 hpa1 hdg hrel1 hwp1 hc'.1
                  fun s1 ⟨⟨rvs1, hrvs1, hdh1⟩, hm1⟩ hfr1 => ?_
                subst hrvs1
                rcases hdh1 with _ | ⟨hd1, -⟩
                have hrd1 : T.mach.getGpr s1 rd = vb + voth := by
                  simpa [Machine.PDstHolds, GprHolds, BitVec.setWidth_eq] using hd1.2
                have hop2 := rematAddImm64_spec hrm2
                have hrd_ns : rd ∉ T.frame.scratch := hdg rd (by simp [tupDstGprs])
                have hpa2 : ∀ r ∈ tupArgGprs (V := T.VReg) (C := T.Cond)
                    (ts := [.bits 64, .bits 64]) (PArg.gpr rd, PArg.imm disp, ()),
                    r ∉ T.frame.scratch := by
                  intro r hr; simp [tupArgGprs, tupFlatMap, PArg.gprs] at hr
                  subst hr; exact hrd_ns
                have hrel2 : TRel (T.mach.PArgHolds s1) (as := [.bits 64, .bits 64])
                    (PArg.gpr rd, PArg.imm disp, ()) (vb + voth, disp, ()) := by
                  refine .cons ?_ (.cons rfl .nil)
                  exact ⟨by decide, by rw [hrd1, BitVec.setWidth_eq]⟩
                have hwp2 : (OpCode.add (.bits 64)).wp (vb + voth, disp, ())
                    (fun rvs => rvs = ((vb + voth) + disp, ())) := by
                  simp [OpCode.wp, lift2, Ty.hasFloat]
                refine T.gprSpec.op_spec hop2 hpa2 hdg hrel2 hwp2 hc'.2
                  fun s2 ⟨⟨rvs2, hrvs2, hdh2⟩, hm2⟩ hfr2 => ?_
                subst hrvs2
                have hval : (vb + voth) + disp = vx + vy := by
                  rw [← hsum, hvrem]; ac_rfl
                rw [hval] at hdh2
                have hfr12 : T.mach.Frame T.gpr.condReads s s2
                    (tupDstGprs (V := T.VReg) (C := T.Cond) (ts := [.bits 64])
                      (PDst.gpr rd, ()) ++ T.frame.scratch) [] cl1 :=
                  ⟨fun r hr => (hfr2.1 r hr).trans (hfr1.1 r hr),
                   fun v hv => (hfr2.2.1 v hv).trans (hfr1.2.1 v hv),
                   fun cc hcc => (hfr2.2.2 cc (by simp [FlagMask.disjoint, FlagMask.none])).trans
                     (hfr1.2.2 cc hcc)⟩
                simpa [List.length_append, Nat.add_assoc] using
                  kont s2 ⟨⟨(vx + vy, ()), hwp, hdh2⟩, hm2.trans hm1⟩ hfr12
              rcases orElse_eq_some h with h1 | h2
              · exact run_ok x y vx vy hmx hmy rfl h1
              · exact run_ok y x vy vx hmy hmx (BitVec.add_comm _ _) h2
      · unfold tryRematAdd64SameDst at h; split at h
        · cases ‹[Ty.bits w] = [Ty.bits 64]›; exact absurd rfl hw
        · simp at h
    | _ => simp [tryRematAdd64SameDst] at h
  | _ => simp [tryRematAdd64SameDst] at h

theorem findMissingRematArg_ok {I : Isa} {st : SymState I} {x base : Nat} {disp : BitVec 64}
    {rb : I.Reg} {sig : List Ty} {args : Tup (Arg VNat) sig}
    (h : findMissingRematArg I st args = some (x, base, disp, rb)) :
    st.defs.find? x = some (.addImm64 base disp) ∧
    findGprFor I true st.regs (.var base) = some rb := by
  induction sig with
  | nil => rcases args with ⟨⟩; simp [findMissingRematArg] at h
  | cons t ts ih =>
    rcases args with ⟨a, as⟩
    simp only [findMissingRematArg] at h
    split at h
    · rename_i y
      split at h
      · cases hrem : rematBaseOf? I st y with
        | some p =>
          rcases p with ⟨b', d', r'⟩
          rw [hrem] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          exact rematBaseOf?_spec hrem
        | none => rw [hrem] at h; exact ih h
      · exact ih h
    · exact ih h

theorem rematTempCands_isAllocGpr {I : Isa} {saved : List I.Reg} {st : SymState I} {ts : List Ty}
    {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {tmp : I.Reg}
    (hdg : ∀ r ∈ tupDstGprs dsts, isAllocGpr I saved r = true)
    (hmem : tmp ∈ rematTempCands I saved st dsts) :
    isAllocGpr I saved tmp = true := by
  unfold rematTempCands at hmem
  rcases List.mem_append.mp hmem with h1 | h2
  · cases ts with
    | nil => simp at h1
    | cons t0 ts0 =>
      cases ts0 with
      | cons _ _ => simp at h1
      | nil =>
        rcases dsts with ⟨d0, ⟨⟩⟩
        cases d0 with
        | gpr rd =>
          simp only [List.mem_singleton] at h1; subst h1
          exact hdg tmp (by simp [tupDstGprs, tupFlatMap, PDst.gprs])
        | vec _ | flag _ => simp at h1
  · simp only [List.mem_filter, List.mem_append] at h2
    rcases h2.1 with ha | hs
    · simp [isAllocGpr, ha]
    · simp [isAllocGpr, hs]

theorem rematAddImm64_clean {I : Isa} (hcl : LabelClean I) {rb rd : I.Reg} {disp : BitVec 64}
    {c : List I.Directive} (h : rematAddImm64 I rb rd disp = some c) : NoLab I c :=
  hcl.op _ _ _ _ _ _ (rematAddImm64_spec h)

theorem tryRematDirect_clean {I : Isa} (hcl : LabelClean I) {st : SymState I}
    {df? : Option DefFact} {ts : List Ty} {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts}
    {c : List I.Directive} {cl : FlagMask}
    (h : tryRematDirect I st df? dsts = some (c, cl)) : NoLab I c := by
  unfold tryRematDirect at h
  split at h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, hrm, hp⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hp; rw [← hp.1]
    exact rematAddImm64_clean hcl hrm
  · simp at h

theorem tryRematCmpEqImm_clean {I : Isa} (hcl : LabelClean I) {st : SymState I} {vh : VariantHint}
    {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {c : List I.Directive} {cl : FlagMask}
    (h : tryRematCmpEqImm I st vh code args dsts = some (c, cl)) : NoLab I c := by
  unfold tryRematCmpEqImm at h
  split at h
  · split at h; · simp at h
    split at h
    · dsimp only at h; split at h; · simp at h
      obtain ⟨_, -, hop⟩ := Option.bind_eq_some_iff.mp h
      exact hcl.op _ _ _ _ _ _ hop
    · dsimp only at h; split at h; · simp at h
      obtain ⟨_, -, hop⟩ := Option.bind_eq_some_iff.mp h
      exact hcl.op _ _ _ _ _ _ hop
    · simp at h
  · simp at h

theorem tryRematAdd64SameDst_clean {I : Isa} (hcl : LabelClean I) {st : SymState I}
    {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg VNat) sig}
    {dsts : Tup (PDst I.Reg I.VReg I.Cond) ts} {c : List I.Directive} {cl : FlagMask}
    (h : tryRematAdd64SameDst I st code args dsts = some (c, cl)) : NoLab I c := by
  unfold tryRematAdd64SameDst at h
  split at h
  · rcases orElse_eq_some h with h1 | h1 <;> (
      dsimp only at h1; split at h1; · simp at h1
      obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨_, -, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨⟨c1, cl1⟩, hop1, h1⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨c2, hrm2, hp⟩ := Option.map_eq_some_iff.mp h1
      simp only [Prod.mk.injEq] at hp; rw [← hp.1]
      exact fun l hl => (List.mem_append.mp hl).elim
        (hcl.op _ _ _ _ _ _ hop1 l) (rematAddImm64_clean hcl hrm2 l))
  · simp at h

end Lemmas
end Rega
end LeanQbe.T
