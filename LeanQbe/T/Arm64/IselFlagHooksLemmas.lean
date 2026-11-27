module

public import LeanQbe.T.Arm64.IselLemmas3

/-!
# AArch64 Flag-Reuse & `jnzGprInv?` Specification Proofs (`Arm64.IselFlagHooksLemmas`)

Verifies the 5 flag-reuse and branch-inversion contracts on `LeanQbe.T.Arm64.armGpr`:
* `armJnzGprInv_noLab` & `armJnzGprInv_spec`: `TBZ`/`TBNZ w_r, #0, l` (including `.SP` via `.X16`).
* `armBoolFlagOut_spec`: `.copy .bool` and `.not .bool` from `.flag` preserve NZCV across `CSET`.
* `armCmpFlagsOut_spec`: integer comparisons produce full `FlagCmpOk ... false` flags in the exact
  operand order reported by `armCmpFlagsOut`.
* `armTestOp_boolFlag_spec` & `armTestMem_boolFlag_spec`: `ANDS` bit-tests leave `.eq`/`.ne` flags.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

private theorem bool_getLsbD_zero' {v : BitVec 64} {b : Bool}
    (hb : GprHolds v .bool b) : (v.setWidth 32).getLsbD 0 = b := by
  simp only [GprHolds] at hb
  have h0 : (v.setWidth 32).getLsbD 0 = (v.setWidth 8).getLsbD 0 := by simp
  rw [h0, hb]
  cases b <;> decide

/-- Label-freedom of `armJnzGprInv`. -/
theorem armJnzGprInv_noLab (r : Reg) (inv : Bool) (tgt l : Sym) :
    Kraken.Directive.label l ∉ (armJnzGprInv r inv tgt).1 :=
  emitClean_noLab _ l

/-- Soundness specification matching `GprTarget.jnzGprInv_spec` for `armGpr`. -/
theorem armJnzGprInv_spec {fn : Reg → Bool → Sym → List Directive × FlagMask}
    {h : Host} {k j : Nat} {r : Reg} {inv : Bool} {l : Sym} {b : Bool}
    {s : MachineData} {post : MachineState → Prop}
    (hfn : armGpr.jnzGprInv? = some fn)
    (hc : (fn r inv l).1.IsInfixAt (armMach.prog h) k)
    (hl : armMach.labelAddr h l = armMach.addrOf h j)
    (_ : r ∉ armScratch) (hb : GprHolds (armMach.getGpr s r) .bool b)
    (hk : ∀ s', armMach.Frame armCondReads s s' armScratch [] (fn r inv l).2 →
      s'.dmem = s.dmem →
      ((if inv then !b else b) = true → armMach.Run h j s' post) ∧
      ((if inv then !b else b) = false → armMach.Run h (k + (fn r inv l).1.length) s' post)) :
    armMach.Run h k s post := by
  dsimp only [armGpr] at hfn
  cases hfn
  letI := h
  have hl' : Labels.label l = Host.addrOf j := hl
  have stepBr : ∀ {k' : Nat} {x : XReg} {s' : MachineData} {post' : MachineState → Prop},
      [Kraken.Directive.instr (armJnzBit0I inv x l)].IsInfixAt Host.prog k' →
      ((s'.regs.getXReg x).toBitVec.setWidth 32).getLsbD 0 = b →
      ((if inv then !b else b) = true → armMach.Run h j s' post') →
      ((if inv then !b else b) = false → armMach.Run h (k' + 1) s' post') →
      armMach.Run h k' s' post' := by
    intro k' x s' post' hinf hxbit ht hf
    cases inv
    · refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hinf) ?_
      cases b <;>
        simp only [armJnzBit0I, armIselInsI, t_step_simp, hxbit] at ht hf ⊢
      · exact hf rfl
      · rw [hl']; exact ht rfl
    · refine Host.eventually_of_interp_cps (List.isInfixAt_singleton.mp hinf) ?_
      cases b <;>
        simp only [armJnzBit0I, armIselInsI, t_step_simp, hxbit] at ht hf ⊢
      · rw [hl']; exact ht rfl
      · exact hf rfl
  cases r with
  | reg x =>
    have hc' : [Kraken.Directive.instr (armJnzBit0I inv x l)].IsInfixAt Host.prog k := by
      simpa [armJnzGprInv, armJnzGprInvIns, emitClean] using hc
    have hrun := hk s (Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone) rfl
    have hlen : (armJnzGprInv (.reg x) inv l).1.length = 1 := rfl
    rw [hlen] at hrun
    exact stepBr hc' (bool_getLsbD_zero' (by simpa [armMach, get_reg] using hb)) hrun.1 hrun.2
  | SP =>
    have hc' : ([armMovToX .X16 .SP] ++
        [Kraken.Directive.instr (armJnzBit0I inv .X16 l)]).IsInfixAt Host.prog k := by
      simpa [armJnzGprInv, armJnzGprInvIns, emitClean] using hc
    have hpair := hc'.append
    have hrun1 : @Program.wp h [armMovToX .X16 .SP] (fun s' => s' = wr s .X16 (get s .SP))
        (fun _ _ => False) s := armMovToX_wp .X16 .SP s
    refine eventually_trans _ _ _ _ (hrun1 k hpair.1) ?_
    rintro ⟨s₁, a⟩ (⟨ha, rfl⟩ | hf)
    · dsimp only at ha; subst ha
      have hbit : (((wr s .X16 (get s .SP)).regs.getXReg .X16).toBitVec.setWidth 32).getLsbD 0 =
          b := by
        rw [← get_reg, get_wr_same]; exact bool_getLsbD_zero' hb
      have hfr : armMach.Frame armCondReads s (wr s .X16 (get s .SP)) armScratch []
          (armJnzGprInv .SP inv l).2 :=
        frame_wr .X16 (get s .SP) List.mem_cons_self maskNone
      have hrun := hk _ hfr rfl
      have hlen : (armJnzGprInv .SP inv l).1.length = 2 := rfl
      rw [show armMach.Run h (k + (armJnzGprInv .SP inv l).1.length)
            (wr s .X16 (get s .SP)) post =
          armMach.Run h (k + 1 + 1) (wr s .X16 (get s .SP)) post from by
        rw [hlen]] at hrun
      exact stepBr hpair.2 hbit hrun.1 hrun.2
    · exact False.elim hf

/-- Flag-preservation specification matching `GprTarget.op_boolFlag_spec` for `armGpr`. -/
theorem armBoolFlagOut_spec {h : Host} {k : Nat} {sig : List Ty}
    {code : OpCode sig [.bool]} {pas : Tup (PArg Reg Empty ArmCond) sig}
    {pd : PDst Reg Empty ArmCond .bool} {cnd : ArmCond} {vh : VariantHint}
    {c : List Directive} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val [.bool] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hfl : armGpr.boolFlagOut? code pas pd = some cnd)
    (hc0 : armGpr.op code pas (pd, ()) vh = some (c, clob))
    (_hargs : ∀ r ∈ tupArgGprs pas, r ∉ armScratch)
    (_hdst : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (hvs : TRel (armMach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    armMach.FallsTo armGpr.condReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' => (∃ b : Bool, P (b, ()) ∧ armMach.PDstHolds s' .bool pd b ∧
          armMach.evalCond s' cnd = b) ∧
        armMach.mem s' = armMach.mem s) post := by
  dsimp only [armGpr, armBoolFlagOut, armOp] at hfl hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  cases pd with
  | vec v => exact v.elim
  | flag _ => simp at hfl
  | gpr r => cases r with
    | SP => simp at hfl
    | reg d =>
      cases code with
      | copy =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        cases pa with
        | gpr _ | imm _ => cases hfl
        | vec v => exact v.elim
        | flag cf =>
          cases hfl
          dsimp only [armOpIns, armBoolOpIns] at hc
          rcases Option.some.inj hc with ⟨rfl, rfl⟩
          have hcond : cnd.interp s.status = va := (trel1_inv hvs)
          dsimp only [OpCode.wp] at hwp
          refine armFallsTo_of_wp ?_
          simp only [emitClean_cons, emitClean_nil]
          refine armWp_mono (armCset64_wp d cnd s) ?_
          rintro s' rfl
          refine ⟨⟨⟨va, hwp, ?_, hcond⟩, rfl⟩, ?_⟩
          · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hcond]; cases va <;> rfl
          · exact frame_wr d _ List.mem_cons_self maskNone
      | not =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        cases pa with
        | gpr _ | imm _ => cases hfl
        | vec v => exact v.elim
        | flag cf =>
          cases hfl
          dsimp only [armOpIns, armBoolOpIns] at hc
          rcases Option.some.inj hc with ⟨rfl, rfl⟩
          have hcond : cf.interp s.status = va := (trel1_inv hvs)
          have hneg : (armNegCond cf).interp s.status = !va := by
            rw [armNegCond_interp, hcond]
          dsimp only [OpCode.wp] at hwp
          refine armFallsTo_of_wp ?_
          simp only [emitClean_cons, emitClean_nil]
          refine armWp_mono (armCset64_wp d (armNegCond cf) s) ?_
          rintro s' rfl
          refine ⟨⟨⟨!va, hwp, ?_, hneg⟩, rfl⟩, ?_⟩
          · simp only [Machine.PDstHolds, GprHolds, get_wr_same, hneg]; cases va <;> rfl
          · exact frame_wr d _ List.mem_cons_self maskNone
      | _ => cases hfl

/-- Compare-flags preservation specification matching `GprTarget.op_cmpFlags_spec` for `armGpr`. -/
theorem armCmpFlagsOut_spec {h : Host} {k : Nat} {co : CmpOp} {n : Nat}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {pd : PDst Reg Empty ArmCond .bool}
    {lhsFirst : Bool} {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec n} {s : MachineData} {post : MachineState → Prop}
    (hfl : armGpr.cmpFlagsOut? co n pa pb pd = some lhsFirst)
    (hc0 : armGpr.op (.cmp co (.bits n) .bool rfl) (pa, pb, ()) (pd, ()) vh = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ armScratch)
    (hdst : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    armMach.FallsTo armGpr.condReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' => armMach.PDstHolds s' .bool pd (co.evalBits va vb) ∧
        FlagCmpOk armMach armGpr s' (if lhsFirst then va else vb) (if lhsFirst then vb else va)
          false ∧
        armMach.mem s' = armMach.mem s) post := by
  dsimp only [armGpr, armOp] at hfl hc0 ⊢
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  dsimp only [armOpIns] at hc
  have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_left _ hr)
  have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_right _ hr)
  have hdst' : ∀ r ∈ tupDstGprs (ts := [.bool]) (pd, ()), r ∉ armScratch := by
    simpa [tupDstGprs] using hdst
  refine armFallsTo_of_wp (armWp_mono (armCmpOp_wp co pa pb pd hc hga hgb hdst' hpa hpb) ?_)
  rintro s' ⟨hpd, hfc, hdm, hfr⟩
  rw [show tupDstGprs (ts := [.bool]) (pd, ()) = pd.gprs by simp [tupDstGprs]] at hfr
  exact ⟨⟨hpd, hfc hfl, hdm⟩, hfr⟩

/-- Bit-test flag reuse specification matching `GprTarget.testOp_boolFlag_spec` for `armGpr`. -/
theorem armTestOp_boolFlag_spec (_ : armGpr.hasTestFlags = true)
    {h : Host} {k n : Nat} {neg : Bool}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {pd : PDst Reg Empty ArmCond .bool}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec n} {cnd : ArmCond}
    {s : MachineData} {post : MachineState → Prop}
    (hcl : clob ≠ FlagMask.none)
    (hcc : armGpr.condOfCmp? (if neg then .ne else .eq) = some cnd)
    (hc0 : armGpr.testOp n neg pa pb pd = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ armScratch)
    (hd : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (hpa : armMach.PArgHolds s (.bits n) pa va) (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    armMach.FallsTo armGpr.condReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#n
        armMach.PDstHolds s' .bool pd res ∧ armMach.evalCond s' cnd = res ∧
        armMach.mem s' = armMach.mem s) post := by
  have hcond : cnd = if neg then .ne else .eq := by
    cases neg <;> simp only [Function.comp_def, armCmpCond, Option.some.injEq] at hcc <;>
      exact hcc.symm
  subst hcond
  refine armFallsTo_of_wp (armWp_mono (armTestOp_wp neg pa pb pd hc0 hargs hd hpa hpb) ?_)
  rintro s' ⟨⟨hpd, _, hst⟩, hdm, hfr⟩
  exact ⟨⟨hpd, hst hcl, hdm⟩, hfr⟩

/-- Vacuous memory-test flag reuse specification (`armGpr.testMem = none`). -/
theorem armTestMem_boolFlag_spec (_ : armGpr.hasTestFlags = true)
    {h : Host} {k w : Nat} {neg : Bool} {a : AddrArg Reg} {pb : PArg Reg Empty ArmCond (.bits w)}
    {pd : PDst Reg Empty ArmCond .bool} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec w} {cnd : ArmCond} {s : MachineData} {post : MachineState → Prop}
    (_hcl : clob ≠ FlagMask.none)
    (_hcc : armGpr.condOfCmp? (if neg then .ne else .eq) = some cnd)
    (hc : armGpr.testMem w neg a pb pd = some (c, clob)) :
    (∀ r ∈ a.regs ++ pb.gprs, r ∉ armScratch) → (∀ r ∈ pd.gprs, r ∉ armScratch) →
    loadVal (armMach.mem s) (.bits w) (a.eval (armMach.getGpr s)) = some va →
    armMach.PArgHolds s (.bits w) pb vb →
    armMach.FallsTo armGpr.condReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' =>
        let res := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w
        armMach.PDstHolds s' .bool pd res ∧ armMach.evalCond s' cnd = res ∧
        armMach.mem s' = armMach.mem s) post := by
  cases hc

end LeanQbe.T.Arm64
