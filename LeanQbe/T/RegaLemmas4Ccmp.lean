module

public import LeanQbe.T.RegaLemmas4Base

/-!
# Wave 6.2-B `CCMP`/`CCMN` Chain Verification Helpers

Verified short-circuit `CCMP`/`CCMN` chain lowering (`CcmpJumpReady`, `CcmpMotive`,
`CcmpJnzMotive`, `ccmpStart_ok`, `ccmpMotive_let`, `ccmpMotive_jnz`, `ccmpJnzMotive_jnz`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace Rega

section Main
variable {T : Target} {host : T.mach.Host} {hints : T.toIsa.Hints} {E : Ext} {Γ : Env} {fn : Sym}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n nX : Nat} {Rf : Mem 64 → Prop} {bound : Sym → Nat}
  {rs : List Ty} {Q : Post rs} {X : XPost}

/-- State `s` is ready to branch to `targetJ` (whose label is at `kT`) through any subsequent
scratch/flag-only `ccmp` frames while preserving memory. -/
@[expose]
def CcmpJumpReady (T : Target) (host : T.mach.Host) (fn : Sym)
    (s₀ : T.mach.MData) (ra : T.mach.Addr) (n nX : Nat) (Rf : Mem 64 → Prop) {rs : List Ty}
    (Q : Post rs) (X : XPost) (fwd : Trie Nat) (targetJ : Nat)
    (s : T.mach.MData) (kT : Nat) : Prop :=
  (T.mach.prog host)[kT]? = some (T.frame.label (lname fn (tgtLab fwd targetJ))) ∧
  ∀ s', T.mach.Frame T.gpr.condReads s s' T.frame.scratch [] FlagMask.all →
    T.mach.mem s' = T.mach.mem s →
    T.mach.Run host kT s' (FnPost T host s₀ ra n nX Rf Q X)

private theorem CcmpJumpReady.frame {fwd : Trie Nat} {targetJ kT : Nat} {s s₁ : T.mach.MData}
    {cl : FlagMask}
    (hR : CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s kT)
    (hfr : T.mach.Frame T.gpr.condReads s s₁ T.frame.scratch [] cl)
    (hm : T.mach.mem s₁ = T.mach.mem s) :
    CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s₁ kT := by
  refine ⟨hR.1, fun s' hfr' hm' => ?_⟩
  have hnf : ~~~FlagMask.all = 0#8 := by decide
  have hfrAll : T.mach.Frame T.gpr.condReads s s' T.frame.scratch [] FlagMask.all :=
    (hfr.trans hfr').weaken (fun _ hm => (List.mem_append.mp hm).elim id id)
      (fun _ h => nomatch h) (by simp [hnf])
  exact hR.2 s' hfrAll (hm'.trans hm)

private theorem ccmpJumpReady_of_zeroMoveJump (hy : Hyps T host hints E Γ s₀ n nX bound)
    {G : VCtx} {D : Ctx Cont LNat} {nv ipJ targetJ kT : Nat} {stJ : SymState T.toIsa}
    {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64} {fwd : Trie Nat}
    {e₁ : Expr Val Cont rs} {e₂ : Expr VNat LNat rs}
    (hwf : Wf G D e₁ e₂) (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D)
    (hz : zeroMoveJump? T.toIsa hints ipJ stJ e₂ = some targetJ)
    (hnf : ccmpTargetNoFlag T.toIsa hints targetJ = true)
    (hlabT : (T.mach.prog host)[kT]? = some (T.frame.label (lname fn (tgtLab fwd targetJ))))
    (hA : Agree T G nv stJ s σ)
    (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    (hwp : wp Γ Q X e₁ m) :
    CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s kT := by
  refine ⟨hlabT, fun s' hfr hm => ?_⟩
  cases hwf with
  | @jump _ _ ts j₁ j₂ args₁ args₂ hj hargs =>
    simp only [zeroMoveJump?] at hz
    split at hz; · cases hz
    cases hen : hints.entry.find? j₂ with
    | none => simp [hen] at hz
    | some en =>
      cases hjt : jumpTargets T.toIsa args₂ en.ploc with
      | none => simp [hen, hjt] at hz
      | some argTgts =>
        simp only [hen, hjt, Option.bind_some] at hz
        split at hz
        · rename_i hall
          simp only [Bool.and_eq_true, Option.some.injEq] at hall hz
          subst hz
          obtain ⟨⟨kℓ, hlab⟩, G', hGs, rfl⟩ := hD ts j₁ j₂ hj
          have hkEq := hy.unique _ _ _ hlab hlabT
          subst hkEq
          have hAll : ∀ p ∈ en.live ++ argTgts,
              jumpLocOk T.toIsa hints.nslots p.2 = true ∧
              holdsLoc T.toIsa stJ p.1 p.2 = true := fun p hp => by
            have h := List.all_eq_true.mp hall.1 p hp
            simpa [Bool.and_eq_true] using h
          obtain ⟨hlZ, hpZ⟩ := entryZOk_ok hA hargs hjt hall.2
          simp only [ccmpTargetNoFlag, hen, Bool.and_eq_true, List.all_eq_true] at hnf
          have hjlLive : ∀ p ∈ en.live, ∀ r, p.2 = .gpr r → r ∉ T.frame.scratch := fun p hp r hr =>
            (jumpLocOk_spec (hAll p (List.mem_append_left _ hp)).1).1 r hr
          have hjlArg : ∀ p ∈ argTgts, ∀ r, p.2 = .gpr r → r ∉ T.frame.scratch := fun p hp r hr =>
            (jumpLocOk_spec (hAll p (List.mem_append_right _ hp)).1).1 r hr
          have hNoFlag : ∀ p ∈ en.live ++ argTgts, ∀ c, p.2 ≠ .flag c := fun p hp c hfc => by
            rcases List.mem_append.mp hp with hp | hp
            · have h1 := hnf.1 p hp; simp [hfc] at h1
            · have h2 := hnf.2 p.2 (jumpTargets_loc_mem hjt p hp); simp [hfc] at h2
          exact enter_labJ hy hGs hargs hen hjt (fun p hp =>
            LocOk.frame hfr (holdsLoc_ok hA (hAll p hp).2)
              (jumpLocOk_spec (hAll p hp).1).1 (fun _ _ => List.not_mem_nil)
              (fun c hc => absurd hc (hNoFlag p hp c)))
            (LiveZOk.frame hfr (fun _ => Or.inr trivial) hjlLive hlZ)
            (paramsZOk_frame_jump hfr hjt hjlArg hpZ)
            (hI.keep hm (keep_of_frame_scratch hfr)) hlab hwp
        · cases hz
  | _ => simp [zeroMoveJump?] at hz

private theorem ccmpStartCond_ok {G : VCtx} {nv k : Nat} {st1 : SymState T.toIsa}
    {s1 : T.mach.MData} {σ1 : List (BitVec 64)} {m : Mem 64} {cv : Bool} {cx : Nat}
    {post : T.mach.State → Prop}
    (hmem : (⟨.bool, cv, cx⟩ : (t : Ty) × Val t × VNat t) ∈ G)
    (hA1 : Agree T G nv st1 s1 σ1)
    (hI1 : Inv T hints s₀ ra n Rf m s1 σ1 (isZeroLeaf T.toIsa hints E))
    (hM1 : MemDefsOk G m nv st1.memDefs)
    {cond : JnzCond T.toIsa} (hfc : findJnzCond T.toIsa hints.nslots st1 cx = some cond)
    {cc0 : T.Cond} {c0 : List T.Directive} {cl0 : FlagMask} {reqNonCb : Bool}
    (hsc : ccmpStartCond? T.toIsa cond = some (cc0, c0, cl0, reqNonCb))
    (hc0 : c0.IsInfixAt (T.mach.prog host) k)
    (kont : ∀ s2, T.mach.evalCond s2 cc0 = cv → T.mach.mem s2 = T.mach.mem s1 →
      Agree T G nv (ccmpKillState T.toIsa st1 cl0) s2 σ1 →
      Inv T hints s₀ ra n Rf m s2 σ1 (isZeroLeaf T.toIsa hints E) →
      T.mach.Frame T.gpr.condReads s1 s2 T.frame.scratch [] cl0 →
      T.mach.Run host (k + c0.length) s2 post) :
    T.mach.Run host k s1 post := by
  have hc := findJnzCond_ok hA1 hI1 hM1 hmem hfc
  have stepZero : ∀ {w : Nat} {co : CmpOp} {r : T.Reg} {va : BitVec w} {reqNonCb' : Bool},
      r ∉ T.frame.scratch → GprHolds (T.mach.getGpr s1 r) (.bits w) va →
      cv = co.evalBits va 0#w →
      ((T.gpr.condOfCmp? co).bind fun cc =>
        (T.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ()) (.flag cc, ()) .default).map
          fun (c, cl) => (cc, c, cl, reqNonCb')) = some (cc0, c0, cl0, reqNonCb) →
      T.mach.Run host k s1 post := fun {w co r va _} hns hgp hcv hsc' => by
    obtain ⟨cc', hcc, hsc'⟩ := Option.bind_eq_some_iff.mp hsc'
    obtain ⟨⟨c', cl'⟩, hop, hex⟩ := Option.map_eq_some_iff.mp hsc'
    simp only [Prod.mk.injEq] at hex
    obtain ⟨rfl, rfl, rfl, -⟩ := hex
    refine T.gprSpec.op_spec (s := s1) (P := fun res => res = (co.evalBits va 0#w, ())) hop
      (by simpa [tupArgGprs, PArg.gprs] using hns) (by simp [tupDstGprs])
      (.cons hgp (.cons rfl .nil)) (by simp [OpCode.wp_cmp, liftCmp]) hc0
      fun s2 ⟨⟨⟨b, ⟨⟩⟩, hb, hpd⟩, hm2⟩ hfr2 => ?_
    cases hb; cases hpd with | cons hd _ =>
    have hfr' : T.mach.Frame T.gpr.condReads s1 s2 T.frame.scratch [] cl' := by
      simpa [tupDstGprs] using hfr2
    have hev : T.mach.evalCond s2 cc' = cv := by
      dsimp only [Machine.PDstHolds] at hd; rw [hd, ← hcv]
    exact kont s2 hev hm2 (Agree_ccmpKill hA1 hfr')
      (hI1.keep hm2 (keep_of_frame_scratch hfr')) hfr'
  cases cond with
  | flag cc =>
    simp only [ccmpStartCond?, Option.some.injEq, Prod.mk.injEq] at hsc
    obtain ⟨rfl, rfl, rfl, -⟩ := hsc
    have hfr := Machine.Frame.refl T.gpr.condReads s1 T.frame.scratch [] FlagMask.none
    exact kont s1 hc rfl (Agree_ccmpKill hA1 hfr) hI1 hfr
  | cmpZero co w r =>
    dsimp only [ccmpStartCond?] at hsc
    exact stepZero hc.1 hc.2.choose_spec.1 hc.2.choose_spec.2 hsc
  | cmpZeroFlag co w _ r _ =>
    rcases hc with ⟨_, _, hns, va, hgp, hcv, -⟩
    dsimp only [ccmpStartCond?] at hsc
    exact stepZero hns hgp hcv hsc
  | gpr _ | slot _ | cmpZeroMem _ _ _ _ _ | testImm _ _ _ _ => simp [ccmpStartCond?] at hsc

/-- Induction motive for `lowerCcmpChain` inside `Wf.induct`. -/
@[expose]
def CcmpMotive (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (Γ : Env)
    (fn : Sym) (s₀ : T.mach.MData) (ra : T.mach.Addr) (n nX : Nat) (Rf : Mem 64 → Prop)
    {rs : List Ty} (Q : Post rs) (X : XPost) (G : VCtx) (D : Ctx Cont LNat)
    (e₁ : Expr Val Cont rs) (e₂ : Expr VNat LNat rs) : Prop :=
  ∀ (nv nl ip : Nat) (st : SymState T.toIsa) (brCond : T.Cond) (targetJ ipExtra : Nat)
    (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool)
    (c : List T.Directive) (nv' nl' ip' k kT : Nat) (s : T.mach.MData)
    (σ : List (BitVec 64)) (m : Mem 64),
  lowerCcmpChain T.toIsa hints E fn e₂ nv nl ip st brCond targetJ ipExtra ft fwd fwdTgts =
    .ok (c, nv', nl', ip') →
  c.IsInfixAt (T.mach.prog host) k → FT T host fn ft (k + c.length) →
  FwdBound nl fwd fwdTgts → DScope nl D →
  DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D → Agree T G nv st s σ →
  MemDefsOk G m nv st.memDefs →
  Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E) →
  ccmpTargetNoFlag T.toIsa hints targetJ = true →
  (T.mach.prog host)[kT]? = some (T.frame.label (lname fn (tgtLab fwd targetJ))) →
  (T.mach.evalCond s brCond = true →
    CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s kT) →
  (T.mach.evalCond s brCond = false → wp Γ Q X e₁ m) →
  T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X)

/-- Induction motive for `lowerCcmpJnz` inside `Wf.induct`. -/
@[expose]
def CcmpJnzMotive (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (Γ : Env)
    (fn : Sym) (s₀ : T.mach.MData) (ra : T.mach.Addr) (n nX : Nat) (Rf : Mem 64 → Prop)
    {rs : List Ty} (Q : Post rs) (X : XPost) (G : VCtx) (D : Ctx Cont LNat)
    (e₁ : Expr Val Cont rs) (e₂ : Expr VNat LNat rs) : Prop :=
  ∀ (nv nl ipJnz : Nat) (st : SymState T.toIsa) (brCond : T.Cond) (targetJ ipExtra : Nat)
    (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool) (reqCx : Nat) (co : CmpOp)
    {w : Nat} (a₁ b₁ : Arg Val (.bits w)) (a₂ b₂ : Arg VNat (.bits w))
    (c : List T.Directive) (nv' nl' ip' k kT : Nat) (s : T.mach.MData)
    (σ : List (BitVec 64)) (m : Mem 64),
  lowerCcmpJnz T.toIsa hints E fn e₂ nv nl ipJnz st brCond targetJ ipExtra ft fwd fwdTgts
    reqCx co a₂ b₂ = .ok (c, nv', nl', ip') →
  c.IsInfixAt (T.mach.prog host) k → FT T host fn ft (k + c.length) →
  FwdBound nl fwd fwdTgts → DScope nl D →
  DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D → Agree T G nv st s σ →
  MemDefsOk G m nv st.memDefs →
  Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E) →
  ccmpTargetNoFlag T.toIsa hints targetJ = true →
  (T.mach.prog host)[kT]? = some (T.frame.label (lname fn (tgtLab fwd targetJ))) →
  ArgRel G (.bits w) a₁ a₂ → ArgRel G (.bits w) b₁ b₂ →
  ⟨.bool, co.evalBits a₁.val b₁.val, reqCx⟩ ∈ G →
  (T.mach.evalCond s brCond = true →
    CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s kT) →
  (T.mach.evalCond s brCond = false → wp Γ Q X e₁ m) →
  T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X)

private theorem ccmpArm_spec (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {D : Ctx Cont LNat} {nv ipJump : Nat} {st : SymState T.toIsa} {targetJ : Nat}
    {brCond dstCond : T.Cond} {coStep : CmpOp} {w : Nat}
    {a₁ b₁ : Arg Val (.bits w)} {a₂ b₂ : Arg VNat (.bits w)}
    {jump₁ : Expr Val Cont rs} {jump₂ : Expr VNat LNat rs}
    {rest₁ : Expr Val Cont rs} {c : List T.Directive} {st1 : SymState T.toIsa} {ncb : Bool}
    {k kT : Nat} {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64} {fwd : Trie Nat}
    (hwfJ : Wf G D jump₁ jump₂) (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D)
    (hA : Agree T G nv st s σ) (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    (ha : ArgRel G (.bits w) a₁ a₂) (hb : ArgRel G (.bits w) b₁ b₂)
    (hnf : ccmpTargetNoFlag T.toIsa hints targetJ = true)
    (hlabT : (T.mach.prog host)[kT]? = some (T.frame.label (lname fn (tgtLab fwd targetJ))))
    (hs : ccmpStepArm? T.toIsa hints ipJump st targetJ brCond coStep a₂ b₂ jump₂ =
      some (c, st1, dstCond, ncb))
    (hc : c.IsInfixAt (T.mach.prog host) k)
    (hReady : T.mach.evalCond s brCond = true →
      CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s kT)
    (hTake : T.mach.evalCond s brCond = false →
      (coStep.evalBits a₁.val b₁.val = true → wp Γ Q X jump₁ m) ∧
      (coStep.evalBits a₁.val b₁.val = false → wp Γ Q X rest₁ m))
    (kont : ∀ s1 cl, st1 = ccmpKillState T.toIsa st cl →
      Agree T G nv st1 s1 σ → Inv T hints s₀ ra n Rf m s1 σ (isZeroLeaf T.toIsa hints E) →
      (T.mach.evalCond s1 dstCond = true →
        CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s1 kT) →
      (T.mach.evalCond s1 dstCond = false → wp Γ Q X rest₁ m) →
      T.mach.Run host (k + c.length) s1 (FnPost T host s₀ ra n nX Rf Q X)) :
    T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X) := by
  unfold ccmpStepArm? at hs
  split at hs; · cases hs
  obtain ⟨⟨dst', c', cl, ncb'⟩, hpick, hs⟩ := Option.bind_eq_some_iff.mp hs
  dsimp only at hs
  cases hzm : zeroMoveJump? T.toIsa hints ipJump (ccmpKillState T.toIsa st cl) jump₂ with
  | none => simp [hzm] at hs
  | some j =>
    rw [hzm] at hs; dsimp only at hs
    by_cases heq : Nat.beq j targetJ = true
    · simp only [heq, ite_true, Option.some.injEq, Prod.mk.injEq] at hs
      have hjEq : j = targetJ := Nat.beq_eq.mp heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
      refine ccmpPickStep_ok hA ha hb hc hpick fun s1 hev hm1 hfr1 => ?_
      have hA1 := Agree_ccmpKill hA hfr1
      have hI1 := hI.keep hm1 (keep_of_frame_scratch hfr1)
      refine kont s1 cl rfl hA1 hI1 (fun hdst => ?_) (fun hdst => ?_)
      · cases hbr : T.mach.evalCond s brCond with
        | true => exact (hReady hbr).frame hfr1 hm1
        | false =>
          rw [hbr, Bool.false_or] at hev
          have hc1 : coStep.evalBits a₁.val b₁.val = true := by rw [← hev]; exact hdst
          exact ccmpJumpReady_of_zeroMoveJump hy hwfJ hD (hjEq ▸ hzm) hnf hlabT hA1 hI1
            ((hTake hbr).1 hc1)
      · cases hbr : T.mach.evalCond s brCond with
        | true => simp [hbr] at hev; rw [hev] at hdst; cases hdst
        | false =>
          rw [hbr, Bool.false_or] at hev
          have hc0 : coStep.evalBits a₁.val b₁.val = false := by rw [← hev]; exact hdst
          exact (hTake hbr).2 hc0
    · simp only [heq, Bool.false_eq_true, ite_false] at hs
      cases hs

private inductive CcmpTailRes (T : Target) (hints : T.toIsa.Hints) (E : Ext) (fn : Sym)
    {rs : List Ty} (e₂ : Expr VNat LNat rs) (nv nl ip : Nat) (st : SymState T.toIsa)
    (br : T.Cond) (targetJ ipEx : Nat) (ft : Option Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool)
    (cRest : List T.Directive) (nv' nl' ip' : Nat) : Prop where
  | chain : ccmpCanStep? T.toIsa hints nv nl ip st targetJ br false e₂ = true →
      lowerCcmpChain T.toIsa hints E fn e₂ nv nl ip st br targetJ ipEx ft fwd fwdTgts =
        .ok (cRest, nv', nl', ip') →
      CcmpTailRes T hints E fn e₂ nv nl ip st br targetJ ipEx ft fwd fwdTgts cRest nv' nl' ip'
  | tailJcc : ccmpCanStep? T.toIsa hints nv nl ip st targetJ br false e₂ = false →
      ccmpTailJcc? T.toIsa hints fn nv nl ip ipEx st br targetJ ft fwd e₂ =
        some (cRest, nv', nl', ip') →
      CcmpTailRes T hints E fn e₂ nv nl ip st br targetJ ipEx ft fwd fwdTgts cRest nv' nl' ip'
  | fall : ccmpCanStep? T.toIsa hints nv nl ip st targetJ br false e₂ = false →
      ccmpTailJcc? T.toIsa hints fn nv nl ip ipEx st br targetJ ft fwd e₂ = none →
      finishCcmpTail T.toIsa fn br targetJ fwd ipEx
        (lowerExpr T.toIsa hints E fn e₂ nv nl ip st ft fwd fwdTgts) = .ok (cRest, nv', nl', ip') →
      CcmpTailRes T hints E fn e₂ nv nl ip st br targetJ ipEx ft fwd fwdTgts cRest nv' nl' ip'

private theorem ccmpTail_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {D : Ctx Cont LNat} {nv nl ipRest ipExtra ipEx1 targetJ k1 kT : Nat}
    {st st1 : SymState T.toIsa} {cl : FlagMask} {br1 : T.Cond}
    {ft : Option Nat} {fwd : Trie Nat} {fwdTgts : Trie Bool}
    {rest₁ : Expr Val Cont rs} {rest₂ : Expr VNat LNat rs}
    {cRest : List T.Directive} {nv' nl' ip' : Nat} {s1 : T.mach.MData} {σ : List (BitVec 64)}
    {m : Mem 64}
    (hwfR : Wf G D rest₁ rest₂)
    (ihR1 : Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D rest₁ rest₂)
    (ihR2 : CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D rest₁ rest₂)
    (hst1 : st1 = ccmpKillState T.toIsa st cl)
    (hr : CcmpTailRes T hints E fn rest₂ nv (nl + 1) ipRest st1 br1 targetJ
      (ipExtra + ipEx1) ft fwd fwdTgts cRest nv' nl' ip')
    (hcR : cRest.IsInfixAt (T.mach.prog host) k1) (hft : FT T host fn ft (k1 + cRest.length))
    (hFb : FwdBound nl fwd fwdTgts) (hSc : DScope nl D)
    (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D) (hA1 : Agree T G nv st1 s1 σ)
    (hM1 : MemDefsOk G m nv st1.memDefs)
    (hI1 : Inv T hints s₀ ra n Rf m s1 σ (isZeroLeaf T.toIsa hints E))
    (hnf : ccmpTargetNoFlag T.toIsa hints targetJ = true)
    (hlabT : (T.mach.prog host)[kT]? = some (T.frame.label (lname fn (tgtLab fwd targetJ))))
    (hReady1 : T.mach.evalCond s1 br1 = true →
      CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s1 kT)
    (hRest1 : T.mach.evalCond s1 br1 = false → wp Γ Q X rest₁ m) :
    T.mach.Run host k1 s1 (FnPost T host s₀ ra n nX Rf Q X) := by
  have hFb1 : FwdBound (nl + 1) fwd fwdTgts := hFb.mono (Nat.le_succ _)
  have hSc1 : DScope (nl + 1) D := hSc.mono (Nat.le_succ _)
  cases hr with
  | chain _ hch =>
    exact ihR2 nv (nl + 1) ipRest st1 br1 targetJ (ipExtra + ipEx1) ft fwd fwdTgts cRest nv' nl'
      ip' k1 kT s1 σ m hch hcR hft hFb1 hSc1 hD hA1 hM1 hI1 hnf hlabT hReady1 hRest1
  | tailJcc _ heq =>
    unfold ccmpTailJcc? at heq
    by_cases hftEq : (ft == some (tgtLab fwd targetJ)) = true
    · simp only [hftEq, ite_true] at heq
      obtain ⟨j', hz', hmeq⟩ := Option.map_eq_some_iff.mp heq
      simp only [Prod.mk.injEq] at hmeq
      rcases hmeq with ⟨rfl, rfl, rfl, rfl⟩
      have hftLab := hft (tgtLab fwd targetJ) (beq_iff_eq.mp hftEq)
      obtain ⟨kJ, hlabJ, hrunJ⟩ := thread_ok (m := m) hy hwfR hD hz'
      refine T.gprSpec.jcc_spec hcR (labelAddr_of_unique hy.unique hlabJ) fun s2 hfr2 hm2 => ?_
      cases hbr1 : T.mach.evalCond s1 br1 with
      | false =>
        refine ⟨fun _ => ?_, fun h => by simp [T.gprSpec.negCond_eval, hbr1] at h⟩
        exact hrunJ (hRest1 hbr1) nv s2 σ (Agree_ccmpKill_frameNone hst1 hA1 hfr2)
          (hI1.keep hm2 (keep_of_frame_scratch hfr2))
      | true =>
        refine ⟨fun h => by simp [T.gprSpec.negCond_eval, hbr1] at h, fun _ => ?_⟩
        have hEqK :
            k1 + (T.gpr.jcc (T.gpr.negCond br1) (lname fn (tgtLab fwd j'))).length = kT :=
          hy.unique _ _ _ hftLab hlabT
        rw [hEqK]
        exact (hReady1 hbr1).2 s2 (hfr2.weaken (fun _ hm => hm) (fun _ h => h) (by decide)) hm2
    · simp only [hftEq, Bool.false_eq_true, ite_false] at heq; cases heq
  | fall _ _ hrf =>
    cases hre : lowerExpr T.toIsa hints E fn rest₂ nv (nl + 1) ipRest st1 ft fwd fwdTgts with
    | error _ => rw [hre] at hrf; simp [finishCcmpTail] at hrf
    | ok pR =>
      rcases pR with ⟨cR, nvR, nlR, ipR⟩
      rw [hre] at hrf
      simp only [finishCcmpTail, Except.ok.injEq, Prod.mk.injEq] at hrf
      rcases hrf with ⟨rfl, rfl, rfl, rfl⟩
      obtain ⟨hcJ, hcR'⟩ := List.IsInfixAt.append hcR
      refine T.gprSpec.jcc_spec hcJ (labelAddr_of_unique hy.unique hlabT) fun s2 hfr2 hm2 => ?_
      cases hbr1 : T.mach.evalCond s1 br1 with
      | true =>
        refine ⟨fun _ => ?_, (fun h => by cases h)⟩
        exact (hReady1 hbr1).2 s2 (hfr2.weaken (fun _ hm => hm) (fun _ h => h) (by decide)) hm2
      | false =>
        refine ⟨(fun h => by cases h), fun _ => ?_⟩
        exact ihR1 nv (nl + 1) ipRest st1 ft fwd fwdTgts cR nvR nlR ipR
          (k1 + (T.gpr.jcc br1 (lname fn (tgtLab fwd targetJ))).length) s2 σ m hre hcR'
          (FT_congr (by simp [List.length_append, Nat.add_assoc]) hft) hFb1 hSc1 hD
          (Agree_ccmpKill_frameNone hst1 hA1 hfr2) hM1
          (hI1.keep hm2 (keep_of_frame_scratch hfr2)) (hRest1 hbr1)

private theorem ccmpStepAndTail_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {D : Ctx Cont LNat} {nv nl ipJnz : Nat} {st : SymState T.toIsa} {brCond : T.Cond}
    {targetJ ipExtra : Nat} {ft : Option Nat} {fwd : Trie Nat} {fwdTgts : Trie Bool}
    {co : CmpOp} {w : Nat} {a₁ b₁ : Arg Val (.bits w)} {a₂ b₂ : Arg VNat (.bits w)}
    {t₁ e₁ : Expr Val Cont rs} {t₂ e₂ : Expr VNat LNat rs}
    {code : List T.Directive} {st1 : SymState T.toIsa} {br1 : T.Cond} {ncb wantTrue : Bool}
    {ipRest ipEx1 : Nat} {cRest : List T.Directive} {nv' nl' ip' k kT : Nat} {s : T.mach.MData}
    {σ : List (BitVec 64)} {m : Mem 64}
    (hwfT : Wf G D t₁ t₂) (hwfE : Wf G D e₁ e₂)
    (ihT : Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D t₁ t₂ ∧
      CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D t₁ t₂)
    (ihE : Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ ∧
      CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂)
    (ha : ArgRel G (.bits w) a₁ a₂) (hb : ArgRel G (.bits w) b₁ b₂)
    (hpk : ccmpPickArms? T.toIsa hints nv nl ipJnz st targetJ brCond co a₂ b₂ t₂ e₂ =
      some (code, st1, br1, ncb, wantTrue, ipRest, ipEx1))
    (hTail : (wantTrue = true →
        CcmpTailRes T hints E fn e₂ nv (nl + 1) ipRest st1 br1 targetJ (ipExtra + ipEx1)
          ft fwd fwdTgts cRest nv' nl' ip') ∧
      (wantTrue = false →
        CcmpTailRes T hints E fn t₂ nv (nl + 1) ipRest st1 br1 targetJ (ipExtra + ipEx1)
          ft fwd fwdTgts cRest nv' nl' ip'))
    (hc : (code ++ cRest).IsInfixAt (T.mach.prog host) k)
    (hft : FT T host fn ft (k + (code ++ cRest).length))
    (hFb : FwdBound nl fwd fwdTgts) (hSc : DScope nl D)
    (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D) (hA : Agree T G nv st s σ)
    (hM : MemDefsOk G m nv st.memDefs)
    (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    (hnf : ccmpTargetNoFlag T.toIsa hints targetJ = true)
    (hlabT : (T.mach.prog host)[kT]? = some (T.frame.label (lname fn (tgtLab fwd targetJ))))
    (hReady : T.mach.evalCond s brCond = true →
      CcmpJumpReady T host fn s₀ ra n nX Rf Q X fwd targetJ s kT)
    (hWp : T.mach.evalCond s brCond = false →
      (co.evalBits a₁.val b₁.val = true → wp Γ Q X t₁ m) ∧
      (co.evalBits a₁.val b₁.val = false → wp Γ Q X e₁ m)) :
    T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X) := by
  obtain ⟨hcCode, hcRest⟩ := List.IsInfixAt.append hc
  have hftR : FT T host fn ft (k + code.length + cRest.length) :=
    FT_congr (by simp [List.length_append, Nat.add_assoc]) hft
  unfold ccmpPickArms? at hpk
  rcases orElse_eq_some hpk with hT | hF
  · obtain ⟨⟨c', st', br', ncb'⟩, haT, heq⟩ := Option.map_eq_some_iff.mp hT
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    refine ccmpArm_spec hy hwfT hD hA hI ha hb hnf hlabT haT hcCode hReady hWp
      fun s1 cl hst1 hA1 hI1 hReady1 hRest1 => ?_
    exact ccmpTail_ok hy hwfE ihE.1 ihE.2 hst1 (hTail.1 rfl) hcRest hftR hFb hSc hD hA1
      (by subst hst1; exact hM) hI1 hnf hlabT hReady1 hRest1
  · obtain ⟨⟨c', st', br', ncb'⟩, haF, heq⟩ := Option.map_eq_some_iff.mp hF
    simp only [Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hWpNeg : T.mach.evalCond s brCond = false →
        (co.neg.evalBits a₁.val b₁.val = true → wp Γ Q X e₁ m) ∧
        (co.neg.evalBits a₁.val b₁.val = false → wp Γ Q X t₁ m) := fun hbr => by
      have hw := hWp hbr
      refine ⟨fun hn => hw.2 ?_, fun hn => hw.1 ?_⟩
      · rw [CmpOp.neg_evalBits] at hn; cases h : co.evalBits a₁.val b₁.val <;> simp_all
      · rw [CmpOp.neg_evalBits] at hn; cases h : co.evalBits a₁.val b₁.val <;> simp_all
    refine ccmpArm_spec hy hwfE hD hA hI ha hb hnf hlabT haF hcCode hReady hWpNeg
      fun s1 cl hst1 hA1 hI1 hReady1 hRest1 => ?_
    exact ccmpTail_ok hy hwfT ihT.1 ihT.2 hst1 (hTail.2 rfl) hcRest hftR hFb hSc hD hA1
      (by subst hst1; exact hM) hI1 hnf hlabT hReady1 hRest1

theorem ccmpStart_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {D : Ctx Cont LNat} {nv nl ip : Nat} {st1 : SymState T.toIsa} {cond : JnzCond T.toIsa}
    {t₁ e₁ : Expr Val Cont rs} {t₂ e₂ : Expr VNat LNat rs}
    {c0 : List T.Directive} {st0 : SymState T.toIsa} {br0 : T.Cond}
    {targetJ : Nat} {wantTrue : Bool} {ipRest ipEx0 : Nat}
    {cR : List T.Directive} {nv' nl' ip' k : Nat} {s1 : T.mach.MData} {σ1 : List (BitVec 64)}
    {m : Mem 64} {cv : Bool} {cx : Nat} {ft : Option Nat} {fwd : Trie Nat} {fwdTgts : Trie Bool}
    (hwfT : Wf G D t₁ t₂) (hwfE : Wf G D e₁ e₂)
    (ihT : CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D t₁ t₂)
    (ihE : CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂)
    (hmem : (⟨.bool, cv, cx⟩ : (t : Ty) × Val t × VNat t) ∈ G)
    (hfc : findJnzCond T.toIsa hints.nslots st1 cx = some cond)
    (hstC : ccmpStart? T.toIsa hints nv nl ip st1 cond t₂ e₂ =
      some (c0, st0, br0, targetJ, wantTrue, ipRest, ipEx0))
    (hr : (if wantTrue then
        lowerCcmpChain T.toIsa hints E fn e₂ nv (nl + 1) ipRest st0 br0 targetJ ipEx0
          ft fwd fwdTgts
      else
        lowerCcmpChain T.toIsa hints E fn t₂ nv (nl + 1) ipRest st0 br0 targetJ ipEx0
          ft fwd fwdTgts) = .ok (cR, nv', nl', ip'))
    (hc : (c0 ++ cR).IsInfixAt (T.mach.prog host) k)
    (hft : FT T host fn ft (k + (c0 ++ cR).length))
    (hFb : FwdBound nl fwd fwdTgts) (hSc : DScope nl D)
    (hD : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G D) (hA1 : Agree T G nv st1 s1 σ1)
    (hM1 : MemDefsOk G m nv st1.memDefs)
    (hI1 : Inv T hints s₀ ra n Rf m s1 σ1 (isZeroLeaf T.toIsa hints E))
    (hwp : (cv = true → wp Γ Q X t₁ m) ∧ (cv = false → wp Γ Q X e₁ m)) :
    T.mach.Run host k s1 (FnPost T host s₀ ra n nX Rf Q X) := by
  unfold ccmpStart? at hstC
  split at hstC; · cases hstC
  obtain ⟨⟨cc0, c0', cl0, reqNonCb⟩, hsc, hstC⟩ := Option.bind_eq_some_iff.mp hstC
  obtain ⟨hc0, hcR⟩ := List.IsInfixAt.append hc
  have hftR : FT T host fn ft (k + c0.length + cR.length) :=
    FT_congr (by simp [List.length_append, Nat.add_assoc]) hft
  have hFb1 : FwdBound (nl + 1) fwd fwdTgts := hFb.mono (Nat.le_succ _)
  have hSc1 : DScope (nl + 1) D := hSc.mono (Nat.le_succ _)
  rcases orElse_eq_some hstC with h1 | h2
  · dsimp only at h1; split at h1; · cases h1
    cases hzm : zeroMoveJump? T.toIsa hints (jnzIpT nv nl ip t₂ e₂)
        (ccmpKillState T.toIsa st1 cl0) t₂ with
    | none => simp [hzm] at h1
    | some tj =>
      simp only [hzm] at h1
      cases hnf : ccmpTargetNoFlag T.toIsa hints tj
      · simp [hnf] at h1
      · simp only [hnf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h1
        by_cases hcs : ccmpCanStep? T.toIsa hints nv (nl + 1) (ip + 1)
            (ccmpKillState T.toIsa st1 cl0) tj cc0 reqNonCb e₂ = true
        · simp only [hcs, ite_true, Option.some.injEq, Prod.mk.injEq] at h1
          rcases h1 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          simp only [ite_true] at hr
          obtain ⟨kT, hlabT, _⟩ := thread_ok (m := m) hy hwfT hD hzm
          refine ccmpStartCond_ok hmem hA1 hI1 hM1 hfc hsc hc0
            fun s0 hev hm0 hA0 hI0 _ => ?_
          have hM0 : MemDefsOk G m nv (ccmpKillState T.toIsa st1 cl0).memDefs := hM1
          exact ihE nv (nl + 1) (ip + 1) (ccmpKillState T.toIsa st1 cl0) cc0 tj 1 ft fwd fwdTgts
            cR nv' nl' ip' (k + c0'.length) kT s0 σ1 m hr hcR hftR hFb1 hSc1 hD hA0 hM0 hI0 hnf
            hlabT (fun hcc => ccmpJumpReady_of_zeroMoveJump hy hwfT hD hzm hnf hlabT hA0 hI0
              (hwp.1 (by rw [← hev]; exact hcc)))
            (fun hcc => hwp.2 (by rw [← hev]; exact hcc))
        · simp [hcs] at h1
  · dsimp only at h2; split at h2; · cases h2
    cases hzm : zeroMoveJump? T.toIsa hints (ip + 1) (ccmpKillState T.toIsa st1 cl0) e₂ with
    | none => simp [hzm] at h2
    | some tj =>
      simp only [hzm] at h2
      cases hnf : ccmpTargetNoFlag T.toIsa hints tj
      · simp [hnf] at h2
      · simp only [hnf, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h2
        by_cases hcs : ccmpCanStep? T.toIsa hints nv (nl + 1) (ip + 2)
            (ccmpKillState T.toIsa st1 cl0) tj (T.gpr.negCond cc0) reqNonCb t₂ = true
        · simp only [hcs, ite_true, Option.some.injEq, Prod.mk.injEq] at h2
          rcases h2 with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          simp only [Bool.false_eq_true, ite_false] at hr
          obtain ⟨kT, hlabT, _⟩ := thread_ok (m := m) hy hwfE hD hzm
          refine ccmpStartCond_ok hmem hA1 hI1 hM1 hfc hsc hc0
            fun s0 hev hm0 hA0 hI0 _ => ?_
          have hM0 : MemDefsOk G m nv (ccmpKillState T.toIsa st1 cl0).memDefs := hM1
          exact ihT nv (nl + 1) (ip + 2) (ccmpKillState T.toIsa st1 cl0) (T.gpr.negCond cc0) tj 0
            ft fwd fwdTgts cR nv' nl' ip' (k + c0'.length) kT s0 σ1 m hr hcR hftR hFb1 hSc1 hD hA0
            hM0 hI0 hnf hlabT
            (fun hneg => ccmpJumpReady_of_zeroMoveJump hy hwfE hD hzm hnf hlabT hA0 hI0
              (hwp.2 (by rw [T.gprSpec.negCond_eval, hev] at hneg; cases cv <;> simp_all)))
            (fun hneg => hwp.1 (by rw [T.gprSpec.negCond_eval, hev] at hneg; cases cv <;> simp_all))
        · simp [hcs] at h2

theorem ccmpMotive_let (_hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {D : Ctx Cont LNat} {ts : List Ty} {op₁ : Op Val ts} {op₂ : Op VNat ts}
    {k₁ : Tup Val ts → Expr Val Cont rs} {k₂ : Tup VNat ts → Expr VNat LNat rs}
    (hop : OpRel G op₁ op₂)
    (ih : ∀ (xs₁ : Tup Val ts) (xs₂ : Tup VNat ts),
      CcmpJnzMotive T host hints E Γ fn s₀ ra n nX Rf Q X (Tup.zip xs₁ xs₂ ++ G) D
        (k₁ xs₁) (k₂ xs₂)) :
    CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D (.let_ (ts := ts) op₁ k₁)
      (.let_ op₂ k₂) := by
  intro nv nl ip st brCond targetJ ipExtra ft fwd fwdTgts c nv' nl' ip' k kT s σ m
    hl hc hft hFb hSc hD hA hM hI hnf hlabT hReady hWp
  cases ts with
  | nil => dsimp only [lowerCcmpChain] at hl; cases hl
  | cons t0 ts0 =>
    cases t0 <;> try (dsimp only [lowerCcmpChain] at hl; cases hl; done)
    cases ts0 with
    | cons _ _ => dsimp only [lowerCcmpChain] at hl; cases hl
    | nil =>
      dsimp only [lowerCcmpChain] at hl
      cases hcmp : ccmpAsCmp? op₂.code op₂.args with
      | none => rw [hcmp] at hl; cases hl
      | some p =>
        rcases p with ⟨w, co, a₂, b₂⟩
        rw [hcmp] at hl; dsimp only at hl
        split at hl; · cases hl
        obtain ⟨a₁, b₁, ha, hb, hwpF⟩ := opRel_ccmpAsCmp hop hcmp
        let bv := co.evalBits a₁.val b₁.val
        let G' : VCtx := ⟨.bool, bv, nv⟩ :: G
        have hA' : Agree T G' (nv + 1) st s σ := Agree_push_bool hA bv
        have hM' : MemDefsOk G' m (nv + 1) st.memDefs :=
          hM.grow (Nat.le_succ _)
            (fun p hp => (List.mem_cons.mp hp).elim
              (fun h => .inr (by cases h; exact Nat.le_refl _)) .inl)
            (fun _ hp => List.mem_cons_of_mem _ hp)
        have hD' : DOk T host hints E fn s₀ ra n nX Rf Q X fwd G' D :=
          hD.weaken fun _ hp => List.mem_cons_of_mem _ hp
        have ha' : ArgRel G' (.bits w) a₁ a₂ :=
          argRel_mono (fun _ hp => List.mem_cons_of_mem _ hp) ha
        have hb' : ArgRel G' (.bits w) b₁ b₂ :=
          argRel_mono (fun _ hp => List.mem_cons_of_mem _ hp) hb
        exact ih (bv, ()) (Tup.levels [.bool] nv) (nv + 1) nl (ip + 1) st brCond targetJ ipExtra
          ft fwd fwdTgts nv co a₁ b₁ a₂ b₂ c nv' nl' ip' k kT s σ m hl hc hft hFb hSc hD' hA'
          hM' hI hnf hlabT ha' hb' List.mem_cons_self hReady fun hbrF => hwpF _ (hWp hbrF)

theorem ccmpMotive_jnz (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {D : Ctx Cont LNat} {c₁ : Arg Val .bool} {c₂ : Arg VNat .bool}
    {t₁ e₁ : Expr Val Cont rs} {t₂ e₂ : Expr VNat LNat rs}
    (hcr : ArgRel G .bool c₁ c₂) (hwfT : Wf G D t₁ t₂) (hwfE : Wf G D e₁ e₂)
    (ihT : Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D t₁ t₂ ∧
      CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D t₁ t₂)
    (ihE : Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ ∧
      CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂) :
    CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂) := by
  intro nv nl ip st brCond targetJ ipExtra ft fwd fwdTgts c nv' nl' ip' k kT s σ m
    hl hc hft hFb hSc hD hA hM hI hnf hlabT hReady hWp
  cases hcr with
  | imm _ => dsimp only [lowerCcmpChain] at hl; cases hl
  | @var cv cx hmem =>
    dsimp only [lowerCcmpChain] at hl
    split at hl; · cases hl
    cases hd : st.defs.find? cx with
    | none => rw [hd] at hl; cases hl
    | some df =>
      rw [hd] at hl
      cases df <;> try (dsimp only at hl; cases hl; done)
      rename_i co w y
      dsimp only at hl
      obtain ⟨va, hmy, hcv⟩ := (hA.defs cx (.cmpZeroVar co w y) hd).2 cv hmem
      cases hpk : ccmpPickArms? T.toIsa hints nv nl ip st targetJ brCond co (.var y) (.imm 0#w)
          t₂ e₂ with
      | none => rw [hpk] at hl; cases hl
      | some p =>
        rcases p with ⟨code, st1, br1, ncb, wantTrue, ipRest, ipEx1⟩
        rw [hpk] at hl; dsimp only at hl
        obtain ⟨cRest, hrest, rfl⟩ := prepend_ok hl
        refine ccmpStepAndTail_ok (nv := nv) (nl := nl) (ipJnz := ip) (st := st)
          (brCond := brCond) (targetJ := targetJ) (ipExtra := ipExtra) (ft := ft) (fwd := fwd)
          (fwdTgts := fwdTgts) (co := co) (w := w) (b₁ := .imm (0#w)) (b₂ := .imm (0#w))
          (cRest := cRest) (nv' := nv') (nl' := nl') (ip' := ip')
          hy hwfT hwfE ihT ihE (ArgRel.var hmy) (ArgRel.imm (t := .bits w) (0#w : BitVec w))
          hpk ?_ hc
          hft hFb hSc hD hA hM hI hnf hlabT hReady fun hbr => ?_
        · refine ⟨fun hwt => ?_, fun hwt => ?_⟩ <;>
          · simp only [hwt, Bool.false_eq_true, ite_true, ite_false] at hrest
            cases hcs : ccmpCanStep? T.toIsa hints nv (nl + 1) ipRest st1 targetJ br1 false
                _ with
            | true => exact .chain hcs (by simpa [hcs] using hrest)
            | false =>
              simp only [hcs, Bool.false_eq_true, ite_false] at hrest
              cases htj : ccmpTailJcc? T.toIsa hints fn nv (nl + 1) ipRest (ipExtra + ipEx1) st1
                  br1 targetJ ft fwd _ with
              | some res => rw [htj] at hrest; cases hrest; exact .tailJcc hcs htj
              | none => rw [htj] at hrest; exact .fall hcs htj hrest
        · have hwpJ := hWp hbr
          simp only [wp, Arg.val] at hwpJ
          exact ⟨fun ht => hwpJ.1 (by rw [hcv]; exact ht), fun hf => hwpJ.2 (by rw [hcv]; exact hf)⟩

theorem ccmpJnzMotive_jnz (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {D : Ctx Cont LNat} {c₁ : Arg Val .bool} {c₂ : Arg VNat .bool}
    {t₁ e₁ : Expr Val Cont rs} {t₂ e₂ : Expr VNat LNat rs}
    (hcr : ArgRel G .bool c₁ c₂) (hwfT : Wf G D t₁ t₂) (hwfE : Wf G D e₁ e₂)
    (ihT : Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D t₁ t₂ ∧
      CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D t₁ t₂)
    (ihE : Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ ∧
      CcmpMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂) :
    CcmpJnzMotive T host hints E Γ fn s₀ ra n nX Rf Q X G D (.jnz c₁ t₁ e₁) (.jnz c₂ t₂ e₂) := by
  intro nv nl ipJnz st brCond targetJ ipExtra ft fwd fwdTgts reqCx co w a₁ b₁ a₂ b₂
    c nv' nl' ip' k kT s σ m hl hc hft hFb hSc hD hA hM hI hnf hlabT ha hb hreq hReady hWp
  cases hcr with
  | imm _ => dsimp only [lowerCcmpJnz] at hl; cases hl
  | @var cv cx hmem =>
    dsimp only [lowerCcmpJnz] at hl
    split at hl; · cases hl
    rename_i hcond
    simp only [Bool.not_eq_true', Bool.and_eq_false_iff] at hcond
    have hcx : cx = reqCx := by
      cases hc' : Nat.beq cx reqCx
      · simp [hc'] at hcond
      · exact Nat.beq_eq.mp hc'
    subst hcx
    have hcvEq : cv = co.evalBits a₁.val b₁.val := hA.ctx_uniq hmem hreq
    cases hpk : ccmpPickArms? T.toIsa hints nv nl ipJnz st targetJ brCond co a₂ b₂ t₂ e₂ with
    | none => rw [hpk] at hl; cases hl
    | some p =>
      rcases p with ⟨code, st1, br1, ncb, wantTrue, ipRest, ipEx1⟩
      rw [hpk] at hl; dsimp only at hl
      obtain ⟨cRest, hrest, rfl⟩ := prepend_ok hl
      refine ccmpStepAndTail_ok (nv := nv) (nl := nl) (ipJnz := ipJnz) (st := st)
        (brCond := brCond) (targetJ := targetJ) (ipExtra := ipExtra) (ft := ft) (fwd := fwd)
        (fwdTgts := fwdTgts) (co := co) (cRest := cRest) (nv' := nv') (nl' := nl') (ip' := ip')
        hy hwfT hwfE ihT ihE ha hb hpk ?_ hc hft hFb hSc hD hA hM hI hnf hlabT hReady
        fun hbr => ?_
      · refine ⟨fun hwt => ?_, fun hwt => ?_⟩ <;>
        · simp only [hwt, Bool.false_eq_true, ite_true, ite_false] at hrest
          cases hcs : ccmpCanStep? T.toIsa hints nv (nl + 1) ipRest st1 targetJ br1 false _ with
          | true => exact .chain hcs (by simpa [hcs] using hrest)
          | false =>
            simp only [hcs, Bool.false_eq_true, ite_false] at hrest
            cases htj : ccmpTailJcc? T.toIsa hints fn nv (nl + 1) ipRest (ipExtra + ipEx1) st1
                br1 targetJ ft fwd _ with
            | some res => rw [htj] at hrest; cases hrest; exact .tailJcc hcs htj
            | none => rw [htj] at hrest; exact .fall hcs htj hrest
      · have hwpJ := hWp hbr
        simp only [wp, Arg.val, hcvEq] at hwpJ
        exact hwpJ

end Main

end Rega
end LeanQbe.T
