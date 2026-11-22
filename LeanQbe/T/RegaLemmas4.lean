module

public import LeanQbe.T.RegaLemmas2
public import LeanQbe.T.RegaLemmas3

/-!
# `T7b` Part 4: `Wf.induct` Correctness of PHOAS-First `lowerExpr`/`lowerBlocks` and `lowerFn`

* `LabJ`/`makeLabJs`/`DOk`: join points are interpreted as "running from the block label is safe
  for every machine state agreeing with the block `Entry`" (the `LabJ` pattern of `AuditProof.lean`,
  no `pend_mem` pass).
* `lowerExpr_correct` by `Wf.induct`, `lowerBlocks_closed` by induction on `WfB`.
* `lowerFn_correct : ... → T.FnSpec host f.name (Func.spec Γ f.body) n nX`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

section Defs
variable (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (fn : Sym)
  (s₀ : T.mach.MData) (ra : T.mach.Addr) (n nX : Nat) (Rf : Mem 64 → Prop) {rs : List Ty}
  (Q : Post rs) (X : XPost)

/-- Machine meaning of block label `ℓ` for a join point declared in value context `G`. -/
def LabJ (G : VCtx) (ℓ : Nat) {ts : List Ty} : Cont ts := fun xs m =>
  ∃ k en, (T.mach.prog host)[k]? = some (T.frame.label (lname fn ℓ)) ∧
    hints.entry.find? ℓ = some en ∧
    ∀ s σ, (∀ p ∈ en.live, LocOk T.mach G s σ p.1 p.2) → ParamsOk T.mach s σ ts xs en.ploc →
      Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E) →
      T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X)

def makeLabJs (G : VCtx) : (sig : List (List Ty)) → Nat → Tup Cont sig
  | [], _ => ()
  | ts :: sig, lid =>
    (LabJ T host hints E fn s₀ ra n nX Rf Q X G lid (ts := ts), makeLabJs G sig (lid + 1))

/-- Every join point in scope is a `LabJ` of an enclosing context. -/
def DOk (G : VCtx) (D : Ctx Cont LNat) : Prop :=
  ∀ ts (J : Cont ts) (ℓ : Nat), ⟨ts, J, ℓ⟩ ∈ D →
    (∃ k : Nat, (T.mach.prog host)[k]? = some (T.frame.label (lname fn ℓ))) ∧
    ∃ G', (∀ p ∈ G', p ∈ G) ∧ J = LabJ T host hints E fn s₀ ra n nX Rf Q X G' ℓ

/-- Fallthrough obligation: code following position `k` starts with label `ft`. -/
def FT (ft : Option Nat) (k : Nat) : Prop :=
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

theorem DOk.weaken {G G' : VCtx} {D : Ctx Cont LNat} (hsub : ∀ p ∈ G, p ∈ G')
    (hD : DOk T host hints E fn s₀ ra n nX Rf Q X G D) :
    DOk T host hints E fn s₀ ra n nX Rf Q X G' D := by
  intro ts J ℓ hJ
  obtain ⟨hk, G'', hG'', rfl⟩ := hD ts J ℓ hJ
  exact ⟨hk, G'', fun p hp => hsub p (hG'' p hp), rfl⟩

theorem makeLabJs_dok {G : VCtx} :
    ∀ (sig : List (List Ty)) (lid : Nat) {D : Ctx Cont LNat},
    (∀ i, i < sig.length → ∃ k : Nat, (T.mach.prog host)[k]? = some (T.frame.label (lname fn (lid + i)))) →
    DOk T host hints E fn s₀ ra n nX Rf Q X G D →
    DOk T host hints E fn s₀ ra n nX Rf Q X G
      (Tup.zip (makeLabJs T host hints E fn s₀ ra n nX Rf Q X G sig lid) (Tup.levels sig lid) ++ D)
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

theorem jumpLocOk_spec {nslots : Nat} {loc : T.toIsa.Loc} (h : jumpLocOk T.toIsa nslots loc = true) :
    (∀ r, loc = .gpr r → r ∉ T.frame.scratch) ∧ (∀ vr, loc = .vec vr → vr ∉ T.vec.vecScratch) := by
  cases loc <;> simp_all [jumpLocOk]

/-- `Agree` for the block-entry base state (lexical `defs`/`vw` of the enclosing group). -/
theorem Agree.base {G : VCtx} {nvg nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nvg st s σ) (hle : nvg ≤ nv) (s' : T.mach.MData)
    (σ' : List (BitVec 64)) :
    Agree T G nv
      { regs := [], slots := .empty, defs := st.defs, vecWidths := st.vecWidths } s' σ' where
  ctx_lt p hp := Nat.lt_of_lt_of_le (hA.ctx_lt p hp) hle
  regs p hp := by simp at hp
  slots i se h := by simp [Trie.find?] at h
  defs := hA.defs
  vw := hA.vw
  regs_lt p hp := by simp at hp
  slots_lt i se h := by simp [Trie.find?] at h
  defs_lt x d h := Nat.lt_of_lt_of_le (hA.defs_lt x d h) hle
  vw_lt x w h := Nat.lt_of_lt_of_le (hA.vw_lt x w h) hle
  vt := hA.vt

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

/-- `jnz` condition lookup. -/
theorem findJnzCond_ok {G : VCtx} {nv : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) {cv : Bool} {cx : Nat}
    (hmem : (⟨.bool, cv, cx⟩ : (t : Ty) × Val t × VNat t) ∈ G) :
    ∀ {r}, findJnzCond T.toIsa st.regs cx = some r →
    match r with
    | .inl c => T.mach.evalCond s c = cv
    | .inr g => g ∉ T.frame.scratch ∧ GprHolds (T.mach.getGpr s g) .bool cv := by
  intro r hr
  unfold findJnzCond at hr
  cases hf : findFlagFor T.toIsa st.regs (.var cx) with
  | some c =>
    rw [hf] at hr; simp only [Option.map_some] at hr; cases hr
    unfold findFlagFor at hf
    obtain ⟨⟨sa, rl⟩, hp, he⟩ := findSome_mem hf
    cases rl with
    | flag c' =>
      simp only at he
      split at he
      · cases he
        have h1 := hA.regs _ hp
        simp only [RegLocOk, symArgEq_var ‹_›, FlagSym] at h1
        have := h1 _ _ hmem
        simp only [FlagHolds] at this
        exact this.symm
      · cases he
    | _ => simp at he
  | none =>
    rw [hf] at hr; simp only [Option.map_none] at hr
    cases hg : findGprFor T.toIsa true st.regs (.var cx) with
    | none => rw [hg] at hr; cases hr
    | some g =>
      rw [hg] at hr; cases hr
      unfold findGprFor at hg
      obtain ⟨⟨sa, rl⟩, hp, he⟩ := findSome_mem hg
      cases rl with
      | gpr g' =>
        simp only at he
        split at he
        · cases he
          rename_i hc
          simp only [Bool.and_eq_true] at hc
          obtain ⟨hc1, hc2⟩ := hc
          refine ⟨fun hm => by simp [hm] at hc1, ?_⟩
          have h1 := hA.regs _ hp
          simp only [RegLocOk, symArgMatchesGpr_var hc2, GprSym] at h1
          exact h1 _ _ hmem
        · cases he
      | gprZ g' =>
        simp only at he
        split at he
        · cases he
          rename_i hc
          simp only [Bool.and_eq_true] at hc
          obtain ⟨hc1, hc2⟩ := hc
          refine ⟨fun hm => by simp [hm] at hc1, ?_⟩
          have h1 := (hA.regs _ hp).1
          simp only [symArgMatchesGpr_var hc2, GprSym] at h1
          exact h1 _ _ hmem
        · cases he
      | _ => simp at he

end Basic

/-! ## The main induction -/


section Main
variable {T : Target} {host : T.mach.Host} {hints : T.toIsa.Hints} {E : Ext} {Γ : Env} {fn : Sym}
  {s₀ : T.mach.MData} {ra : T.mach.Addr} {n nX : Nat} {Rf : Mem 64 → Prop} {bound : Sym → Nat}
  {rs : List Ty} {Q : Post rs} {X : XPost}

/-- The `Wf.induct` motive. -/
def Motive (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (Γ : Env) (fn : Sym)
    (s₀ : T.mach.MData) (ra : T.mach.Addr) (n nX : Nat) (Rf : Mem 64 → Prop) {rs : List Ty}
    (Q : Post rs) (X : XPost) (G : VCtx) (D : Ctx Cont LNat)
    (e₁ : Expr Val Cont rs) (e₂ : Expr VNat LNat rs) : Prop :=
  ∀ (nv nl ip : Nat) (st : SymState T.toIsa) (ft : Option Nat) (c : List T.Directive)
    (nv' nl' ip' k : Nat) (s : T.mach.MData) (σ : List (BitVec 64)) (m : Mem 64),
  lowerExpr T.toIsa hints E fn e₂ nv nl ip st ft = .ok (c, nv', nl', ip') →
  c.IsInfixAt (T.mach.prog host) k → FT T host fn ft (k + c.length) →
  DOk T host hints E fn s₀ ra n nX Rf Q X G D → Agree T G nv st s σ →
  MemDefsOk G m nv st.memDefs →
  Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E) → wp Γ Q X e₁ m →
  T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X)

/-- Jump to a join point `J = LabJ G' j` after targets hold (shared by `jump` and `jnz` threads). -/
theorem enter_labJ (hy : Hyps T host hints E Γ s₀ n nX bound) {G G' : VCtx} (hGs : ∀ p ∈ G', p ∈ G)
    {ts : List Ty} {args₁ : Tup (Arg Val) ts} {args : Tup (Arg VNat) ts} (hargs : TRel (ArgRel G) args₁ args)
    {j k : Nat} {en : Entry T.Reg T.VReg T.Cond} {argTgts : List (SymArg × T.toIsa.Loc)}
    (hen : hints.entry.find? j = some en) (hjt : jumpTargets T.toIsa args en.ploc = some argTgts)
    {s : T.mach.MData} {σ : List (BitVec 64)} {m : Mem 64}
    (hok : ∀ p ∈ en.live ++ argTgts, LocOk T.mach G s σ p.1 p.2)
    (hI : Inv T hints s₀ ra n Rf m s σ (isZeroLeaf T.toIsa hints E))
    (hlab : (T.mach.prog host)[k]? = some (T.frame.label (lname fn j)))
    (hJ : LabJ T host hints E fn s₀ ra n nX Rf Q X G' j (vals args₁) m) :
    T.mach.Run host k s (FnPost T host s₀ ra n nX Rf Q X) := by
  obtain ⟨kℓ, en', hlab', hen', hrun⟩ := hJ
  rw [hen] at hen'; cases hen'
  have hk := hy.unique _ _ _ hlab hlab'
  subst hk
  refine hrun s σ (fun p hp => LocOk.mono hGs (hok p (List.mem_append_left _ hp))) ?_ hI
  exact paramsOk_of_jumpTargets hargs hjt fun p hp => hok p (List.mem_append_right _ hp)

theorem lowerBlocks_closed (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx} {D' : Ctx Cont LNat}
    (hD' : DOk T host hints E fn s₀ ra n nX Rf Q X G D') {nvg : Nat} {stg : SymState T.toIsa}
    {sg : T.mach.MData} {σg : List (BitVec 64)} (hAg : Agree T G nvg stg sg σg) :
    ∀ {sig : List (List Ty)} {bs₁ : Blocks Val Cont rs sig} {bs₂ : Blocks VNat LNat rs sig},
    WfB G D' bs₁ bs₂ →
    (∀ {ts} (i : Member ts sig) (xs₁ : Tup Val ts) (xs₂ : Tup VNat ts),
      Motive T host hints E Γ fn s₀ ra n nX Rf Q X (Tup.zip xs₁ xs₂ ++ G) D'
        (bs₁.get i xs₁) (bs₂.get i xs₂)) →
    ∀ (lid nv nl ip : Nat) (ft : Option Nat) (cb : List T.Directive) (nv' nl' ip' kb : Nat),
    nvg ≤ nv →
    lowerBlocks T.toIsa hints E fn bs₂ lid nv nl ip stg.defs stg.vecWidths ft = .ok (cb, nv', nl', ip') →
    cb.IsInfixAt (T.mach.prog host) kb → FT T host fn ft (kb + cb.length) →
    Closed Γ Q X bs₁ (makeLabJs T host hints E fn s₀ ra n nX Rf Q X G sig lid)
  | [], .nil, .nil, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | ts :: _, .cons b₁ bs₁, .cons b₂ bs₂, .cons _ hbs', ihb, lid, nv, nl, ip, ft, cb, nv', nl', ip', kb,
      hle, hpb, hcode, hft => by
    simp only [lowerBlocks] at hpb
    cases hen : hints.entry.find? lid with
    | none => simp [hen] at hpb
    | some en =>
      simp only [hen] at hpb
      by_cases hsc : entryScopeOk nv en = true
      · simp only [hsc, Bool.not_true, Bool.false_eq_true, ite_false] at hpb
        cases hbe : buildEntryBase T.toIsa hints.nslots stg.vecWidths en.live
            { regs := [], slots := .empty, defs := stg.defs, vecWidths := stg.vecWidths } with
        | none => simp [hbe] at hpb
        | some baseSt =>
          simp only [hbe] at hpb
          cases hbp : bindBlockParams T.toIsa hints.nslots ts en.ploc nv baseSt with
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
              have hnv1 : nv ≤ nv1 := by
                have := (lowerExpr_nv_le hlb).1; omega
              simp only [Closed, makeLabJs]
              refine ⟨?_, ?_⟩
              · intro xs₁ m' hwpb
                refine ⟨kb, en, hlab, hen, fun s σ hlive hparams hI => ?_⟩
                refine T.frameSpec.label_spec hlab ?_
                have hσ : σ.length = hints.nslots := hI.1
                have hlt : ∀ p ∈ en.live, symArgScopeOk nv p.1 = true := by
                  simpa [entryScopeOk, List.all_eq_true] using hsc
                have hA0 := buildEntryBase_ok hbe hlive hlt hσ (hAg.base hle s σ)
                have hA1 := bindBlockParams_ok hbp hparams hσ hA0
                have hmd : initSt.memDefs = .empty :=
                  (bindBlockParams_memDefs hbp).trans (buildEntryBase_memDefs hbe)
                refine ihb .here xs₁ (Tup.levels ts nv) (nv + ts.length) nl ip initSt _ cbb nv1 nl1 ip1
                  (kb + 1) s σ m' hlb hcbb ?_ (hD'.weaken fun _ hp => List.mem_append_right _ hp)
                  hA1 (hmd ▸ MemDefsOk.empty _ _ _) hI hwpb
                intro j hj
                split at hj
                · simp only [lowerBlocks, Except.ok.injEq, Prod.mk.injEq] at hpr
                  obtain ⟨rfl, -, -, -⟩ := hpr
                  have := hft j hj
                  simpa [Nat.add_assoc, Nat.add_comm 1] using this
                · simp only [Option.some.injEq] at hj; subst hj
                  simp only [lowerBlocks] at hpr
                  split at hpr
                  · simp at hpr
                  · split at hpr
                    · simp at hpr
                    · split at hpr
                      · simp at hpr
                      · split at hpr
                        · simp at hpr
                        · split at hpr
                          · simp at hpr
                          · obtain ⟨cr', _, rfl⟩ := prepend_ok hpr
                            have := (List.IsInfixAt.cons (List.IsInfixAt.append hrest).1).1
                            simpa [Nat.add_assoc, Nat.add_comm 1] using this
              · exact lowerBlocks_closed hy hD' hAg hbs' (fun i => ihb (.there i)) (lid + 1) nv1 nl1 ip1 ft
                  cr nv' nl' ip' (kb + (T.frame.label (lname fn lid) :: cbb).length) (Nat.le_trans hle hnv1)
                  hpr hrest (by
                    have e : kb + (T.frame.label (lname fn lid) :: cbb).length + cr.length =
                        kb + (T.frame.label (lname fn lid) :: cbb ++ cr).length := by
                      simp only [List.length_append, List.length_cons]; omega
                    rw [e]; exact hft)
      · simp [hsc] at hpb


theorem run_congr {a b : Nat} {s : T.mach.MData} {p : T.mach.State → Prop} (h : a = b)
    (hr : T.mach.Run host a s p) : T.mach.Run host b s p := h ▸ hr

theorem jnzMode_spec {I : Isa} {h : I.Hints} {ipT ipE : Nat} {st : SymState I} {canInv : Bool}
    {t e : Expr VNat LNat rs} {ft : Option Nat} {inv : Bool} {j : Nat}
    (hm : jnzMode I h ipT ipE st canInv t e ft = (inv, some j)) :
    (inv = false → zeroMoveJump? I h ipT st t = some j) ∧
    (inv = true → zeroMoveJump? I h ipE st e = some j) := by
  unfold jnzMode at hm
  split at hm <;> (try split at hm) <;> simp_all

/-- A zero-move threaded jump (`jnz` taken branch straight to a join point). -/
theorem thread_ok (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx} {D : Ctx Cont LNat}
    {tb₁ : Expr Val Cont rs} {tb₂ : Expr VNat LNat rs} (hwf : Wf G D tb₁ tb₂)
    (hD : DOk T host hints E fn s₀ ra n nX Rf Q X G D)
    {ip : Nat} {stB : SymState T.toIsa} {j : Nat} {m : Mem 64}
    (hz : zeroMoveJump? T.toIsa hints ip stB tb₂ = some j) :
    ∃ kj, (T.mach.prog host)[kj]? = some (T.frame.label (lname fn j)) ∧
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
            simp only [Option.some.injEq] at hz; subst hz
            obtain ⟨⟨kℓ, hlab⟩, G', hGs, rfl⟩ := hD ts j₁ j₂ hj
            refine ⟨kℓ, hlab, fun hwp nv s σ hA hI => ?_⟩
            simp only [wp] at hwp
            have hJ := hwp
            refine enter_labJ hy hGs hargs hen hjt (fun p hp => ?_) hI hlab hJ
            have := List.all_eq_true.mp hall p hp
            simp only [Bool.and_eq_true] at this
            exact holdsLoc_ok hA this.2
          · simp at hz
  | _ => simp [zeroMoveJump?] at hz

theorem keep_of_frame_scratch {s s' : T.mach.MData} {v : List T.VReg} {f : FlagMask}
    (hfr : T.mach.Frame T.gpr.condReads s s' T.frame.scratch v f) :
    ∀ r, isMoveGpr T.toIsa hints.saved r = false → T.mach.getGpr s' r = T.mach.getGpr s r :=
  fun r hr => hfr.1 r fun hm => by simp [isMoveGpr, hm] at hr


theorem FT_congr {a b : Nat} {ft : Option Nat} (h : a = b) (hf : FT T host fn ft a) : FT T host fn ft b :=
  h ▸ hf

theorem FT_none (k : Nat) : FT T host fn none k := fun _ h => nomatch h

theorem Agree.mono_nv {G : VCtx} {nv nv' : Nat} {st : SymState T.toIsa} {s : T.mach.MData}
    {σ : List (BitVec 64)} (hA : Agree T G nv st s σ) (hle : nv ≤ nv') : Agree T G nv' st s σ :=
  hA.extend hle (fun _ hp => .inl hp) (fun _ hp => Nat.lt_of_lt_of_le (hA.ctx_lt _ hp) hle)
    (fun _ hp => hp) (vw' := st.vecWidths) (fun _ _ => rfl)
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
    cf = br ++ (cft ++ ([I.frame.label (lname fn nl)] ++ ctk)) ∧ nv' = nv2 ∧ nl' = nl2 ∧ ip' = ip2 := by
  simp only [finishJnzBranch, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨by rw [← h.1]; simp [List.append_assoc], h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem jnzSetup_thread {I : Isa} {h : I.Hints} {nl ipT ipE : Nat} {st1 : SymState I}
    {t e : Expr VNat LNat rs} {ft : Option Nat} {cond : Sum I.Cond I.Reg} {inv : Bool} {j : Nat}
    {br : List I.Directive} {stBr : SymState I}
    (hs : jnzSetup I h fn nl ipT ipE st1 t e ft cond = (inv, some j, br, stBr)) :
    (inv = false → zeroMoveJump? I h ipT stBr t = some j) ∧
    (inv = true → zeroMoveJump? I h ipE stBr e = some j) := by
  cases cond with
  | inl cc =>
    simp only [jnzSetup, Prod.mk.injEq] at hs
    obtain ⟨h1, h2, -, rfl⟩ := hs
    exact jnzMode_spec (Prod.ext h1 h2)
  | inr r =>
    simp only [jnzSetup, Prod.mk.injEq] at hs
    obtain ⟨rfl, h2, -, rfl⟩ := hs
    refine ⟨fun _ => ?_, fun h => nomatch h⟩
    rw [h2]
    simp only [Option.getD_some]
    unfold gprThread? at h2
    split at h2
    · rename_i j' args
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
      subst hj; exact h2
    · cases h2

theorem jnzSetup_memDefs {I : Isa} {h : I.Hints} {nl ipT ipE : Nat} {st1 : SymState I}
    {t e : Expr VNat LNat rs} {ft : Option Nat} {cond : Sum I.Cond I.Reg} {inv : Bool}
    {tgt : Option Nat} {br : List I.Directive} {stBr : SymState I}
    (hs : jnzSetup I h fn nl ipT ipE st1 t e ft cond = (inv, tgt, br, stBr)) :
    stBr.memDefs = st1.memDefs := by
  cases cond <;> simp only [jnzSetup, Prod.mk.injEq] at hs <;> rw [← hs.2.2.2]

/-- Branch on the `jnz` condition (`jcc` on a flag or `jnzGpr` on a GPR). -/
theorem branch_ok {zl : Bool} (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx}
    {nv nl ipT ipE : Nat} {st1 stBr : SymState T.toIsa} {s1 : T.mach.MData}
    {σ1 : List (BitVec 64)} {m : Mem 64} {cv : Bool} {cx : Nat}
    (hmem : (⟨.bool, cv, cx⟩ : (t : Ty) × Val t × VNat t) ∈ G)
    (hA1 : Agree T G nv st1 s1 σ1) (hI1 : Inv T hints s₀ ra n Rf m s1 σ1 zl)
    {cond : Sum T.Cond T.Reg} (hfc : findJnzCond T.toIsa st1.regs cx = some cond)
    {t e : Expr VNat LNat rs} {ft : Option Nat} {inv : Bool} {tgt : Option Nat}
    {br : List T.Directive}
    (hs : jnzSetup T.toIsa hints fn nl ipT ipE st1 t e ft cond = (inv, tgt, br, stBr))
    {kb kT : Nat} {post : T.mach.State → Prop} (hbr : br.IsInfixAt (T.mach.prog host) kb)
    (hlab : (T.mach.prog host)[kT]? = some (T.frame.label (lname fn (tgt.getD nl))))
    (kont : ∀ s', Agree T G nv stBr s' σ1 → Inv T hints s₀ ra n Rf m s' σ1 zl →
      ((if inv then !cv else cv) = true → T.mach.Run host kT s' post) ∧
      ((if inv then !cv else cv) = false → T.mach.Run host (kb + br.length) s' post)) :
    T.mach.Run host kb s1 post := by
  have hc := findJnzCond_ok hA1 hmem hfc
  have hla := labelAddr_of_unique hy.unique hlab
  cases cond with
  | inl cc =>
    simp only at hc
    simp only [jnzSetup, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    refine T.gprSpec.jcc_spec hbr hla fun s' hfr hm => ?_
    have := kont s' (hA1.kill hfr) (hI1.keep hm (keep_of_frame_scratch hfr))
    have hev : T.mach.evalCond s1 (if (jnzMode T.toIsa hints ipT ipE
        { st1 with regs := killRegs T.toIsa T.frame.scratch [] FlagMask.none st1.regs } true t e ft).1
        then T.gpr.negCond cc else cc) =
        (if (jnzMode T.toIsa hints ipT ipE
        { st1 with regs := killRegs T.toIsa T.frame.scratch [] FlagMask.none st1.regs } true t e ft).1
        then !cv else cv) := by
      split <;> simp_all [T.gprSpec.negCond_eval]
    rw [hev]; exact this
  | inr r =>
    simp only at hc
    simp only [jnzSetup, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    refine T.gprSpec.jnzGpr_spec hbr hla hc.1 hc.2 fun s' hfr hm => ?_
    have := kont s' (hA1.kill hfr) (hI1.keep hm (keep_of_frame_scratch hfr))
    simpa using this

theorem lowerBlocks_labelPos {I : Isa} {h : I.Hints} {E : Ext} {prog : List I.Directive} :
    ∀ {sig : List (List Ty)} (bs : Blocks VNat LNat rs sig) (lid nv nl ip : Nat) (defs : Trie DefFact)
      (vw : Trie SlotWidth) (ft : Option Nat) (cb : List I.Directive) (nv' nl' ip' kb : Nat),
    lowerBlocks I h E fn bs lid nv nl ip defs vw ft = .ok (cb, nv', nl', ip') →
    cb.IsInfixAt prog kb →
    (∀ i, i < sig.length → ∃ k : Nat, prog[k]? = some (I.frame.label (lname fn (lid + i)))) ∧
    (sig ≠ [] → prog[kb]? = some (I.frame.label (lname fn lid)))
  | _, .nil, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => ⟨fun _ hi => by simp at hi, fun h => absurd rfl h⟩
  | _ :: _, .cons b bs, lid, nv, nl, ip, defs, vw, ft, cb, nv', nl', ip', kb, hl, hc => by
    simp only [lowerBlocks] at hl
    split at hl; · simp at hl
    split at hl; · simp at hl
    split at hl; · simp at hl
    split at hl; · simp at hl
    split at hl; · simp at hl
    obtain ⟨cr, hr, rfl⟩ := prepend_ok hl
    have hhead := (List.IsInfixAt.cons (List.IsInfixAt.append hc).1).1
    have ih := lowerBlocks_labelPos bs (lid + 1) _ _ _ defs vw ft cr nv' nl' ip' _ hr (List.IsInfixAt.append hc).2
    refine ⟨fun i hi => ?_, fun _ => hhead⟩
    cases i with
    | zero => exact ⟨kb, by simpa using hhead⟩
    | succ i =>
      obtain ⟨k, hk⟩ := ih.1 i (by simp at hi; omega)
      exact ⟨k, by simpa [Nat.add_assoc, Nat.add_comm 1] using hk⟩


/-- Main theorem: `Wf.induct` correctness of `lowerExpr` (all ten `Expr` forms). -/
theorem lowerExpr_correct (hy : Hyps T host hints E Γ s₀ n nX bound) {G : VCtx} {D : Ctx Cont LNat}
    {e₁ : Expr Val Cont rs} {e₂ : Expr VNat LNat rs} (hwf : Wf G D e₁ e₂) :
    Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂ := by
  refine Wf.induct (motive := fun G D e₁ e₂ _ => Motive T host hints E Γ fn s₀ ra n nX Rf Q X G D e₁ e₂)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hwf
  · -- let_
    intro G D ts op₁ op₂ k₁ k₂ hop _ ih nv nl ip st ft c nv' nl' ip' k s σ m
      hl hc hft hD hA hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hlop : lowerOp T.toIsa hints nv ip st1 op₂ with
      | none => simp [hp, hlop] at hl
      | some p2 =>
        obtain ⟨co, st2⟩ := p2
        simp only [hp, hlop] at hl
        obtain ⟨ck, hlk, rfl⟩ := prepend_ok hl
        obtain ⟨hc1, hck⟩ := List.IsInfixAt.append hc
        obtain ⟨hmc, hco⟩ := List.IsInfixAt.append hc1
        simp only [wp] at hwp
        have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
        refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
        refine lowerOp_ok hy.spE hy.saved_cs hop hlop hco hA1 hM1 hI1 hwp
          fun rvs s2 hP hA2 hM2 hI2 => ?_
        refine run_congr (by simp [Nat.add_assoc]) (ih rvs (Tup.levels ts nv) (nv + ts.length) nl
          (ip + 1) st2 ft ck nv' nl' ip' _ s2 σ1 m hlk hck (FT_congr (by simp [Nat.add_assoc]) hft)
          (hD.weaken fun _ hp => List.mem_append_right _ hp) hA2 hM2 hI2 hP)
  · -- load
    intro G D t a₁ a₂ k₁ k₂ ha _ ih nv nl ip st ft c nv' nl' ip' k s σ m hl hc hft hD hA hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hll : lowerLoad T.toIsa hints nv ip st1 t a₂
          (loadSextNext T.toIsa hints nv ip st1 t a₂ (k₂ nv)) with
      | none => simp [hp, hll] at hl
      | some p2 =>
        obtain ⟨co, st2⟩ := p2
        simp only [hp, hll] at hl
        obtain ⟨ck, hlk, rfl⟩ := prepend_ok hl
        obtain ⟨hc1, hck⟩ := List.IsInfixAt.append hc
        obtain ⟨hmc, hco⟩ := List.IsInfixAt.append hc1
        simp only [wp] at hwp
        obtain ⟨v, hv, hwk⟩ := hwp
        have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
        refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
        refine lowerLoad_ok hy.spE hy.saved_cs ha hll hco hA1 hM1 hI1 hv fun s2 hA2 hM2 hI2 => ?_
        refine run_congr (by simp [Nat.add_assoc]) (ih v nv (nv + 1) nl (ip + 1) st2 ft ck nv' nl' ip' _
          s2 σ1 m hlk hck (FT_congr (by simp [Nat.add_assoc]) hft)
          (hD.weaken fun _ hp => List.mem_cons_of_mem _ hp) hA2 hM2 hI2 hwk)
  · -- store
    intro G D t v₁ v₂ a₁ a₂ k₁ k₂ hv ha _ ih nv nl ip st ft c nv' nl' ip' k s σ m
      hl hc hft hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hls : lowerStore T.toIsa st1 (hints.variant.getD ip .default) t v₂ a₂ with
      | none => simp [hp, hls] at hl
      | some p2 =>
        obtain ⟨co, st2⟩ := p2
        simp only [hp, hls] at hl
        obtain ⟨ck, hlk, rfl⟩ := prepend_ok hl
        obtain ⟨hc1, hck⟩ := List.IsInfixAt.append hc
        obtain ⟨hmc, hco⟩ := List.IsInfixAt.append hc1
        simp only [wp] at hwp
        refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
        refine lowerStore_ok hy.spE hv ha hls hco hA1 hI1 hwp.1 fun s2 hA2 hM2 hI2 => ?_
        refine run_congr (by simp [Nat.add_assoc]) (ih nv nl (ip + 1) st2 ft ck nv' nl' ip' _ s2 σ1 _ hlk hck
          (FT_congr (by simp [Nat.add_assoc]) hft) hD hA2 hM2 hI2 hwp.2)
  · -- call
    intro G D f as bs args₁ args₂ k₁ k₂ hargs _ ih nv nl ip st ft c nv' nl' ip' k s σ m
      hl hc hft hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      simp only [hp] at hl
      split at hl; · simp at hl
      rename_i hcal
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hcal
      cases hal : T.toIsa.assignArgs as with
      | none => simp [hal] at hl
      | some argLocs =>
        cases hrl : T.toIsa.assignRets bs with
        | none => simp [hal, hrl] at hl
        | some retLocs =>
          simp only [hal, hrl] at hl
          cases htg : abiTargets T.toIsa args₂ argLocs with
          | none => simp [htg] at hl
          | some tgts =>
            cases hsh : shuffle T.toIsa hints.nslots hints.saved st1 tgts with
            | none => simp [htg, hsh] at hl
            | some p2 =>
              obtain ⟨sc, st2⟩ := p2
              cases hb : bindAbiParams T.toIsa retLocs nv (afterCallState T.toIsa hints.saved st2) with
              | none => simp [htg, hsh, hb] at hl
              | some st4 =>
                simp only [htg, hsh, hb] at hl
                obtain ⟨ck, hlk, rfl⟩ := prepend_ok hl
                obtain ⟨hc1, hck⟩ := List.IsInfixAt.append hc
                simp only [List.append_assoc] at hc1
                obtain ⟨hmc, hc2⟩ := List.IsInfixAt.append hc1
                obtain ⟨hsc, hcc⟩ := List.IsInfixAt.append hc2
                simp only [wp] at hwp
                obtain ⟨P, X', hspec, hk, hX⟩ := hwp
                have hmd4 : st4.memDefs = .empty := bindAbiParams_memDefs hb
                refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
                refine shuffle_ok hy.spE hsh hsc hA1 hI1 fun s2 σ2 hok hA2 hI2 => ?_
                refine call_ok hy hargs hcal hal hrl htg hb hcc hok hA2 hI2 hspec hX
                  fun rets m' s3 σ3 hP hA3 hI3 => ?_
                refine run_congr (by simp; omega) (ih rets (Tup.levels bs nv) (nv + bs.length) nl
                  (ip + 1) st4 ft ck nv' nl' ip' _ s3 σ3 m' hlk hck (FT_congr (by simp; omega) hft)
                  (hD.weaken fun _ hp => List.mem_append_right _ hp) hA3
                  (hmd4 ▸ MemDefsOk.empty _ _ _) hI3 (hk rets m' hP))
  · -- jnz
    intro G D c₁ c₂ t₁ t₂ e₁ e₂ hcr ht he iht ihe nv nl ip st ft c nv' nl' ip' k s σ m
      hl hc hft hD hA hM hI hwp
    cases hcr with
    | imm b =>
      simp only [lowerExpr] at hl
      cases hp : stepPre T.toIsa hints ip st with
      | none => simp [hp] at hl
      | some p1 =>
        obtain ⟨mc, st1⟩ := p1
        simp only [hp] at hl
        obtain ⟨cb, hlb, rfl⟩ := prepend_ok hl
        obtain ⟨hmc, hcb⟩ := List.IsInfixAt.append hc
        simp only [wp, Arg.val] at hwp
        have hM1 : MemDefsOk G m nv st1.memDefs := stepPre_memDefs hp ▸ hM
        refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
        have hft' : FT T host fn ft (k + mc.length + cb.length) := FT_congr (by simp [Nat.add_assoc]) hft
        cases b
        · simp only [Bool.false_eq_true, ite_false] at hlb
          exact ihe nv nl (ip + 1) st1 ft cb nv' nl' ip' _ s1 σ1 m
            hlb hcb hft' hD hA1 hM1 hI1 (hwp.2 rfl)
        · simp only [ite_true] at hlb
          exact iht nv nl (ip + 1) st1 ft cb nv' nl' ip' _ s1 σ1 m
            hlb hcb hft' hD hA1 hM1 hI1 (hwp.1 rfl)
    | @var cv cx hmem =>
      simp only [lowerExpr] at hl
      cases hp : stepPre T.toIsa hints ip st with
      | none => simp [hp] at hl
      | some p1 =>
        obtain ⟨mc, st1⟩ := p1
        cases hfc : findJnzCond T.toIsa st1.regs cx with
        | none => simp [hp, hfc] at hl
        | some cond =>
          rcases hs : jnzSetup T.toIsa hints fn nl
              (jnzIpT nv nl ip t₂ e₂) (ip + 1) st1 t₂ e₂ ft cond with
            ⟨inv, tgt, br, stBr⟩
          simp only [hp, hfc, hs] at hl
          split at hl; · simp at hl
          rename_i ce nv1 nl1 ip1 hle
          split at hl; · simp at hl
          rename_i ct nv2 nl2 ip2 hlt
          obtain ⟨cf, hfin, rfl⟩ := prepend_ok hl
          obtain ⟨hmc, hcf⟩ := List.IsInfixAt.append hc
          simp only [wp, Arg.val] at hwp
          have hnv1 := (lowerExpr_nv_le hle).1
          have hMBr : MemDefsOk G m nv stBr.memDefs :=
            ((jnzSetup_memDefs hs).trans (stepPre_memDefs hp)) ▸ hM
          have hMBr1 : MemDefsOk G m nv1 stBr.memDefs :=
            hMBr.grow hnv1 (fun _ h => Or.inl h) (fun _ h => h)
          refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
          cases tgt with
          | none =>
            have hcf' := hcf
            cases inv with
            | false =>
              simp only [Bool.false_eq_true, ite_false] at hle hlt hfin
              obtain ⟨hcfe, rfl, rfl, rfl⟩ := finishJnzBranch_none hfin
              rw [hcfe] at hcf' hft
              obtain ⟨hbr, h2⟩ := List.IsInfixAt.append hcf'
              obtain ⟨hce, h3⟩ := List.IsInfixAt.append h2
              obtain ⟨hlab, hct⟩ := List.IsInfixAt.cons h3
              refine branch_ok hy hmem hA1 hI1 hfc hs hbr hlab fun s' hA' hI' => ⟨fun htk => ?_, fun hnt => ?_⟩
              · refine T.frameSpec.label_spec hlab ?_
                exact iht nv1 nl1 ip1 stBr ft ct _ _ _ _ s' σ1 m hlt hct
                  (FT_congr (by simp; omega) hft) hD (hA'.mono_nv hnv1) hMBr1 hI'
                  (hwp.1 (by simpa using htk))
              · exact ihe nv (nl + 1) (ip + 1) stBr none ce nv1 nl1 ip1 _ s' σ1 m
                  hle hce (FT_none _) hD hA' hMBr hI' (hwp.2 (by simpa using hnt))
            | true =>
              simp only [ite_true] at hle hlt hfin
              obtain ⟨hcfe, rfl, rfl, rfl⟩ := finishJnzBranch_none hfin
              rw [hcfe] at hcf' hft
              obtain ⟨hbr, h2⟩ := List.IsInfixAt.append hcf'
              obtain ⟨hct, h3⟩ := List.IsInfixAt.append h2
              obtain ⟨hlab, hce⟩ := List.IsInfixAt.cons h3
              refine branch_ok hy hmem hA1 hI1 hfc hs hbr hlab fun s' hA' hI' => ⟨fun htk => ?_, fun hnt => ?_⟩
              · refine T.frameSpec.label_spec hlab ?_
                exact ihe nv (nl + 1) (ip + 1) stBr ft ce nv1 nl1 ip1 _ s' σ1 m hle hce
                  (FT_congr (by simp; omega) hft) hD hA' hMBr hI' (hwp.2 (by simpa using htk))
              · exact iht nv1 nl1 ip1 stBr none ct _ _ _ _ s' σ1 m hlt hct (FT_none _) hD
                  (hA'.mono_nv hnv1) hMBr1 hI' (hwp.1 (by simpa using hnt))
          | some j =>
            have hth := jnzSetup_thread hs
            cases inv with
            | false =>
              simp only [Bool.false_eq_true, ite_false] at hle hlt hfin
              obtain ⟨rfl, rfl, rfl, rfl⟩ := finishJnzBranch_some hfin
              obtain ⟨hbr, hce⟩ := List.IsInfixAt.append hcf
              obtain ⟨kj, hlab, hrun⟩ := thread_ok hy ht hD (hth.1 rfl)
              refine branch_ok hy hmem hA1 hI1 hfc hs hbr hlab fun s' hA' hI' => ⟨fun htk => ?_, fun hnt => ?_⟩
              · exact hrun (hwp.1 (by simpa using htk)) nv s' σ1 hA' hI'
              · exact ihe nv (nl + 1) (ip + 1) stBr ft ce nv1 nl1 ip1 _ s' σ1 m hle hce
                  (FT_congr (by simp [Nat.add_assoc]) hft) hD hA' hMBr hI'
                  (hwp.2 (by simpa using hnt))
            | true =>
              simp only [ite_true] at hle hlt hfin
              obtain ⟨rfl, rfl, rfl, rfl⟩ := finishJnzBranch_some hfin
              obtain ⟨hbr, hct⟩ := List.IsInfixAt.append hcf
              obtain ⟨kj, hlab, hrun⟩ := thread_ok hy he hD (hth.2 rfl)
              refine branch_ok hy hmem hA1 hI1 hfc hs hbr hlab fun s' hA' hI' => ⟨fun htk => ?_, fun hnt => ?_⟩
              · exact hrun (hwp.2 (by simpa using htk)) nv s' σ1 hA' hI'
              · exact iht nv1 nl1 ip1 stBr ft ct _ _ _ _ s' σ1 m hlt hct
                  (FT_congr (by simp [Nat.add_assoc]) hft) hD (hA'.mono_nv hnv1) hMBr1 hI'
                  (hwp.1 (by simpa using hnt))
  · -- jump
    intro G D ts j₁ j₂ args₁ args₂ hj hargs nv nl ip st ft c nv' nl' ip' k s σ m
      hl hc hft hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hen : hints.entry.find? j₂ with
      | none => simp [hp, hen] at hl
      | some en =>
        cases hjt : jumpTargets T.toIsa args₂ en.ploc with
        | none => simp [hp, hen, hjt] at hl
        | some argTgts =>
          simp only [hp, hen, hjt] at hl
          split at hl; · simp at hl
          rename_i hlocs
          cases hsh : shuffle T.toIsa hints.nslots hints.saved st1 (en.live ++ argTgts) with
          | none => simp [hsh] at hl
          | some p2 =>
            obtain ⟨sc, st2⟩ := p2
            simp only [hsh, Except.ok.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, -, -, -⟩ := hl
            obtain ⟨⟨kℓ, hlabℓ⟩, G', hGs, hJeq⟩ := hD ts j₁ j₂ hj
            subst hJeq
            simp only [wp] at hwp
            simp only [List.append_assoc] at hc hft
            obtain ⟨hmc, hc2⟩ := List.IsInfixAt.append hc
            obtain ⟨hsc, hc3⟩ := List.IsInfixAt.append hc2
            simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true] at hlocs
            refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
            refine shuffle_ok hy.spE hsh hsc hA1 hI1 fun s2 σ2 hok hA2 hI2 => ?_
            by_cases hfj : (ft == some j₂) = true
            · simp only [hfj, ite_true, List.append_nil] at hft hc3
              have hl0 := hft j₂ (by simpa using hfj)
              exact enter_labJ hy hGs hargs hen hjt hok hI2 (by simpa [Nat.add_assoc] using hl0) hwp
            · simp only [hfj, Bool.false_eq_true, ite_false] at hc3
              refine T.gprSpec.jmp_spec hc3 (labelAddr_of_unique hy.unique hlabℓ) fun s3 hfr hm => ?_
              refine enter_labJ hy hGs hargs hen hjt (fun p hp => ?_) (hI2.keep hm (keep_of_frame_scratch hfr))
                hlabℓ hwp
              have hjl := jumpLocOk_spec (hlocs p hp)
              exact LocOk.frame hfr (hok p hp) hjl.1 (fun _ _ => List.not_mem_nil)
                (fun _ _ => FlagMask.disjoint_none _)
  · -- ret
    intro G D vs₁ vs₂ hvs nv nl ip st ft c nv' nl' ip' k s σ m hl hc hft hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hrl : T.toIsa.assignRets rs with
      | none => simp [hp, hrl] at hl
      | some retLocs =>
        simp only [hp, hrl, lowerTail] at hl
        cases htg : abiTargets T.toIsa vs₂ retLocs with
        | none => simp [htg] at hl
        | some tgts =>
          cases hsh : shuffle T.toIsa hints.nslots hints.saved st1 tgts with
          | none => simp [htg, hsh] at hl
          | some p2 =>
            obtain ⟨sc, st2⟩ := p2
            simp only [htg, hsh, Except.ok.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, -, -, -⟩ := hl
            simp only [List.append_assoc] at hc
            obtain ⟨hmc, hc2⟩ := List.IsInfixAt.append hc
            obtain ⟨hsc, hc3⟩ := List.IsInfixAt.append hc2
            simp only [wp] at hwp
            refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
            refine shuffle_ok hy.spE hsh hsc hA1 hI1 fun s2 σ2 hok hA2 hI2 => ?_
            exact ret_ok hy hvs hrl htg (by simpa only [List.append_assoc] using hc3) hok hA2 hI2
              hwp
  · -- exit
    intro G D f as args₁ args₂ hargs nv nl ip st ft c nv' nl' ip' k s σ m hl hc hft hD hA _hM hI hwp
    simp only [lowerExpr] at hl
    cases hp : stepPre T.toIsa hints ip st with
    | none => simp [hp] at hl
    | some p1 =>
      obtain ⟨mc, st1⟩ := p1
      cases hal : T.toIsa.assignArgs as with
      | none => simp [hp, hal] at hl
      | some argLocs =>
        simp only [hp, hal] at hl
        split at hl; · simp at hl
        rename_i hex
        simp only [Bool.not_eq_true', Bool.not_eq_false] at hex
        simp only [lowerTail] at hl
        cases htg : abiTargets T.toIsa args₂ argLocs with
        | none => simp [htg] at hl
        | some tgts =>
          cases hsh : shuffle T.toIsa hints.nslots hints.saved st1 tgts with
          | none => simp [htg, hsh] at hl
          | some p2 =>
            obtain ⟨sc, st2⟩ := p2
            simp only [htg, hsh, Except.ok.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, -, -, -⟩ := hl
            simp only [List.append_assoc] at hc
            obtain ⟨hmc, hc2⟩ := List.IsInfixAt.append hc
            obtain ⟨hsc, hc3⟩ := List.IsInfixAt.append hc2
            simp only [wp] at hwp
            refine stepPre_ok hy.spE hp hmc hA hI fun s1 σ1 hA1 hI1 => ?_
            refine shuffle_ok hy.spE hsh hsc hA1 hI1 fun s2 σ2 hok hA2 hI2 => ?_
            exact exit_ok hy hargs hex hal htg (by simpa only [List.append_assoc] using hc3) hok hA2
              hI2 hwp
  · -- hlt
    intro G D nv nl ip st ft c nv' nl' ip' k s σ m _ _ _ _ _ _ _ hwp
    exact absurd hwp (by simp [wp])
  · -- group
    intro G D sig b₁ b₂ k₁ k₂ hb _ ihb ihk nv nl ip st ft c nv' nl' ip' k s σ m
      hl hc hft hD hA hM hI hwp
    simp only [lowerExpr] at hl
    split at hl; · simp at hl
    rename_i ck nv1 nl1 ip1 hlk
    obtain ⟨cb, hpb, rfl⟩ := prepend_ok hl
    obtain ⟨hck, hcb⟩ := List.IsInfixAt.append hc
    have hlabs := lowerBlocks_labelPos (prog := T.mach.prog host) (b₂ (Tup.levels sig nl)) nl nv1 nl1 ip1
      st.defs st.vecWidths ft cb nv' nl' ip' _ hpb hcb
    have hD' := makeLabJs_dok (T := T) (host := host) (hints := hints) (E := E) (s₀ := s₀)
      (ra := ra) (n := n) (nX := nX) (Rf := Rf) (Q := Q) (X := X) (G := G) sig nl hlabs.1 hD
    have hnv1 : nv ≤ nv1 := (lowerExpr_nv_le hlk).1
    have hnil : sig = [] → cb = [] := by
      intro hs; subst hs
      revert hpb; generalize b₂ (Tup.levels [] nl) = bs; intro hpb
      cases bs; simp only [lowerBlocks, Except.ok.injEq, Prod.mk.injEq] at hpb; exact hpb.1.symm
    have hClosed := lowerBlocks_closed hy hD' hA (hb _ (Tup.levels sig nl))
      (fun i xs₁ xs₂ => ihb _ (Tup.levels sig nl) i xs₁ xs₂) nl nv1 nl1 ip1 ft cb nv' nl' ip'
      (k + ck.length) hnv1 hpb hcb (FT_congr (by simp [Nat.add_assoc]) hft)
    simp only [wp] at hwp
    refine ihk _ (Tup.levels sig nl) nv (nl + sig.length) ip st _ ck nv1 nl1 ip1 k s σ m
      hlk hck ?_ hD' hA hM hI (hwp _ hClosed)
    intro j hj
    split at hj
    · simpa [hnil rfl] using hft j hj
    · simp only [Option.some.injEq] at hj; subst hj
      exact hlabs.2 (List.cons_ne_nil _ _)

end Main

/-! ## Function-level correctness -/

/-- **`T7b` headline:** a successfully lowered well-formed function satisfies `Target.FnSpec`. -/
theorem lowerFn_correct (T : Target) (host : T.mach.Host) (hints : T.toIsa.Hints) (E : Ext) (f : Fn)
    (Γ : Env) (n nX : Nat) (bound : Sym → Nat) {code : List T.Directive} {k₀ : Nat}
    (hwf : f.Wf) (hl : lowerFn T.toIsa hints E f = .ok code)
    (hc : code.IsInfixAt (T.mach.prog host) k₀) (hu : T.LabelsUnique host)
    (hfr : effFrame T.toIsa hints E ≤ n) (hn : n + T.frame.raBytes ≤ 2 ^ 64)
    (hcal : ∀ g as bs, (g, as, bs) ∈ E.callees →
      T.FnSpec host g (Γ g as bs) (bound g) nX ∧
        effFrame T.toIsa hints E + T.frame.raBytes + bound g ≤ n)
    (hex : ∀ g, g ∈ E.exits → T.Defined host g ∧ nX ≤ n) :
    T.FnSpec host f.name (Func.spec Γ f.body) n nX := by
  unfold lowerFn at hl
  split at hl; · simp at hl
  rename_i hsv
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, List.all_eq_true] at hsv
  cases hal : T.toIsa.assignArgs f.as with
  | none => simp [hal] at hl
  | some argLocs =>
    cases hrl : T.toIsa.assignRets f.rs with
    | none => simp [hal, hrl] at hl
    | some retLocs =>
      simp only [hal, hrl] at hl
      cases hb : bindAbiParams T.toIsa argLocs 0
          { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
      | none => simp [hb] at hl
      | some st0 =>
        simp only [hb] at hl
        split at hl
        · rename_i c nv' nl' ip' hle
          simp only [Except.ok.injEq] at hl
          subst hl
          intro args m Q X hspec s ra R hargs hra hspE hmem
          have hy : Hyps T host hints E Γ s n nX bound :=
            { unique := hu, spE := hspE, frame_le := hfr, frame_bound := by omega, stack_bound := hn,
              saved_cs := fun r hr => by simpa using hsv.2 r hr, saved_nodup := listNodup_nodup hsv.1,
              callees := hcal, exits := hex }
          have hmd0 : st0.memDefs = .empty := bindAbiParams_memDefs hb
          obtain ⟨hlab, hrest⟩ := List.IsInfixAt.cons hc
          rw [labelAddr_of_unique hu hlab]
          refine T.frameSpec.label_spec hlab ?_
          obtain ⟨hpro, hbody⟩ := List.IsInfixAt.append hrest
          refine fn_entry_ok hy hargs hra hmem hal hb hpro fun s' σ hA hI => ?_
          exact lowerExpr_correct (fn := f.name) (Q := Q) (X := X) (Rf := R) (ra := ra) hy
            (hwf Val VNat Cont LNat args (Tup.levels f.as 0)) f.as.length 0 0 st0 none c nv' nl' ip' _ s' σ m
            hle hbody (FT_none _) (fun _ _ _ h => nomatch h) hA
            (hmd0 ▸ MemDefsOk.empty _ _ _) hI hspec
        · simp at hl

end Rega
end LeanQbe.T
