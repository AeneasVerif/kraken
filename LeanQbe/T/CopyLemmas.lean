module

public import LeanQbe.T.Copy
public import LeanQbe.T.FoldLemmas

/-!
# Correctness of `copy` (`T6`)

* `OpRel.copyLet_wp`: `copyLet` preserves weakest preconditions and `CGoodCtx`.
* `OpRel.copyLet_rel`: `copyLet` produces relationally equivalent actions under `CRelG`.
* `copy_wp`: source `wp` implies copy-propagated `wp`, proved via `Wf.induct`.
* `copy_wf`: `Wf` is preserved, proved via `Wf.induct`.
* `Func.copy_spec`, `Func.copy_wf`: closed-function specifications.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Copy environment and semantic invariant `CopyGood` -/

abbrev CEnv := Nat → Option ((t : Ty) × Val t)

def cupd (ρ : CEnv) {t : Ty} (b : Nat) (v : Val t) : CEnv :=
  fun k => if k = b then some ⟨t, v⟩ else ρ k

def cupdTup (ρ : CEnv) (b : Nat) : {ts : List Ty} → Tup Val ts → CEnv
  | [], () => ρ
  | _ :: _, (x, xs) => cupdTup (cupd ρ b x) (b + 1) xs

theorem cupd_eq (ρ : CEnv) {t : Ty} (b : Nat) (v : Val t) :
    cupd ρ b v b = some ⟨t, v⟩ := by
  simp [cupd]

theorem cupd_ne (ρ : CEnv) {t : Ty} {b k : Nat} (v : Val t) (h : k ≠ b) :
    cupd ρ b v k = ρ k := by
  simp [cupd, h]

theorem cupdTup_lt (ρ : CEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → {b k : Nat} →
    k < b → cupdTup ρ b xs k = ρ k
  | [], (), _, _, _ => rfl
  | _ :: _, (x, xs), b, k, hk => by
    simp only [cupdTup]
    rw [cupdTup_lt (cupd ρ b x) xs (by omega)]
    exact cupd_ne ρ x (by omega)

mutual
def CopyGood (ρ : CEnv) (bound : Nat) : {t : Ty} → CVal Val t → Val t → Prop
  | t, .mk out id parts fstOf sndOf, v =>
    out.val = v ∧
    (∀ k, id = some k → k < bound ∧ ρ k = some ⟨t, v⟩) ∧
    CGoodParts ρ bound parts v ∧
    CGoodFst ρ bound fstOf v ∧
    CGoodSnd ρ bound sndOf v

def CGoodParts (ρ : CEnv) (bound : Nat) : {t : Ty} → CParts Val t → Val t → Prop
  | _, .unknown, _ => True
  | .pair _ _, .pair x y, v => CopyGood ρ bound x v.1 ∧ CopyGood ρ bound y v.2

def CGoodFst (ρ : CEnv) (bound : Nat) : {t : Ty} → CProjFst Val t → Val t → Prop
  | _, .none, _ => True
  | a, .some (b := b) pid p, v =>
    ∃ u : Val b, pid < bound ∧ ρ pid = some ⟨.pair a b, (v, u)⟩ ∧ CopyGood ρ bound p (v, u)

def CGoodSnd (ρ : CEnv) (bound : Nat) : {t : Ty} → CProjSnd Val t → Val t → Prop
  | _, .none, _ => True
  | b, .some (a := a) pid p, v =>
    ∃ u : Val a, pid < bound ∧ ρ pid = some ⟨.pair a b, (u, v)⟩ ∧ CopyGood ρ bound p (u, v)
end

mutual
theorem CopyGood.mono {ρ ρ' : CEnv} {bound bound' : Nat}
    (hb : bound ≤ bound') (hρ : ∀ k, k < bound → ρ' k = ρ k) :
    {t : Ty} → {c : CVal Val t} → {v : Val t} →
    CopyGood ρ bound c v → CopyGood ρ' bound' c v
  | _, .mk _ _ _ _ _, _, h => by
    simp only [CopyGood] at h ⊢
    rcases h with ⟨ho, hid, hp, hf, hs⟩
    exact ⟨ho,
      fun k hk => by obtain ⟨hlt, hpk⟩ := hid k hk; exact ⟨by omega, (hρ k hlt).trans hpk⟩,
      CGoodParts.mono hb hρ hp, CGoodFst.mono hb hρ hf, CGoodSnd.mono hb hρ hs⟩

theorem CGoodParts.mono {ρ ρ' : CEnv} {bound bound' : Nat}
    (hb : bound ≤ bound') (hρ : ∀ k, k < bound → ρ' k = ρ k) :
    {t : Ty} → {p : CParts Val t} → {v : Val t} →
    CGoodParts ρ bound p v → CGoodParts ρ' bound' p v
  | _, .unknown, _, _ => trivial
  | .pair _ _, .pair _ _, _, h => by
    simp only [CGoodParts] at h ⊢
    exact ⟨CopyGood.mono hb hρ h.1, CopyGood.mono hb hρ h.2⟩

theorem CGoodFst.mono {ρ ρ' : CEnv} {bound bound' : Nat}
    (hb : bound ≤ bound') (hρ : ∀ k, k < bound → ρ' k = ρ k) :
    {t : Ty} → {f : CProjFst Val t} → {v : Val t} →
    CGoodFst ρ bound f v → CGoodFst ρ' bound' f v
  | _, .none, _, _ => trivial
  | _, .some pid _, _, h => by
    simp only [CGoodFst] at h ⊢
    rcases h with ⟨u, hlt, hp, hcg⟩
    exact ⟨u, by omega, (hρ pid hlt).trans hp, CopyGood.mono hb hρ hcg⟩

theorem CGoodSnd.mono {ρ ρ' : CEnv} {bound bound' : Nat}
    (hb : bound ≤ bound') (hρ : ∀ k, k < bound → ρ' k = ρ k) :
    {t : Ty} → {s : CProjSnd Val t} → {v : Val t} →
    CGoodSnd ρ bound s v → CGoodSnd ρ' bound' s v
  | _, .none, _, _ => trivial
  | _, .some pid _, _, h => by
    simp only [CGoodSnd] at h ⊢
    rcases h with ⟨u, hlt, hp, hcg⟩
    exact ⟨u, by omega, (hρ pid hlt).trans hp, CopyGood.mono hb hρ hcg⟩
end

theorem CopyGood.cupd {ρ : CEnv} {bound : Nat} {t u : Ty} {w : Val u}
    {c : CVal Val t} {v : Val t} (h : CopyGood ρ bound c v) :
    CopyGood (cupd ρ bound w) (bound + 1) c v :=
  h.mono (Nat.le_succ _) fun _ hk => cupd_ne ρ w (Nat.ne_of_lt hk)

theorem CopyGood.cupdTup {ρ : CEnv} {bound : Nat} {ts : List Ty} (xs : Tup Val ts)
    {t : Ty} {c : CVal Val t} {v : Val t} (h : CopyGood ρ bound c v) :
    CopyGood (cupdTup ρ bound xs) (bound + ts.length) c v :=
  h.mono (Nat.le_add_right _ _) fun _ hk => cupdTup_lt ρ xs hk

theorem CopyGood.ofImm (ρ : CEnv) (bound : Nat) :
    (t : Ty) → (c : Val t) → CopyGood ρ bound (CVal.ofImm t c) c
  | .bool, c => by simp [CVal.ofImm, CopyGood, CGoodParts, CGoodFst, CGoodSnd]
  | .bits _, c => by simp [CVal.ofImm, CopyGood, CGoodParts, CGoodFst, CGoodSnd]
  | .float _, c => by simp [CVal.ofImm, CopyGood, CGoodParts, CGoodFst, CGoodSnd]
  | .pair a b, (c₁, c₂) => by
    simp only [CVal.ofImm, CopyGood, CGoodParts, CGoodFst, CGoodSnd]
    exact ⟨rfl, (fun _ h => nomatch h), ⟨CopyGood.ofImm ρ bound a c₁, CopyGood.ofImm ρ bound b c₂⟩,
      trivial, trivial⟩

/-- Context invariant for `copy_wp`: every entry in `G` has `CopyGood ρ bound`. -/
def CGoodCtx (ρ : CEnv) (bound : Nat) (G : Ctx (CVal Val) Val) : Prop :=
  ∀ p ∈ G, CopyGood ρ bound p.2.1 p.2.2

theorem CGoodCtx.cons {ρ : CEnv} {bound : Nat} {G : Ctx (CVal Val) Val}
    (hG : CGoodCtx ρ bound G) {t : Ty} {c : CVal Val t} {v : Val t}
    (hc : CopyGood ρ bound c v) :
    CGoodCtx ρ bound (⟨t, c, v⟩ :: G)
  | _, .head _ => hc
  | _, .tail _ hp => hG _ hp

theorem CGoodCtx.upd_all {ρ : CEnv} {bound : Nat} {G : Ctx (CVal Val) Val}
    (hG : CGoodCtx ρ bound G) {ts : List Ty} (xs : Tup Val ts) :
    CGoodCtx (cupdTup ρ bound xs) (bound + ts.length) G :=
  fun p hp => (hG p hp).cupdTup xs

theorem CGoodCtx.append {ρ : CEnv} {bound : Nat} {G₁ G₂ : Ctx (CVal Val) Val}
    (h1 : CGoodCtx ρ bound G₁) (h2 : CGoodCtx ρ bound G₂) : CGoodCtx ρ bound (G₁ ++ G₂) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

theorem CGoodCtx.append_tup {ρ : CEnv} {bound : Nat} {G : Ctx (CVal Val) Val}
    (hG : CGoodCtx ρ bound G) :
    {ts : List Ty} → {cs : Tup (CVal Val) ts} → {xs : Tup Val ts} →
    TRel (fun _ => CopyGood ρ bound) cs xs → CGoodCtx ρ bound (Tup.zip cs xs ++ G)
  | [], (), (), .nil => hG
  | _ :: _, (_, _), (_, _), .cons hc hs =>
    (CGoodCtx.append_tup hG hs).cons hc

private theorem CGoodCtx.freshCVals_only (ρ : CEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    CGoodCtx (cupdTup ρ b xs) (b + ts.length) (Tup.zip (freshCVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | t :: ts, (x, xs), b => by
    simp only [freshCVals, Tup.zip, cupdTup, List.length_cons]
    intro p hp
    cases hp with
    | head =>
      simp only [CVal.fresh, CopyGood, CGoodParts, CGoodFst, CGoodSnd]
      refine ⟨rfl, fun k hk => ?_, trivial, trivial, trivial⟩
      cases hk
      refine ⟨by omega, ?_⟩
      rw [cupdTup_lt (cupd ρ b x) xs (by omega), cupd_eq]
    | tail _ hp =>
      have ih := CGoodCtx.freshCVals_only (cupd ρ b x) xs (b + 1) p hp
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem CGoodCtx.freshCVals {ρ : CEnv} {b : Nat} {G : Ctx (CVal Val) Val}
    (hG : CGoodCtx ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    CGoodCtx (cupdTup ρ b xs) (b + ts.length) (Tup.zip (freshCVals ts xs b) xs ++ G) :=
  (CGoodCtx.freshCVals_only ρ xs b).append (hG.upd_all xs)

theorem CGoodCtx.freshOne {ρ : CEnv} {b : Nat} {G : Ctx (CVal Val) Val}
    (hG : CGoodCtx ρ b G) {t : Ty} (v : Val t) :
    CGoodCtx (cupd ρ b v) (b + 1) (⟨t, CVal.fresh v b, v⟩ :: G) :=
  (hG.upd_all (ts := [t]) (v, ())).cons
    (by
      simp only [CVal.fresh, CopyGood, CGoodParts, CGoodFst, CGoodSnd]
      exact ⟨rfl, fun k hk => by cases hk; exact ⟨Nat.lt_succ_self b, cupd_eq ρ b v⟩,
        trivial, trivial, trivial⟩)

theorem ArgRel.toCVal_good {ρ : CEnv} {b : Nat} {G : Ctx (CVal Val) Val} (hG : CGoodCtx ρ b G)
    {t : Ty} {a₁ : Arg (CVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → CopyGood ρ b a₁.toCVal a₂.val
  | .var h => hG _ h
  | .imm c => CopyGood.ofImm ρ b t c

theorem ArgRel.cout_val {ρ : CEnv} {b : Nat} {G : Ctx (CVal Val) Val} (hG : CGoodCtx ρ b G)
    {t : Ty} : {a₁ : Arg (CVal Val) t} → {a₂ : Arg Val t} →
    ArgRel G t a₁ a₂ → a₁.cout.val = a₂.val
  | .var (.mk _ _ _ _ _), _, .var h => (hG _ h).1
  | .imm _, _, .imm _ => rfl

theorem TRel.cout_vals {ρ : CEnv} {b : Nat} {G : Ctx (CVal Val) Val} (hG : CGoodCtx ρ b G) :
    {ts : List Ty} → {as₁ : Tup (Arg (CVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → vals (tupCOut as₁) = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (h.cout_val hG) (TRel.cout_vals hG hs)

/-- Reconcile matching `fst` and `snd` projections from the same `unpair` identity `pid`. -/
theorem CopyGood.fst_snd_pair {ρ : CEnv} {b : Nat} {a a₂ b₁ b₂ : Ty} {pid : Nat}
    {va : Val a} {vb : Val b₂}
    {p₁ : CVal Val (.pair a b₁)} {p₂ : CVal Val (.pair a₂ b₂)}
    (hb : b₁ = b₂)
    (hfst : CGoodFst ρ b (.some (b := b₁) pid p₁) va)
    (hsnd : CGoodSnd ρ b (.some (a := a₂) pid p₂) vb) :
    CopyGood ρ b (cast (congrArg (fun u => CVal Val (.pair a u)) hb) p₁) (va, vb) := by
  subst hb
  simp only [CGoodFst, CGoodSnd] at hfst hsnd
  rcases hfst with ⟨u₁, _, hρ₁, hp₁⟩
  rcases hsnd with ⟨u₂, _, hρ₂, _⟩
  rw [hρ₁] at hρ₂
  injection hρ₂ with heq
  cases heq
  exact hp₁

/-! ## `Op.copyLet` soundness and `copy_wp` -/

private theorem mkpairEmitStep_wp {ρ : CEnv} {b : Nat} {G : Ctx (CVal Val) Val}
    (hG : CGoodCtx ρ b G) {a b' : Ty} {cx : CVal Val a} {cy : CVal Val b'}
    {vx : Val a} {vy : Val b'} (hcx : CopyGood ρ b cx vx) (hcy : CopyGood ρ b cy vy)
    {P : Tup Val [.pair a b'] → Prop} (hw : P ((vx, vy), ())) :
    match mkpairEmitStep b a b' cx cy with
    | .elim res => ∃ ys, P ys ∧ CGoodCtx ρ b (Tup.zip res ys ++ G)
    | .emit op' next' wrap =>
      op'.wp fun ys => P ys ∧ ∃ ρ', CGoodCtx ρ' next' (Tup.zip (wrap ys) ys ++ G) := by
  simp only [mkpairEmitStep, Op.wp, op2, OpCode.wp_mkpair, vals]
  have hox : cx.out.val = vx := by cases cx; exact hcx.1
  have hoy : cy.out.val = vy := by cases cy; exact hcy.1
  rw [hox, hoy]
  refine ⟨hw, cupd ρ (t := .pair a b') b (vx, vy), ?_⟩
  have hcg : CopyGood (cupd ρ (t := .pair a b') b (vx, vy)) (b + 1)
      (.mk (.var (vx, vy)) (some b) (.pair cx cy) .none .none) (vx, vy) := by
    simp only [CopyGood, CGoodParts, CGoodFst, CGoodSnd]
    exact ⟨rfl, fun k hk => by cases hk; exact ⟨Nat.lt_succ_self b, cupd_eq ρ b _⟩,
      ⟨hcx.cupd, hcy.cupd⟩, trivial, trivial⟩
  simpa [Tup.zip, cupdTup] using (hG.upd_all (ts := [.pair a b']) ((vx, vy), ())).cons hcg

private theorem mkpairProjStep_wp {ρ : CEnv} {b : Nat} {G : Ctx (CVal Val) Val}
    (hG : CGoodCtx ρ b G) {a b' : Ty} {cx : CVal Val a} {cy : CVal Val b'}
    {vx : Val a} {vy : Val b'} (hcx : CopyGood ρ b cx vx) (hcy : CopyGood ρ b cy vy)
    {P : Tup Val [.pair a b'] → Prop} (hw : P ((vx, vy), ())) :
    match mkpairProjStep b a b' cx cy with
    | .elim res => ∃ ys, P ys ∧ CGoodCtx ρ b (Tup.zip res ys ++ G)
    | .emit op' next' wrap =>
      op'.wp fun ys => P ys ∧ ∃ ρ', CGoodCtx ρ' next' (Tup.zip (wrap ys) ys ++ G) := by
  unfold mkpairProjStep
  dsimp only
  cases hfst : cx.fstOf with
  | none =>
    cases hsnd : cy.sndOf <;> exact mkpairEmitStep_wp hG hcx hcy hw
  | @some _ b₁ pid₁ p₁ =>
    cases hsnd : cy.sndOf with
    | none => exact mkpairEmitStep_wp hG hcx hcy hw
    | @some a₂ _ pid₂ p₂ =>
      dsimp only
      cases hpid : (pid₁ == pid₂)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact mkpairEmitStep_wp hG hcx hcy hw
      · simp only [↓reduceIte]
        obtain rfl : pid₁ = pid₂ := eq_of_beq hpid
        cases hdec : tyDecEq b₁ b' with
        | isFalse _ => exact mkpairEmitStep_wp hG hcx hcy hw
        | isTrue hb =>
          dsimp only
          have hcfst : CGoodFst ρ b (.some (b := b₁) pid₁ p₁) vx := by
            cases hc : cx; rw [hc] at hcx hfst; exact hfst ▸ hcx.2.2.2.1
          have hcsnd : CGoodSnd ρ b (.some (a := a₂) pid₁ p₂) vy := by
            cases hc : cy; rw [hc] at hcy hsnd; exact hsnd ▸ hcy.2.2.2.2
          have hp1' := CopyGood.fst_snd_pair hb hcfst hcsnd
          subst hb
          simp only [cast_eq] at hp1' ⊢
          refine ⟨((vx, vy), ()), hw, ?_⟩
          have hp1'_eq : CopyGood ρ b (.mk p₁.out p₁.id (.pair cx cy) p₁.fstOf p₁.sndOf)
              (vx, vy) := by
            cases p₁
            simp only [CopyGood] at hp1' ⊢
            exact ⟨hp1'.1, hp1'.2.1, ⟨hcx, hcy⟩, hp1'.2.2.2.1, hp1'.2.2.2.2⟩
          simpa [Tup.zip] using hG.cons hp1'_eq

theorem OpRel.copyLet_wp {ρ : CEnv} {b : Nat} {G : Ctx (CVal Val) Val} (hG : CGoodCtx ρ b G)
    {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (CVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂)
    {P : Tup Val ts → Prop} (hw : code.wp (vals args₂) P) :
    match ({ code := code, args := args₁ } : Op (CVal Val) ts).copyLet b with
    | .elim res =>
      ∃ ys, P ys ∧ CGoodCtx ρ b (Tup.zip res ys ++ G)
    | .emit op' next' wrap =>
      op'.wp fun ys =>
        P ys ∧
          ∃ ρ', CGoodCtx ρ' next' (Tup.zip (wrap ys) ys ++ G) := by
  unfold Op.copyLet
  dsimp only
  cases code with
  | copy t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩
    rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    simp only [OpCode.wp_copy, vals] at hw
    exact ⟨(a₂.val, ()), hw, hG.cons (ha.toCVal_good hG)⟩
  | unpair a b' =>
    rcases args₁ with ⟨p₁, ⟨⟩⟩
    rcases args₂ with ⟨p₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hp, _⟩
    dsimp only
    have hcp := hp.toCVal_good hG
    simp only [OpCode.wp_unpair, vals] at hw
    cases hparts : p₁.toCVal.parts with
    | pair x y =>
      cases hcp_eq : p₁.toCVal with
      | mk o id parts f s =>
        rw [hcp_eq] at hcp hparts
        dsimp only [CVal.parts] at hparts
        subst hparts
        simp only [CopyGood, CGoodParts] at hcp
        exact ⟨(p₂.val.1, p₂.val.2, ()), hw, (hG.cons hcp.2.2.1.2).cons hcp.2.2.1.1⟩
    | unknown =>
      dsimp only [Op.wp, op1, OpCode.wp_unpair, vals]
      have hout : p₁.toCVal.out.val = p₂.val := by
        cases hcp_eq : p₁.toCVal; rw [hcp_eq] at hcp; exact hcp.1
      rw [hout]
      refine ⟨hw, ?_⟩
      cases hid : p₁.toCVal.id with
      | none =>
        refine ⟨cupdTup ρ b (ts := [a, b']) (p₂.val.1, p₂.val.2, ()), ?_⟩
        have hf := hG.freshCVals (ts := [a, b']) (p₂.val.1, p₂.val.2, ())
        simpa [freshCVals, Tup.zip] using hf
      | some pid =>
        refine ⟨cupdTup ρ b (ts := [a, b']) (p₂.val.1, p₂.val.2, ()), ?_⟩
        have hcp' := hcp
        cases hcp_eq : p₁.toCVal
        rw [hcp_eq] at hcp' hid
        dsimp only [CVal.id] at hid
        subst hid
        simp only [CopyGood] at hcp'
        obtain ⟨hplt, hpρ⟩ := hcp'.2.1 pid rfl
        have hp_mono : CopyGood (cupdTup ρ b (ts := [a, b']) (p₂.val.1, p₂.val.2, ())) (b + 2)
            p₁.toCVal p₂.val :=
          hcp.cupdTup (ts := [a, b']) (p₂.val.1, p₂.val.2, ())
        have hρpid : cupdTup ρ b (ts := [a, b']) (p₂.val.1, p₂.val.2, ()) pid =
            some ⟨.pair a b', p₂.val⟩ := by
          rw [cupdTup_lt (ts := [a, b']) ρ (p₂.val.1, p₂.val.2, ()) hplt]
          exact hpρ
        have hfst : CopyGood (cupdTup ρ b (ts := [a, b']) (p₂.val.1, p₂.val.2, ())) (b + 2)
            (.mk (.var p₂.val.1) (some b) .unknown (.some pid p₁.toCVal) .none) p₂.val.1 := by
          simp only [CopyGood, CGoodParts, CGoodFst, CGoodSnd]
          refine ⟨rfl, fun k hk => ?_, trivial,
            ⟨p₂.val.2, by omega, by simpa using hρpid, hp_mono⟩, trivial⟩
          cases hk
          refine ⟨by omega, ?_⟩
          simp only [cupdTup]
          rw [cupd_ne _ _ (by omega), cupd_eq]
        have hsnd : CopyGood (cupdTup ρ b (ts := [a, b']) (p₂.val.1, p₂.val.2, ())) (b + 2)
            (.mk (.var p₂.val.2) (some (b + 1)) .unknown .none (.some pid p₁.toCVal)) p₂.val.2 := by
          simp only [CopyGood, CGoodParts, CGoodFst, CGoodSnd]
          refine ⟨rfl, fun k hk => ?_, trivial, trivial,
            ⟨p₂.val.1, by omega, by simpa using hρpid, hp_mono⟩⟩
          cases hk
          exact ⟨by omega, by simp [cupdTup, cupd_eq]⟩
        have hf_eq : b + [a, b'].length = b + 2 := rfl
        rw [← hf_eq]
        simpa [Tup.zip, hcp_eq] using
          ((hG.upd_all (ts := [a, b']) (p₂.val.1, p₂.val.2, ())).cons hsnd).cons hfst
  | mkpair a b' =>
    rcases args₁ with ⟨x₁, y₁, ⟨⟩⟩
    rcases args₂ with ⟨x₂, y₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hx, _ | ⟨hy, _⟩⟩
    dsimp only
    have hcx := hx.toCVal_good hG
    have hcy := hy.toCVal_good hG
    simp only [OpCode.wp_mkpair, vals] at hw
    unfold mkpairStep
    cases hxout : x₁.toCVal.out with
    | var _ =>
      dsimp only
      cases hst : mkpairProjStep b a b' x₁.toCVal y₁.toCVal <;>
        (have hp := mkpairProjStep_wp hG hcx hcy hw; rw [hst] at hp; exact hp)
    | imm c₁ =>
      cases hyout : y₁.toCVal.out with
      | var _ =>
        dsimp only
        cases hst : mkpairProjStep b a b' x₁.toCVal y₁.toCVal <;>
          (have hp := mkpairProjStep_wp hG hcx hcy hw; rw [hst] at hp; exact hp)
      | imm c₂ =>
        dsimp only
        have h1 : x₁.toCVal.out.val = x₂.val := by cases h : x₁.toCVal; rw [h] at hcx; exact hcx.1
        have h2 : y₁.toCVal.out.val = y₂.val := by cases h : y₁.toCVal; rw [h] at hcy; exact hcy.1
        rw [hxout] at h1; rw [hyout] at h2
        refine ⟨((x₂.val, y₂.val), ()), hw, ?_⟩
        have hcg : CopyGood ρ b
            (.mk (.imm (c₁, c₂)) none (.pair x₁.toCVal y₁.toCVal) .none .none)
            (x₂.val, y₂.val) := by
          simp only [CopyGood, CGoodParts, CGoodFst, CGoodSnd]
          exact ⟨Prod.ext h1 h2, (fun _ h => nomatch h), ⟨hcx, hcy⟩, trivial, trivial⟩
        simpa [Tup.zip] using hG.cons hcg
  | _ =>
    all_goals
      (dsimp only [Op.wp]
       rw [hargs.cout_vals hG]
       refine OpCode.wp_mono _ _ (fun ys hys => ?_) hw
       exact ⟨hys, cupdTup ρ b ys, hG.freshCVals ys⟩)

theorem copyB_get {V₁ : Ty → Type} {L₁ : List Ty → Type} {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (CVal V₁) L₁ rs sig) →
    (i : Member ts sig) → (xs : Tup V₁ ts) →
    (copyB b bs).get i xs = copy (b + ts.length) (bs.get i (freshCVals ts xs b))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => copyB_get b bs i xs

/-- Weakest-precondition preservation for `copy`, proved via `Wf.induct`. -/
theorem copy_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (CVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (CVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ b ρ, CGoodCtx ρ b G → ∀ m, wp Γ Q X e₂ m → wp Γ Q X (copy b e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD b ρ hG m hw
    simp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hstep := OpRel.copyLet_wp hG hargs hw
      simp only [copy]
      cases hcl : ({ code := code, args := args₁ } : Op (CVal Val) ts).copyLet b with
      | elim res =>
        rw [hcl] at hstep
        rcases hstep with ⟨ys, hk2, hG'⟩
        exact ih res ys hD b ρ hG' m hk2
      | emit op' next' wrap =>
        rw [hcl] at hstep
        simp only [wp]
        exact Op.wp_mono (fun ys ⟨hk2, ρ', hG'⟩ => ih (wrap ys) ys hD next' ρ' hG' m hk2) hstep
  | load t ha _ ih =>
    intro hD b ρ hG m hw
    simp only [wp, copy] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, ha.cout_val hG ▸ hv,
      ih (CVal.fresh v b) v hD (b + 1) (cupd ρ b v) (hG.freshOne v) m hk⟩
  | store hv ha _ ih =>
    intro hD b ρ hG m hw
    simp only [wp, copy] at hw ⊢
    rw [ha.cout_val hG, hv.cout_val hG]
    exact ⟨hw.1, ih hD b ρ hG _ hw.2⟩
  | call f hargs _ ih =>
    intro hD b ρ hG m hw
    simp only [wp, copy] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    rw [hargs.cout_vals hG]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshCVals _ r b) r hD (b + _) (cupdTup ρ b r) (hG.freshCVals r) m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hD b ρ hG m hw
    simp only [wp, copy] at hw ⊢
    rw [hc.cout_val hG]
    exact ⟨fun h => iht hD b ρ hG m (hw.1 h), fun h => ihe hD b ρ hG m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD b ρ hG m hw
    have hj' := hD _ hj; dsimp only at hj'
    simp only [wp, copy] at hw ⊢
    rw [hj', hargs.cout_vals hG]
    exact hw
  | ret hvs =>
    intro _ b ρ hG m hw
    simp only [wp, copy] at hw ⊢
    rw [hvs.cout_vals hG]
    exact hw
  | exit f hargs =>
    intro _ b ρ hG m hw
    simp only [wp, copy] at hw ⊢
    rw [hargs.cout_vals hG]
    exact hw
  | hlt =>
    intro _ _ _ _ _ hw
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD b ρ hG m hw
    simp only [wp, copy] at hw ⊢
    intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) b ρ hG m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb
    have hcopy := ihb Js Js i (freshCVals ts xs b) xs (tup_zip_self_eq hD Js)
      (b + ts.length) (cupdTup ρ b xs) (hG.freshCVals xs) m' hb
    rw [← copyB_get b (b₁ Js) i xs] at hcopy
    exact hclosed i xs m' hcopy

/-! ## Relational well-formedness for `copy` (`CRel` and `copy_wf`) -/

section
variable {V₁ V₂ : Ty → Type}

mutual
inductive CRelVal (G' : Ctx V₁ V₂) : {t : Ty} → CVal V₁ t → CVal V₂ t → Prop
  | mk {t : Ty} {o₁ : Arg V₁ t} {o₂ : Arg V₂ t} {id : Option Nat}
      {p₁ : CParts V₁ t} {p₂ : CParts V₂ t}
      {f₁ : CProjFst V₁ t} {f₂ : CProjFst V₂ t}
      {s₁ : CProjSnd V₁ t} {s₂ : CProjSnd V₂ t} :
      ArgRel G' t o₁ o₂ → CRelParts G' p₁ p₂ → CRelFst G' f₁ f₂ → CRelSnd G' s₁ s₂ →
      CRelVal G' (.mk o₁ id p₁ f₁ s₁) (.mk o₂ id p₂ f₂ s₂)

inductive CRelParts (G' : Ctx V₁ V₂) : {t : Ty} → CParts V₁ t → CParts V₂ t → Prop
  | unknown {t : Ty} : CRelParts G' (.unknown (t := t)) .unknown
  | pair {a b : Ty} {x₁ : CVal V₁ a} {x₂ : CVal V₂ a} {y₁ : CVal V₁ b} {y₂ : CVal V₂ b} :
      CRelVal G' x₁ x₂ → CRelVal G' y₁ y₂ → CRelParts G' (.pair x₁ y₁) (.pair x₂ y₂)

inductive CRelFst (G' : Ctx V₁ V₂) : {t : Ty} → CProjFst V₁ t → CProjFst V₂ t → Prop
  | none {t : Ty} : CRelFst G' (.none (t := t)) .none
  | some {a b : Ty} (pid : Nat) {p₁ : CVal V₁ (.pair a b)} {p₂ : CVal V₂ (.pair a b)} :
      CRelVal G' p₁ p₂ → CRelFst G' (.some pid p₁) (.some pid p₂)

inductive CRelSnd (G' : Ctx V₁ V₂) : {t : Ty} → CProjSnd V₁ t → CProjSnd V₂ t → Prop
  | none {t : Ty} : CRelSnd G' (.none (t := t)) .none
  | some {a b : Ty} (pid : Nat) {p₁ : CVal V₁ (.pair a b)} {p₂ : CVal V₂ (.pair a b)} :
      CRelVal G' p₁ p₂ → CRelSnd G' (.some pid p₁) (.some pid p₂)
end

mutual
theorem CRelVal.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {t : Ty} → {c₁ : CVal V₁ t} → {c₂ : CVal V₂ t} → CRelVal G₁ c₁ c₂ → CRelVal G₂ c₁ c₂
  | _, _, _, .mk ho hp hf hs =>
    .mk (ho.weaken hsub) (hp.weaken hsub) (hf.weaken hsub) (hs.weaken hsub)

theorem CRelParts.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {t : Ty} → {p₁ : CParts V₁ t} → {p₂ : CParts V₂ t} → CRelParts G₁ p₁ p₂ → CRelParts G₂ p₁ p₂
  | _, _, _, .unknown => .unknown
  | _, _, _, .pair hx hy => .pair (hx.weaken hsub) (hy.weaken hsub)

theorem CRelFst.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {t : Ty} → {f₁ : CProjFst V₁ t} → {f₂ : CProjFst V₂ t} → CRelFst G₁ f₁ f₂ → CRelFst G₂ f₁ f₂
  | _, _, _, .none => .none
  | _, _, _, .some pid hp => .some pid (hp.weaken hsub)

theorem CRelSnd.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {t : Ty} → {s₁ : CProjSnd V₁ t} → {s₂ : CProjSnd V₂ t} → CRelSnd G₁ s₁ s₂ → CRelSnd G₂ s₁ s₂
  | _, _, _, .none => .none
  | _, _, _, .some pid hp => .some pid (hp.weaken hsub)
end

theorem CRelVal.ofImm (G' : Ctx V₁ V₂) :
    (t : Ty) → (c : Val t) → CRelVal G' (CVal.ofImm t c) (CVal.ofImm t c)
  | .bool, c => .mk (.imm c) .unknown .none .none
  | .bits _, c => .mk (.imm c) .unknown .none .none
  | .float _, c => .mk (.imm c) .unknown .none .none
  | .pair a b, (c₁, c₂) =>
    .mk (.imm (t := .pair a b) (c₁, c₂)) (.pair (CRelVal.ofImm G' a c₁) (CRelVal.ofImm G' b c₂))
      .none .none

theorem CRelVal.fresh {G' : Ctx V₁ V₂} {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} (b : Nat)
    (hm : ⟨t, v₁, v₂⟩ ∈ G') :
    CRelVal G' (CVal.fresh v₁ b) (CVal.fresh v₂ b) :=
  .mk (.var hm) .unknown .none .none

def CRelG (G' : Ctx V₁ V₂) (G : Ctx (CVal V₁) (CVal V₂)) : Prop :=
  ∀ p ∈ G, CRelVal G' p.2.1 p.2.2

theorem CRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)} (hG : CRelG G' G)
    {t : Ty} {c₁ : CVal V₁ t} {c₂ : CVal V₂ t} (hc : CRelVal G' c₁ c₂) :
    CRelG G' (⟨t, c₁, c₂⟩ :: G)
  | _, .head _ => hc
  | _, .tail _ hp => hG _ hp

theorem CRelG.append {G' : Ctx V₁ V₂} {G H : Ctx (CVal V₁) (CVal V₂)}
    (h1 : CRelG G' G) (h2 : CRelG G' H) : CRelG G' (H ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h2 p hp
  · exact h1 p hp

theorem CRelG.weaken {G' G'' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)}
    (hG : CRelG G' G) (hsub : ∀ p ∈ G', p ∈ G'') : CRelG G'' G :=
  fun p hp => (hG p hp).weaken hsub

theorem CRelG.append_tup {G' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)} (hG : CRelG G' G) :
    {ts : List Ty} → {r₁ : Tup (CVal V₁) ts} → {r₂ : Tup (CVal V₂) ts} →
    TRel (fun _ => CRelVal G') r₁ r₂ → CRelG G' (Tup.zip r₁ r₂ ++ G)
  | [], (), (), .nil => hG
  | _ :: _, (_, _), (_, _), .cons hr hs => (CRelG.append_tup hG hs).cons hr

private theorem CRelG.freshCVals_only :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) → (b : Nat) →
    CRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshCVals ts xs₁ b) (freshCVals ts xs₂ b))
  | [], (), (), _ => fun _ hp => nomatch hp
  | t :: ts, (x₁, xs₁), (x₂, xs₂), b => by
    simp only [freshCVals, Tup.zip]
    intro p hp
    cases hp with
    | head => exact CRelVal.fresh b List.mem_cons_self
    | tail _ hp =>
      exact (CRelG.freshCVals_only xs₁ xs₂ (b + 1) p hp).weaken fun _ hq => List.mem_cons_of_mem _ hq

theorem CRelG.freshCVals {G' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)} (hG : CRelG G' G)
    {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    CRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshCVals ts xs₁ b) (freshCVals ts xs₂ b) ++ G) :=
  (hG.weaken fun _ hq => List.mem_append_right _ hq).append
    ((CRelG.freshCVals_only xs₁ xs₂ b).weaken fun _ hq => List.mem_append_left G' hq)

theorem CRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)} (hG : CRelG G' G)
    {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    CRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, CVal.fresh v₁ b, CVal.fresh v₂ b⟩ :: G) :=
  (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq).cons
    (CRelVal.fresh b List.mem_cons_self)

theorem TRel.weaken_cval {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {ts : List Ty} → {r₁ : Tup (CVal V₁) ts} → {r₂ : Tup (CVal V₂) ts} →
    TRel (fun _ => CRelVal G₁) r₁ r₂ → TRel (fun _ => CRelVal G₂) r₁ r₂
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs => .cons (h.weaken hsub) (TRel.weaken_cval hsub hs)

theorem TRel.freshCVals_rel {G' : Ctx V₁ V₂} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) → (b : Nat) →
    TRel (fun _ => CRelVal (Tup.zip xs₁ xs₂ ++ G')) (freshCVals ts xs₁ b) (freshCVals ts xs₂ b)
  | [], (), (), _ => .nil
  | _ :: _, (_, xs₁), (_, xs₂), b => by
    simp only [freshCVals, Tup.zip, List.cons_append]
    exact .cons (CRelVal.fresh b List.mem_cons_self)
      (TRel.weaken_cval (fun _ hq => List.mem_cons_of_mem _ hq)
        (TRel.freshCVals_rel (G' := G') xs₁ xs₂ (b + 1)))

theorem ArgRel.toCVal_rel {G' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)} (hG : CRelG G' G)
    {t : Ty} {a₁ : Arg (CVal V₁) t} {a₂ : Arg (CVal V₂) t} :
    ArgRel G t a₁ a₂ → CRelVal G' a₁.toCVal a₂.toCVal
  | .var h => hG _ h
  | .imm c => CRelVal.ofImm G' t c

theorem ArgRel.cout {G' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)} (hG : CRelG G' G)
    {t : Ty} : {a₁ : Arg (CVal V₁) t} → {a₂ : Arg (CVal V₂) t} →
    ArgRel G t a₁ a₂ → ArgRel G' t a₁.cout a₂.cout
  | .var (.mk _ _ _ _ _), .var (.mk _ _ _ _ _), .var h => by
    have hc := hG _ h; cases hc with | mk ho _ _ _ => exact ho
  | .imm c, _, .imm _ => .imm c

theorem TRel.cout {G' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)} (hG : CRelG G' G) :
    {ts : List Ty} → {as₁ : Tup (Arg (CVal V₁)) ts} → {as₂ : Tup (Arg (CVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ → TRel (ArgRel G') (tupCOut as₁) (tupCOut as₂)
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs => .cons (h.cout hG) (TRel.cout hG hs)

inductive CopyStepRel (G' : Ctx V₁ V₂) :
    {ts : List Ty} → CopyLetStep V₁ ts → CopyLetStep V₂ ts → Prop
  | elim {ts : List Ty} {r₁ : Tup (CVal V₁) ts} {r₂ : Tup (CVal V₂) ts} :
      TRel (fun _ => CRelVal G') r₁ r₂ → CopyStepRel G' (.elim r₁) (.elim r₂)
  | emit {ts : List Ty} {o₁ : Op V₁ ts} {o₂ : Op V₂ ts} (next' : Nat)
      {w₁ : Tup V₁ ts → Tup (CVal V₁) ts} {w₂ : Tup V₂ ts → Tup (CVal V₂) ts} :
      OpRel G' o₁ o₂ →
      (∀ xs₁ xs₂, TRel (fun _ => CRelVal (Tup.zip xs₁ xs₂ ++ G')) (w₁ xs₁) (w₂ xs₂)) →
      CopyStepRel G' (.emit o₁ next' w₁) (.emit o₂ next' w₂)

private theorem mkpairEmitStep_rel {G' : Ctx V₁ V₂} (b : Nat) {a b' : Ty}
    {cx₁ : CVal V₁ a} {cx₂ : CVal V₂ a} {cy₁ : CVal V₁ b'} {cy₂ : CVal V₂ b'}
    (hox : ArgRel G' a cx₁.out cx₂.out) (hoy : ArgRel G' b' cy₁.out cy₂.out)
    (hcx : CRelVal G' cx₁ cx₂) (hcy : CRelVal G' cy₁ cy₂) :
    CopyStepRel G' (mkpairEmitStep b a b' cx₁ cy₁) (mkpairEmitStep b a b' cx₂ cy₂) := by
  refine .emit (b + 1) (.mk (.mkpair a b') (.cons hox (.cons hoy .nil))) fun xs₁ xs₂ => ?_
  rcases xs₁ with ⟨vp₁, ⟨⟩⟩
  rcases xs₂ with ⟨vp₂, ⟨⟩⟩
  have hsub : ∀ p ∈ G', p ∈ (Tup.zip (as := [.pair a b']) (vp₁, ()) (vp₂, ()) ++ G') :=
    fun _ hp => List.mem_cons_of_mem _ hp
  exact .cons (.mk (.var List.mem_cons_self) (.pair (hcx.weaken hsub) (hcy.weaken hsub)) .none .none)
    .nil

private theorem mkpairProjStep_rel {G' : Ctx V₁ V₂} (b : Nat) {a b' : Ty}
    {cx₁ : CVal V₁ a} {cx₂ : CVal V₂ a} {cy₁ : CVal V₁ b'} {cy₂ : CVal V₂ b'}
    (hcx : CRelVal G' cx₁ cx₂) (hcy : CRelVal G' cy₁ cy₂) :
    CopyStepRel G' (mkpairProjStep b a b' cx₁ cy₁) (mkpairProjStep b a b' cx₂ cy₂) := by
  have hcx' := hcx; have hcy' := hcy
  cases hcx with
  | mk hox hpx hfx hsx =>
    cases hcy with
    | mk hoy hpy hfy hsy =>
      simp only [mkpairProjStep, CVal.fstOf, CVal.sndOf]
      cases hfx with
      | none =>
        cases hsy <;> exact mkpairEmitStep_rel b hox hoy hcx' hcy'
      | @some _ b₁ pid₁ p₁₁ p₁₂ hp₁ =>
        cases hsy with
        | none => exact mkpairEmitStep_rel b hox hoy hcx' hcy'
        | some pid₂ hp₂ =>
          simp only
          cases hpid : (pid₁ == pid₂)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact mkpairEmitStep_rel b hox hoy hcx' hcy'
          · simp only [↓reduceIte]
            cases hdec : tyDecEq b₁ b' with
            | isFalse _ => exact mkpairEmitStep_rel b hox hoy hcx' hcy'
            | isTrue hb =>
              subst hb
              cases hp₁ with
              | @mk _ po₁ po₂ pid _ _ pf₁ pf₂ ps₁ ps₂ hp₁o _ hp₁f hp₁s =>
                exact .elim (.cons (.mk hp₁o (.pair hcx' hcy') hp₁f hp₁s) .nil)

theorem OpRel.copyLet_rel {G' : Ctx V₁ V₂} {G : Ctx (CVal V₁) (CVal V₂)} (hG : CRelG G' G)
    (b : Nat) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (CVal V₁)) sig} {args₂ : Tup (Arg (CVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    CopyStepRel G'
      (({ code := code, args := args₁ } : Op (CVal V₁) ts).copyLet b)
      (({ code := code, args := args₂ } : Op (CVal V₂) ts).copyLet b) := by
  unfold Op.copyLet
  dsimp only
  cases code with
  | copy t =>
    rcases args₁ with ⟨a₁, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hargs with _ | ⟨ha, _⟩
    exact .elim (.cons (ha.toCVal_rel hG) .nil)
  | unpair a b' =>
    rcases args₁ with ⟨p₁, ⟨⟩⟩; rcases args₂ with ⟨p₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hp, _⟩
    dsimp only
    have hcp := hp.toCVal_rel hG
    generalize p₁.toCVal = cp₁ at hcp ⊢
    generalize p₂.toCVal = cp₂ at hcp ⊢
    cases hcp with
    | @mk _ o₁ o₂ cid _ _ f₁ f₂ s₁ s₂ ho hparts hfst hsnd =>
      cases hparts with
      | pair hx hy => exact .elim (.cons hx (.cons hy .nil))
      | unknown =>
        refine .emit (b + 2) (.mk (.unpair a b') (.cons ho .nil)) fun xs₁ xs₂ => ?_
        rcases xs₁ with ⟨vx₁, vy₁, ⟨⟩⟩; rcases xs₂ with ⟨vx₂, vy₂, ⟨⟩⟩
        have hsub : ∀ p ∈ G', p ∈ (Tup.zip (as := [a, b']) (vx₁, vy₁, ()) (vx₂, vy₂, ()) ++ G') :=
          fun _ hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
        have hvx : ⟨a, vx₁, vx₂⟩ ∈ (Tup.zip (as := [a, b']) (vx₁, vy₁, ()) (vx₂, vy₂, ()) ++ G') :=
          List.mem_cons_self
        have hvy : ⟨b', vy₁, vy₂⟩ ∈ (Tup.zip (as := [a, b']) (vx₁, vy₁, ()) (vx₂, vy₂, ()) ++ G') :=
          List.mem_cons_of_mem _ List.mem_cons_self
        have hcp' : CRelVal (Tup.zip (as := [a, b']) (vx₁, vy₁, ()) (vx₂, vy₂, ()) ++ G')
            (.mk o₁ cid .unknown f₁ s₁) (.mk o₂ cid .unknown f₂ s₂) :=
          .mk (ho.weaken hsub) .unknown (hfst.weaken hsub) (hsnd.weaken hsub)
        cases cid with
        | none => exact .cons (CRelVal.fresh b hvx) (.cons (CRelVal.fresh (b + 1) hvy) .nil)
        | some pid =>
          exact .cons (.mk (.var hvx) .unknown (.some pid hcp') .none)
            (.cons (.mk (.var hvy) .unknown .none (.some pid hcp')) .nil)
  | mkpair a b' =>
    rcases args₁ with ⟨x₁, y₁, ⟨⟩⟩; rcases args₂ with ⟨x₂, y₂, ⟨⟩⟩
    rcases hargs with _ | ⟨hx, _ | ⟨hy, _⟩⟩
    dsimp only
    have hcx := hx.toCVal_rel hG; have hcy := hy.toCVal_rel hG
    generalize x₁.toCVal = cx₁ at hcx ⊢
    generalize x₂.toCVal = cx₂ at hcx ⊢
    generalize y₁.toCVal = cy₁ at hcy ⊢
    generalize y₂.toCVal = cy₂ at hcy ⊢
    have hcx' := hcx; have hcy' := hcy
    cases hcx with
    | mk hox _ _ _ =>
      cases hcy with
      | mk hoy _ _ _ =>
        unfold mkpairStep
        cases hox with
        | imm c₁ =>
          cases hoy with
          | imm c₂ => exact .elim (.cons (.mk (.imm _) (.pair hcx' hcy') .none .none) .nil)
          | var _ => exact mkpairProjStep_rel b hcx' hcy'
        | var _ => exact mkpairProjStep_rel b hcx' hcy'
  | _ =>
    all_goals
      exact .emit (b + _) (.mk _ (TRel.cout hG hargs)) fun xs₁ xs₂ =>
        TRel.freshCVals_rel xs₁ xs₂ b

end

/-- Well-formedness preservation for `copy`, proved via `Wf.induct`. -/
theorem copy_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (CVal V₁) (CVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (CVal V₁) L₁ rs} {e₂ : Expr (CVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, CRelG G' G → ∀ b, Wf G' D (copy b e₁) (copy b e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG b
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hrel := OpRel.copyLet_rel hG b hargs (code := code)
      simp only [copy]
      generalize ({ code := code, args := args₁ } : Op (CVal V₁) ts).copyLet b = st₁ at hrel ⊢
      generalize ({ code := code, args := args₂ } : Op (CVal V₂) ts).copyLet b = st₂ at hrel ⊢
      cases hrel with
      | elim hr =>
        exact ih _ _ (hG.append_tup hr) b
      | emit next' hop' hw =>
        refine .let_ hop' fun xs₁ xs₂ => ?_
        have hG' : CRelG (Tup.zip xs₁ xs₂ ++ G') G :=
          hG.weaken fun _ hq => List.mem_append_right _ hq
        exact ih _ _ (hG'.append_tup (hw xs₁ xs₂)) next'
  | load t ha _ ih =>
    intro G' hG b
    exact .load t (ha.cout hG) fun v₁ v₂ => ih _ _ (hG.freshOne v₁ v₂ b) (b + 1)
  | store hv ha _ ih =>
    intro G' hG b
    exact .store (hv.cout hG) (ha.cout hG) (ih hG b)
  | call f hargs _ ih =>
    intro G' hG b
    exact .call f (TRel.cout hG hargs) fun xs₁ xs₂ => ih _ _ (hG.freshCVals xs₁ xs₂ b) (b + _)
  | jnz hc _ _ iht ihe =>
    intro G' hG b
    exact .jnz (hc.cout hG) (iht hG b) (ihe hG b)
  | jump hj hargs =>
    intro G' hG _
    exact .jump hj (TRel.cout hG hargs)
  | ret hvs =>
    intro G' hG _
    exact .ret (TRel.cout hG hvs)
  | exit f hargs =>
    intro G' hG _
    exact .exit f (TRel.cout hG hargs)
  | hlt =>
    intro _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hG b
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ihk Js₁ Js₂ hG b)
    rw [copyB_get, copyB_get]
    exact ihb Js₁ Js₂ i _ _ (hG.freshCVals xs₁ xs₂ b) (b + _)

/-! ## Closed functions -/

theorem Func.copy_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.copy f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (CVal V₁) (CVal V₂) L₁ L₂ (freshCVals as xs₁ 0) (freshCVals as xs₂ 0)
  have hrel : CRelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshCVals as xs₁ 0) (freshCVals as xs₂ 0)) := by
    simpa using CRelG.freshCVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact LeanQbe.T.copy_wf hwf hrel as.length

/-- Copy and pair propagation refines function contracts: any source contract holds on `Func.copy f`. -/
theorem Func.copy_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.copy f) xs m Q X := by
  have hwf := hf (CVal Val) Val Cont Cont (freshCVals as xs 0) xs
  have hgood : CGoodCtx (cupdTup (fun _ => none) 0 xs) as.length
      (Tup.zip (freshCVals as xs 0) xs) := by
    simpa using CGoodCtx.freshCVals (ρ := fun _ => none) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact LeanQbe.T.copy_wp hwf (fun _ hp => nomatch hp) as.length _ hgood m h

end LeanQbe.T
