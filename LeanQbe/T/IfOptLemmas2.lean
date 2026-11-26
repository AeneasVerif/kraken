module

public import LeanQbe.T.IfOptLemmas1
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassEnvKit

/-!
# Store-Sinking Diamond Hoisting `WP` Soundness

Split from `LeanQbe.T.IfOptLemmas` to keep every file `< 1,800` LOC.
Proves `hoistStoreTail_*_wp`, `hoistStoreStep_{taken,untaken_E,untaken_T}_wp`,
and `hoistStoreArms_wp`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open IfOptImpl

namespace IfOptImpl

/-! ## Store-sinking `WP` helpers -/

private theorem iargGood_of_argRel {ρ : FEnv} {b : Nat} {G : Ctx (IVal Val) Val}
    (hG : IGood ρ b G) {t : Ty} {a₁ : Arg (IVal Val) t} {a₂ : Arg Val t}
    (ha : ArgRel G t a₁ a₂) : IArgGood ρ b a₁ a₂.val := by
  cases ha with
  | var hm => exact hG _ hm
  | imm _ => exact ⟨rfl, rfl, trivial⟩

private theorem fev_fupd_of_not_in {ρ : FEnv} {D : Nat → Bool} {t : Ty} (vn : Nat) (v : Val t)
    (hnot : D vn = false) :
    ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev (fupd ρ vn v) = fk.fev ρ
  | _, .var i, hi => by
    have hne : i ≠ vn := fun h => by subst h; simp [KeyIn, hnot] at hi
    exact fupd_ne ρ v hne
  | _, .imm _, _ => rfl

private theorem fev_fupdTup_of_disjoint {ρ : FEnv} {D : Nat → Bool} :
    {ts : List Ty} → (s : Nat) → (r : Tup Val ts) →
    (∀ i, s ≤ i → i < s + ts.length → D i = false) →
    ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev (fupdTup ρ s r) = fk.fev ρ
  | [], _, (), _, _, _, _ => rfl
  | _ :: ts, s, (v, r), hdisj, _, fk, hk => by
    have h1 := fev_fupdTup_of_disjoint (ρ := fupd ρ s v) (ts := ts) (s + 1) r
      (fun i hi1 hi2 => hdisj i (by omega) (by simp only [List.length_cons]; omega)) fk hk
    have h2 := fev_fupd_of_not_in (ρ := ρ) s v
      (hdisj s (Nat.le_refl _) (by simp only [List.length_cons]; omega)) fk hk
    have h0 : fk.fev (fupdTup (ts := _ :: ts) ρ s (v, r)) =
        fk.fev (fupdTup (fupd ρ s v) (s + 1) r) := by
      cases fk <;> rfl
    exact h0.trans (h1.trans h2)

private theorem fKeysEval_congr_in {D : Nat → Bool} {ρ ρ' : FEnv}
    (heq : ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ' = fk.fev ρ) :
    {ts : List Ty} → {ks : Tup FKey ts} → fKeysIn D ks → fKeysEval ρ' ks = fKeysEval ρ ks
  | [], (), _ => rfl
  | _ :: _, (_, _), ⟨h1, h2⟩ => Prod.ext (heq _ h1) (fKeysEval_congr_in heq h2)

private theorem addKeys_disjoint_lt {D : Nat → Bool} {b : Nat} :
    {ts : List Ty} → {ks : Tup FKey ts} →
    fKeysLt b ks → (∀ i, D i = true → i < b) → ∀ i, addKeys D ks i = true → i < b
  | [], (), _, hD, i, hi => hD i hi
  | _ :: _, (k, ks), ⟨hk1, hk2⟩, hD, i, hi => by
    refine addKeys_disjoint_lt hk2 ?_ i hi
    intro j hj
    cases k with
    | imm _ => exact hD j hj
    | var v =>
      simp only [addKey, addVN, Bool.or_eq_true, beq_iff_eq] at hj
      rcases hj with hj | rfl
      · exact hD j hj
      · exact hk1

private theorem addKey_eq_of_keyIn {D : Nat → Bool} {u : Ty} :
    {k : FKey u} → KeyIn D k → ∀ i, addKey D k i = D i
  | .imm _, _, _ => rfl
  | .var v, hk, i => by
    dsimp only [addKey, addVN]
    by_cases h : i = v
    · subst h; simp only [KeyIn] at hk; simp [hk]
    · simp [h]

private theorem addKeys_congr {D₁ D₂ : Nat → Bool} (h : ∀ i, D₁ i = D₂ i) :
    {ts : List Ty} → (ks : Tup FKey ts) → ∀ i, addKeys D₁ ks i = addKeys D₂ ks i
  | [], (), i => h i
  | _ :: _, (k, ks), i => by
    dsimp only [addKeys]
    refine addKeys_congr (fun j => ?_) ks i
    cases k with
    | imm _ => exact h j
    | var v => simp only [addKey, addVN, h j]

private theorem addKeys_eq_of_fKeysIn {D : Nat → Bool} :
    {ts : List Ty} → {ks : Tup FKey ts} →
    fKeysIn D ks → ∀ i, addKeys D ks i = D i
  | [], (), _, _ => rfl
  | _ :: _, (k, ks), ⟨hk1, hk2⟩, i => by
    dsimp only [addKeys]
    exact (addKeys_congr (addKey_eq_of_keyIn hk1) ks i).trans (addKeys_eq_of_fKeysIn hk2 i)

private theorem addKeys_freshFKeys_spec :
    (ts : List Ty) → (D : Nat → Bool) → (s i : Nat) →
    addKeys D (freshFKeys ts s) i =
      (D i || (decide (s ≤ i) && decide (i < s + ts.length)))
  | [], D, s, i => by
    dsimp only [freshFKeys, addKeys, List.length_nil]
    cases D i with
    | true => simp
    | false =>
      have hzero : (decide (s ≤ i) && decide (i < s + 0)) = false := by
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp only [Bool.false_or, hzero]
  | _ :: ts, D, s, i => by
    dsimp only [freshFKeys, addKeys, addKey, addVN, List.length_cons]
    rw [addKeys_freshFKeys_spec ts _ (s + 1) i]
    dsimp only [addVN]
    cases D i with
    | true => simp
    | false =>
      simp only [Bool.false_or]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      omega

private theorem fKeysIn_freshFKeys_of_all {D : Nat → Bool} :
    (ts : List Ty) → (s : Nat) →
    (∀ i, s ≤ i → i < s + ts.length → D i = true) →
    fKeysIn D (freshFKeys ts s)
  | [], _, _ => trivial
  | _ :: ts, s, hall => by
    refine ⟨hall s (Nat.le_refl _) (by simp only [List.length_cons]; omega), ?_⟩
    exact fKeysIn_freshFKeys_of_all ts (s + 1)
      (fun i h1 h2 => hall i (by omega) (by simp only [List.length_cons]; omega))

private theorem fKeysIn_freshFKeys_addVN {D : Nat → Bool} {vn : Nat} :
    (ts : List Ty) → (s : Nat) → (vn < s ∨ s + ts.length ≤ vn) →
    fKeysIn (addVN D vn) (freshFKeys ts s) → fKeysIn D (freshFKeys ts s)
  | [], _, _, _ => trivial
  | _ :: ts, s, hdisj, ⟨h1, h2⟩ => by
    have hne : s ≠ vn := by simp only [List.length_cons] at hdisj; omega
    have h1' : D s = true := by
      simp only [KeyIn, addVN, Bool.or_eq_true, beq_iff_eq] at h1
      exact h1.resolve_right hne
    refine ⟨h1', fKeysIn_freshFKeys_addVN ts (s + 1) ?_ h2⟩
    simp only [List.length_cons] at hdisj; omega

private theorem fKeysIn_freshFKeys_addKeys_disjoint {D : Nat → Bool}
    {ts₀ : List Ty} {s₀ : Nat} :
    (ts : List Ty) → (s : Nat) → (s + ts.length ≤ s₀ ∨ s₀ + ts₀.length ≤ s) →
    fKeysIn (addKeys D (freshFKeys ts₀ s₀)) (freshFKeys ts s) →
    fKeysIn D (freshFKeys ts s)
  | [], _, _, _ => trivial
  | _ :: ts, s, hdisj, ⟨h1, h2⟩ => by
    simp only [KeyIn] at h1
    rw [addKeys_freshFKeys_spec] at h1
    have hnot : ¬ (s₀ ≤ s ∧ s < s₀ + ts₀.length) := by
      simp only [List.length_cons] at hdisj; omega
    have h1' : D s = true := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
      exact h1.resolve_right hnot
    refine ⟨h1', fKeysIn_freshFKeys_addKeys_disjoint ts (s + 1) ?_ h2⟩
    simp only [List.length_cons] at hdisj; omega

/-! ## Store-tail hoisting `WP` -/

private theorem hoistStoreTail_untaken_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {jTs : List Ty} (tgt : TermTarget rs jTs) :
    ∀ (p : StoreTail) (next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val}
      {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → StoreTailSpec tgt p e₂ → IGood ρ next G →
    {cont : Nat → Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ next' ρ' args₁ vs₂, next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgsGood ρ' next' args₁ vs₂ → wp Γ Q X (cont next' args₁) m) →
    wp Γ Q X (hoistStoreTail jTs p next e₁ cont) m
  | .jump, next, ρ, _, _, _, _, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | @jump _ _ ts _ _ args₁ args₂ _ hargs =>
      cases tgt with
      | ret => exact False.elim hsp
      | jump j =>
        rcases hsp with ⟨rfl, rfl⟩
        rw [hoistStoreTail_jump_eq]
        exact hcont next ρ args₁ (vals args₂) (Nat.le_refl _) (fun _ _ => rfl)
          (IArgsGood.of_trel hG hargs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim (by cases tgt <;> exact hsp)
  | .ret, next, ρ, _, _, _, _, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | ret hvs =>
      cases tgt with
      | jump _ => exact False.elim hsp
      | ret =>
        rw [hoistStoreTail_ret_eq]
        exact hcont next ρ _ _ (Nat.le_refl _) (fun _ _ => rfl) (IArgsGood.of_trel hG hvs)
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | exit _ _ | hlt
    | group _ _ => exact False.elim (by cases tgt <;> exact hsp)
  | .let_ rest, next, ρ, _, _, _, _, hwf, hsp, hG, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code args₁ _ _ =>
        rcases hsp with ⟨hsafe, hsp'⟩
        dsimp only [hoistStoreTail, wp, Op.wp]
        refine OpCode.wp_of_isSafeOp code hsafe (vals (tupIOut args₁)) fun r => ?_
        refine hoistStoreTail_untaken_wp tgt rest (next + _) (hk (freshIVals _ r next) r)
          (hsp' r) (hG.freshIVals r) fun next' ρ' args₁ vs₂ hle hev hargs' => ?_
        refine hcont next' ρ' args₁ vs₂ (Nat.le_trans (Nat.le_add_right _ _) hle)
          (fun {u} k hk => ?_) hargs'
        exact (hev k (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r hk)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

private theorem hoistStoreTail_taken_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {mIn mOut : Mem 64} {jTs : List Ty} (tgt : TermTarget rs jTs) :
    ∀ (p : StoreTail) (next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val}
      {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → StoreTailSpec tgt p e₂ → IGood ρ next G → wp Γ Q X e₂ mIn →
    {cont : Nat → Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ next' ρ' args₁ vs₂, next ≤ next' →
      (∀ {u} (k : FKey u), k.FLt next → k.fev ρ' = k.fev ρ) →
      IArgsGood ρ' next' args₁ vs₂ → tgt.wp Q vs₂ mIn → wp Γ Q X (cont next' args₁) mOut) →
    wp Γ Q X (hoistStoreTail jTs p next e₁ cont) mOut
  | .jump, next, ρ, _, _, _, _, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | @jump _ _ ts _ _ args₁ args₂ _ hargs =>
      cases tgt with
      | ret => exact False.elim hsp
      | jump j =>
        rcases hsp with ⟨rfl, rfl⟩
        rw [hoistStoreTail_jump_eq]
        dsimp only [wp] at hwp
        exact hcont next ρ args₁ (vals args₂) (Nat.le_refl _) (fun _ _ => rfl)
          (IArgsGood.of_trel hG hargs) hwp
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim (by cases tgt <;> exact hsp)
  | .ret, next, ρ, _, _, _, _, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | ret hvs =>
      cases tgt with
      | jump _ => exact False.elim hsp
      | ret =>
        rw [hoistStoreTail_ret_eq]
        dsimp only [wp] at hwp
        exact hcont next ρ _ _ (Nat.le_refl _) (fun _ _ => rfl) (IArgsGood.of_trel hG hvs) hwp
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | exit _ _ | hlt
    | group _ _ => exact False.elim (by cases tgt <;> exact hsp)
  | .let_ rest, next, ρ, _, _, _, _, hwf, hsp, hG, hwp, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code _ args₂ hargs =>
        rcases hsp with ⟨_, hsp'⟩
        dsimp only [hoistStoreTail, wp, Op.wp] at hwp ⊢
        rw [TRel.iout_vals hG hargs]
        refine OpCode.wp_mono code (vals args₂) (fun r hr => ?_) hwp
        refine hoistStoreTail_taken_wp tgt rest (next + _) (hk (freshIVals _ r next) r)
          (hsp' r) (hG.freshIVals r) hr fun next' ρ' args₁ vs₂ hle hev hargs' hj => ?_
        refine hcont next' ρ' args₁ vs₂ (Nat.le_trans (Nat.le_add_right _ _) hle)
          (fun {u} k hk => ?_) hargs' hj
        exact (hev k (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r hk)
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

/-! ## Symbolic table soundness (`SymTblOk`, `LoadsMatchSym`, `PartialTblOk`) -/

@[expose] def SymTblOk (m : Mem 64) (ρ : FEnv) (tbl : SymTbl) : Prop :=
  (∀ e ∈ tbl.ops, ∀ {P : Tup Val e.ts → Prop},
    OpCode.wp e.code (fKeysEval ρ e.args) P ↔ P (fKeysEval ρ e.res)) ∧
  (∀ l ∈ tbl.loads, loadVal m l.lt (l.addr.fev ρ) = some (ρ l.lt l.vn))

private theorem symTblOk_empty (m : Mem 64) (ρ : FEnv) (b : Nat) :
    SymTblOk m ρ ⟨b, [], []⟩ :=
  ⟨(fun _ h {_} => by cases h), (fun _ h => by cases h)⟩

private theorem symTblOk_congr {base : Nat} {m : Mem 64} {tbl : SymTbl} {ρ ρ' : FEnv}
    (hTwf : SymTblWf base tbl) (hOk : SymTblOk m ρ tbl)
    (heq : ∀ {u} (fk : FKey u), fk.FLt tbl.vnNext → fk.fev ρ' = fk.fev ρ) :
    SymTblOk m ρ' tbl := by
  refine ⟨fun e he {P} => ?_, fun l hl => ?_⟩
  · rcases hTwf.2.1 e he with ⟨s, hrs, _, hsle, _, hka⟩
    have hargsEq : fKeysEval ρ' e.args = fKeysEval ρ e.args :=
      fKeysEval_fupdTup heq (hka.le (by omega))
    have hresEq : fKeysEval ρ' e.res = fKeysEval ρ e.res :=
      fKeysEval_fupdTup heq (hrs ▸ (fKeysLt_freshFKeys e.ts s).le hsle)
    rw [hargsEq, hresEq]
    exact hOk.1 e he
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hl
    have ⟨_, _, hvn, hla⟩ := hTwf.2.2.1 j l hj
    have ha : l.addr.fev ρ' = l.addr.fev ρ := heq l.addr (hla.le (Nat.le_of_lt hvn))
    have hv : ρ' l.lt l.vn = ρ l.lt l.vn := heq (.var l.vn) hvn
    rw [ha, hv]
    exact hOk.2 l hl

private theorem symTblOk_step_let {base : Nat} {m : Mem 64} {tbl : SymTbl} {ρ : FEnv}
    (hTwf : SymTblWf base tbl) (hOk : SymTblOk m ρ tbl)
    {sig ts : List Ty} (code : OpCode sig ts) (hs : isSafeOp code = true)
    (kArgs : Tup FKey sig) (hkLt : fKeysLt tbl.vnNext kArgs) (r₀ : Tup Val ts)
    (hiff : ∀ (P : Tup Val ts → Prop), OpCode.wp code (fKeysEval ρ kArgs) P ↔ P r₀) :
    ∃ ρ', (∀ {u} (fk : FKey u), fk.FLt tbl.vnNext → fk.fev ρ' = fk.fev ρ) ∧
      fKeysEval ρ' (tbl.internOp code kArgs).1 = r₀ ∧
      SymTblOk m ρ' (tbl.internOp code kArgs).2 := by
  unfold SymTbl.internOp
  split
  · refine ⟨ρ, fun _ _ => rfl, ?_, hOk⟩
    exact ((hiff (fun x => x = _)).1 rfl).symm
  · cases hf : findSymOp tbl.ops sig ts code kArgs with
    | some res =>
      have hmem := findSymOp_mem tbl.ops sig ts code kArgs res hf
      have hres_eq : fKeysEval ρ res = r₀ := by
        have h1 := (hOk.1 _ hmem (P := fun x => x = fKeysEval ρ res)).2 rfl
        exact ((hiff _).1 h1).symm
      exact ⟨ρ, fun _ _ => rfl, hres_eq, hOk⟩
    | none =>
      refine ⟨fupdTup ρ tbl.vnNext r₀, fun fk hfk => FKey.fev_fupdTup r₀ hfk,
        fKeysEval_freshFKeys ρ ts tbl.vnNext r₀, ?_⟩
      refine ⟨fun e he {P} => ?_, fun l hl => ?_⟩
      · cases he with
        | head =>
          dsimp only
          rw [fKeysEval_fupdTup (fun fk hfk => FKey.fev_fupdTup r₀ hfk) hkLt,
              fKeysEval_freshFKeys ρ ts tbl.vnNext r₀]
          exact hiff P
        | tail _ he' =>
          exact (symTblOk_congr hTwf hOk (fun fk hfk => FKey.fev_fupdTup r₀ hfk)).1 e he'
      · exact (symTblOk_congr hTwf hOk (fun fk hfk => FKey.fev_fupdTup r₀ hfk)).2 l hl

private theorem symTblOk_loadEmit {base : Nat} {m : Mem 64} {tbl : SymTbl} {ρ : FEnv}
    (hTwf : SymTblWf base tbl) (hOk : SymTblOk m ρ tbl)
    (t : Ty) (aKey : FKey i64) (haLt : aKey.FLt tbl.vnNext) (v : Val t)
    (hv : loadVal m t (aKey.fev ρ) = some v) :
    let entry : SymLoadEntry := ⟨tbl.loads.length, t, aKey, tbl.vnNext⟩
    let tbl' : SymTbl := { tbl with vnNext := tbl.vnNext + 1, loads := tbl.loads ++ [entry] }
    let ρ' := fupd ρ tbl.vnNext v
    (∀ {u} (fk : FKey u), fk.FLt tbl.vnNext → fk.fev ρ' = fk.fev ρ) ∧
    ρ' t tbl.vnNext = v ∧
    SymTblOk m ρ' tbl' := by
  intro entry tbl' ρ'
  have hcongr := symTblOk_congr hTwf hOk
    (fun {u} fk hfk => FKey.fev_fupd (ρ := ρ) (b := tbl.vnNext) v hfk)
  refine ⟨fun {u} fk hfk => FKey.fev_fupd v hfk, by dsimp only [ρ']; exact fupd_eq ρ tbl.vnNext v,
    fun e he {P} => hcongr.1 e he, fun l hl => ?_⟩
  rcases List.mem_append.1 hl with hl | hl
  · exact hcongr.2 l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    subst hl
    dsimp only [entry, ρ']
    rw [FKey.fev_fupd v haLt, fupd_eq]
    exact hv

@[expose] def LoadsMatchSym (ρh ρs : FEnv) (hn : Nat)
    (loads : List ((t : Ty) × IVal Val t)) (tblLoads : List SymLoadEntry) : Prop :=
  loads.length = tblLoads.length ∧
  ∀ (i : Nat) {t : Ty} {iv : IVal Val t} {sl : SymLoadEntry},
    loads[i]? = some ⟨t, iv⟩ → tblLoads[i]? = some sl →
    ∃ h : sl.lt = t, sl.slot = i ∧ iv.1 = .var (h ▸ ρs sl.lt sl.vn) ∧
      iv.2.fev ρh = (h ▸ ρs sl.lt sl.vn) ∧ iv.2.FLt hn

private theorem loadsMatchSym_empty (ρh ρs : FEnv) (hn : Nat) :
    LoadsMatchSym ρh ρs hn [] [] := by
  refine ⟨rfl, ?_⟩
  intro _ _ _ _ h1 _
  cases h1

private theorem loadsMatchSym_mono_h {ρh ρh' ρs : FEnv} {hn hn' : Nat}
    {loads : List ((t : Ty) × IVal Val t)} {tblLoads : List SymLoadEntry}
    (hle : hn ≤ hn') (heq : ∀ {u} (fk : FKey u), fk.FLt hn → fk.fev ρh' = fk.fev ρh)
    (hL : LoadsMatchSym ρh ρs hn loads tblLoads) :
    LoadsMatchSym ρh' ρs hn' loads tblLoads := by
  refine ⟨hL.1, fun i {_} {_} {_} h1 h2 => ?_⟩
  rcases hL.2 i h1 h2 with ⟨h, hsl, hv1, hv2, hlt⟩
  exact ⟨h, hsl, hv1, (heq _ hlt).trans hv2, hlt.le hle⟩

private theorem loadsMatchSym_mono_s {base : Nat} {tbl : SymTbl} {ρh ρs ρs' : FEnv} {hn : Nat}
    {loads : List ((t : Ty) × IVal Val t)}
    (hTwf : SymTblWf base tbl)
    (heq : ∀ {u} (fk : FKey u), fk.FLt tbl.vnNext → fk.fev ρs' = fk.fev ρs)
    (hL : LoadsMatchSym ρh ρs hn loads tbl.loads) :
    LoadsMatchSym ρh ρs' hn loads tbl.loads := by
  refine ⟨hL.1, fun i {_} {_} {sl} h1 h2 => ?_⟩
  rcases hL.2 i h1 h2 with ⟨h, hsl, hv1, hv2, hlt⟩
  have hvn : sl.vn < tbl.vnNext := (hTwf.2.2.1 i sl h2).2.2.1
  have hveq : ρs' sl.lt sl.vn = ρs sl.lt sl.vn := heq (.var sl.vn) hvn
  refine ⟨h, hsl, ?_, ?_, hlt⟩
  · rw [hveq]; exact hv1
  · rw [hveq]; exact hv2

private theorem loadsMatchSym_append {ρh ρs : FEnv} {hn vn : Nat}
    {loads : List ((t : Ty) × IVal Val t)} {tblLoads : List SymLoadEntry}
    {t : Ty} (aKey : FKey i64) (v : Val t)
    (hL : LoadsMatchSym ρh ρs hn loads tblLoads)
    (ρh' ρs' : FEnv)
    (hEqH : ∀ {u} (fk : FKey u), fk.FLt hn → fk.fev ρh' = fk.fev ρh)
    (hEqS : ∀ (sl : SymLoadEntry), sl ∈ tblLoads → ρs' sl.lt sl.vn = ρs sl.lt sl.vn)
    (hNewH : FKey.fev ρh' (.var (t := t) hn) = v) (hNewS : ρs' t vn = v) :
    LoadsMatchSym ρh' ρs' (hn + 1)
      (loads ++ [⟨t, (.var v, .var hn)⟩])
      (tblLoads ++ [⟨tblLoads.length, t, aKey, vn⟩]) := by
  refine ⟨by simp [hL.1], fun i t' iv sl h1 h2 => ?_⟩
  by_cases hi : i < loads.length
  · have hi2 : i < tblLoads.length := hL.1 ▸ hi
    rw [List.getElem?_append_left hi] at h1
    rw [List.getElem?_append_left hi2] at h2
    rcases hL.2 i h1 h2 with ⟨h, hsl, hv1, hv2, hlt⟩
    have hveq := hEqS sl (List.mem_of_getElem? h2)
    refine ⟨h, hsl, ?_, ?_, hlt.le (Nat.le_succ _)⟩
    · rw [hveq]; exact hv1
    · rw [hveq]; exact (hEqH _ hlt).trans hv2
  · have hi1 : loads.length ≤ i := Nat.le_of_not_lt hi
    have hi2 : tblLoads.length ≤ i := hL.1 ▸ hi1
    rw [List.getElem?_append_right hi1] at h1
    rw [List.getElem?_append_right hi2] at h2
    rw [hL.1] at h1
    cases hidx : i - tblLoads.length with
    | zero =>
      simp only [hidx, List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      cases h1; cases h2
      refine ⟨rfl, by dsimp only; omega, ?_, ?_, Nat.lt_succ_self _⟩
      · dsimp only; rw [hNewS]
      · dsimp only; rw [hNewS]; exact hNewH
    | succ k => simp [hidx] at h1

private theorem loadsMatchSym_lookup {ρh ρs : FEnv} {hn : Nat}
    {loads : List ((t : Ty) × IVal Val t)} {tblLoads : List SymLoadEntry}
    {slot : Nat} {sl : SymLoadEntry} {t : Ty}
    (hL : LoadsMatchSym ρh ρs hn loads tblLoads)
    (hsl : tblLoads[slot]? = some sl) (hlt : sl.lt = t) :
    ∃ (iv : IVal Val t),
      loads[slot]? = some ⟨t, iv⟩ ∧ iv.1 = .var (ρs t sl.vn) ∧
        iv.2.fev ρh = ρs t sl.vn ∧ iv.2.FLt hn := by
  have hslot : slot < tblLoads.length := (List.getElem?_eq_some_iff.1 hsl).1
  have hslot1 : slot < loads.length := hL.1 ▸ hslot
  cases hget : loads[slot]? with
  | none => exact absurd (List.getElem?_eq_none_iff.1 hget) (by omega)
  | some p =>
    rcases p with ⟨t', iv⟩
    rcases hL.2 slot hget hsl with ⟨heq, _, hv1, hv2, hfl⟩
    have htt : t' = t := heq.symm.trans hlt
    subst htt
    subst hlt
    exact ⟨iv, rfl, hv1, hv2, hfl⟩

/-! ## Store-step hoisting `WP` (taken, untaken `E`, untaken `T`) -/

private theorem hoistStoreStep_taken_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {jTs : List Ty} (tgt : TermTarget rs jTs) (st : Ty)
    (allowNew : Bool) (base : Nat) (Qend : List Nat → SymTbl → Prop) :
    ∀ (p : StoreStep) (hn : Nat) (loads : List ((t : Ty) × IVal Val t))
      (ρh ρs : FEnv) (tbl : SymTbl) (Dvn : Nat → Bool) (hits : List Nat) (aGoal : FKey i64)
      {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → StoreStepSpec tgt st allowNew Qend p tbl Dvn hits aGoal ρs e₂ →
    SymTblWf base tbl → SymTblOk m ρs tbl → IGood ρh hn G →
    LoadsMatchSym ρh ρs hn loads tbl.loads →
    (∀ i, Dvn i = true → i < tbl.vnNext) → wp Γ Q X e₂ m →
    {cont : Nat → List ((t : Ty) × IVal Val t) → Arg (IVal Val) st → Arg (IVal Val) i64 →
      Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ hn' loads' ρh' ρs' tbl' hits' v₁ (v₂ : Val st) a₁ (a₂ : Arg Val i64) args₁ vs₂,
      hn ≤ hn' → tbl.vnNext ≤ tbl'.vnNext →
      (∀ {u} (fk : FKey u), fk.FLt hn → fk.fev ρh' = fk.fev ρh) →
      (∀ {u} (fk : FKey u), fk.FLt tbl.vnNext → fk.fev ρs' = fk.fev ρs) →
      SymTblWf base tbl' → SymTblOk m ρs' tbl' → Qend hits' tbl' →
      LoadsMatchSym ρh' ρs' hn' loads' tbl'.loads →
      IArgGood ρh' hn' v₁ v₂ → IArgGood ρh' hn' a₁ a₂.val →
      aGoal.fev ρs' = a₂.val → IArgsGood ρh' hn' args₁ vs₂ →
      tgt.wp Q vs₂ (storeMem m st a₂.val v₂) → storeOk m st a₂.val →
      wp Γ Q X (cont hn' loads' v₁ a₁ args₁) m) →
    wp Γ Q X (hoistStoreStep jTs st p hn loads e₁ cont) m
  | .let_ rest, hn, loads, ρh, ρs, tbl, Dvn, hits, aGoal, _, _, _, _, hwf, hsp,
    hTwf, hOk, hG, hL, hDlt, hwp, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code args₁ args₂ hargs =>
        rcases hsp with ⟨hsafe, kArgs, hkev, _, hkLt, hsp'⟩
        dsimp only [hoistStoreStep, wp, Op.wp] at hwp ⊢
        rw [TRel.iout_vals hG hargs]
        obtain ⟨r₀, hiff⟩ := OpCode.wp_isSafeOp_iff code hsafe (vals args₂)
        have hk_wp := (hiff _).1 hwp
        have hiff_k : ∀ P, OpCode.wp code (fKeysEval ρs kArgs) P ↔ P r₀ := fun P => by
          rw [hkev]; exact hiff P
        rcases symTblOk_step_let hTwf hOk code hsafe kArgs hkLt r₀ hiff_k with
          ⟨ρs', hsEq, hresEq, hOk'⟩
        have hInt := symTblWf_internOp hTwf code hsafe kArgs hkLt
        refine (hiff _).2 ?_
        have hG' := hG.freshIVals r₀
        have hDlt' : ∀ i, addKeys Dvn (tbl.internOp code kArgs).1 i = true →
            i < (tbl.internOp code kArgs).2.vnNext :=
          addKeys_disjoint_lt hInt.2.2.1 (fun i hi => Nat.lt_of_lt_of_le (hDlt i hi) hInt.2.1)
        have hsp_next := hsp' r₀ ρs' (fun fk hk => by
          cases fk with
          | imm _ => rfl
          | var v => exact hsEq _ (hDlt v hk)) hresEq
        refine hoistStoreStep_taken_wp tgt st allowNew base Qend rest (hn + _) loads
          (fupdTup ρh hn r₀) ρs' (tbl.internOp code kArgs).2
          (addKeys Dvn (tbl.internOp code kArgs).1) hits aGoal
          (hk (freshIVals _ r₀ hn) r₀) hsp_next hInt.1 hOk' hG'
          (loadsMatchSym_mono_h (Nat.le_add_right _ _)
            (fun fk hfk => FKey.fev_fupdTup r₀ hfk)
            (hInt.2.2.2.2 ▸ loadsMatchSym_mono_s hTwf hsEq hL))
          hDlt' hk_wp
          fun hn' loads' ρh' ρs'' tbl' hits' v₁ v₂ a₁ a₂ args₁ vs₂ hleH hleS
            heqH heqS hTwf' hOk'' hQend hL'' hv ha haev hargs' htgt hstok => ?_
        exact hcont hn' loads' ρh' ρs'' tbl' hits' v₁ v₂ a₁ a₂ args₁ vs₂
          (Nat.le_trans (Nat.le_add_right _ _) hleH) (Nat.le_trans hInt.2.1 hleS)
          (fun fk hk => (heqH fk (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r₀ hk))
          (fun fk hk => (heqS fk (hk.le hInt.2.1)).trans (hsEq fk hk))
          hTwf' hOk'' hQend hL'' hv ha haev hargs' htgt hstok
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .loadEmit rest, hn, loads, ρh, ρs, tbl, Dvn, hits, aGoal, _, _, _, _, hwf, hsp,
    hTwf, hOk, hG, hL, hDlt, hwp, cont, hcont => by
    cases hwf with
    | load t ha hk =>
      rcases hsp with ⟨rfl, aKey, haev, _, haLt, _, hsp'⟩
      dsimp only [hoistStoreStep, wp] at hwp ⊢
      rcases hwp with ⟨v, hv, hk2⟩
      rw [argRel_iout_val hG ha]
      refine ⟨v, hv, ?_⟩
      have hv_sym : loadVal m t (aKey.fev ρs) = some v := by rw [haev]; exact hv
      rcases symTblOk_loadEmit hTwf hOk t aKey haLt v hv_sym with ⟨hsEq, _, hOk'⟩
      have hTwf1 := symTblWf_loadEmit hTwf t aKey haLt
      have hG' := hG.freshOne v
      have hL' := loadsMatchSym_append aKey v hL (fupd ρh hn v) (fupd ρs tbl.vnNext v)
        (fun fk hfk => FKey.fev_fupd v hfk)
        (fun sl hsl => by
          obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hsl
          have hvn := (hTwf.2.2.1 j sl hj).2.2.1
          exact FKey.fev_fupd (ρ := ρs) (b := tbl.vnNext) (κ := .var sl.vn) v hvn)
        (by dsimp only [FKey.fev]; exact fupd_eq ρh hn v) (fupd_eq ρs tbl.vnNext v)
      have hDlt' : ∀ i, addVN Dvn tbl.vnNext i = true → i < tbl.vnNext + 1 := by
        intro i hi
        simp only [addVN, Bool.or_eq_true, beq_iff_eq] at hi
        rcases hi with hi | rfl
        · exact Nat.lt_succ_of_lt (hDlt i hi)
        · exact Nat.lt_succ_self _
      have hsp_next := hsp' v (fupd ρs tbl.vnNext v)
        (fun fk hk => by cases fk with | imm _ => rfl | var w => exact hsEq _ (hDlt w hk))
        (fupd_eq ρs tbl.vnNext v)
      refine hoistStoreStep_taken_wp tgt st true base Qend rest (hn + 1)
        (loads ++ [⟨t, (.var v, .var hn)⟩]) (fupd ρh hn v) (fupd ρs tbl.vnNext v) _
        (addVN Dvn tbl.vnNext) (tbl.loads.length :: hits) aGoal
        (hk (.var v, .var hn) v) hsp_next hTwf1 hOk' hG' hL' hDlt' hk2
        fun hn' loads' ρh' ρs'' tbl' hits' v₁ v₂ a₁ a₂ args₁ vs₂ hleH hleS
          heqH heqS hTwf' hOk'' hQend hL'' hv' ha' haev' hargs' htgt hstok => ?_
      exact hcont hn' loads' ρh' ρs'' tbl' hits' v₁ v₂ a₁ a₂ args₁ vs₂
        (Nat.le_trans (Nat.le_succ _) hleH) (Nat.le_trans (Nat.le_succ _) hleS)
        (fun fk hk => (heqH fk (hk.le (Nat.le_succ _))).trans (FKey.fev_fupd v hk))
        (fun fk hk => (heqS fk (hk.le (Nat.le_succ _))).trans (hsEq fk hk))
        hTwf' hOk'' hQend hL'' hv' ha' haev' hargs' htgt hstok
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .loadReuse slot rest, hn, loads, ρh, ρs, tbl, Dvn, hits, aGoal, G, _, _, _, hwf, hsp,
    hTwf, hOk, hG, hL, hDlt, hwp, cont, hcont => by
    cases hwf with
    | load t _ hk =>
      rcases hsp with ⟨aKey, entry, haev, _, _, hfind, rfl, hsp'⟩
      dsimp only [wp] at hwp
      rcases hwp with ⟨v, hv, hk2⟩
      have hmem := findSymLoad_mem tbl.loads t aKey entry hfind
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem.1
      have ⟨hsl, _, hvn, _⟩ := hTwf.2.2.1 j entry hj
      have hload_ok := hOk.2 entry hmem.1
      rw [hmem.2.1, hmem.2.2, haev] at hload_ok
      have hveq : v = ρs t entry.vn := Option.some.inj (hv.symm.trans hload_ok)
      rcases loadsMatchSym_lookup hL (hsl ▸ hj) hmem.2.1 with
        ⟨iv, hl_eq, hiv1, hiv2, hivlt⟩
      dsimp only [hoistStoreStep]
      rw [hl_eq]; dsimp only
      cases hdec : tyDecEq t t with
      | isFalse hne => exact absurd rfl hne
      | isTrue _ =>
        have hG' : IGood ρh hn (⟨t, iv, v⟩ :: G) := fun p hp => by
          cases hp with
          | head => exact ⟨by rw [hiv1, hveq]; rfl, hiv2.trans hveq.symm, hivlt⟩
          | tail _ hm => exact hG p hm
        have hDlt' : ∀ i, addVN Dvn entry.vn i = true → i < tbl.vnNext := by
          intro i hi
          simp only [addVN, Bool.or_eq_true, beq_iff_eq] at hi
          rcases hi with hi | rfl
          · exact hDlt i hi
          · exact hvn
        have hsp_next := hsp' v ρs (fun _ _ => rfl) hveq.symm
        exact hoistStoreStep_taken_wp tgt st allowNew base Qend rest hn loads ρh ρs tbl
          (addVN Dvn entry.vn) _ aGoal (hk iv v) hsp_next hTwf hOk hG' hL hDlt' hk2 hcont
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .store tail, hn, loads, ρh, ρs, tbl, _, _, aGoal, _, _, _, _, hwf, hsp,
    hTwf, hOk, hG, hL, _, hwp, cont, hcont => by
    cases hwf with
    | store hv ha hk =>
      rcases hsp with ⟨hst, haev, _, hQend, htail⟩
      subst hst
      dsimp only [hoistStoreStep]
      cases hdec : tyDecEq _ _ with
      | isFalse hne => exact absurd rfl hne
      | isTrue _ =>
        dsimp only [wp] at hwp
        refine hoistStoreTail_taken_wp (mOut := m) tgt tail hn hk htail hG hwp.2
          fun hn' ρh' args₁ vs₂ hle hev hargs' htgt => ?_
        have hL' := loadsMatchSym_mono_h hle hev hL
        have hv' := iargGood_mono hle hev (iargGood_of_argRel hG hv)
        have ha' := iargGood_mono hle hev (iargGood_of_argRel hG ha)
        exact hcont hn' loads ρh' ρs tbl _ _ _ _ _ args₁ vs₂
          hle (Nat.le_refl _) hev (fun _ _ => rfl) hTwf hOk hQend hL'
          hv' ha' haev hargs' htgt hwp.1
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

private theorem hoistStoreStep_untaken_E_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {jTs : List Ty} (tgt : TermTarget rs jTs) (st : Ty)
    (base : Nat) (Qend : List Nat → SymTbl → Prop) :
    ∀ (p : StoreStep) (hn : Nat) (loads : List ((t : Ty) × IVal Val t))
      (ρh ρs : FEnv) (tbl : SymTbl) (Dvn : Nat → Bool) (hits : List Nat) (aGoal : FKey i64)
      {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → StoreStepSpec tgt st false Qend p tbl Dvn hits aGoal ρs e₂ →
    SymTblWf base tbl → SymTblOk m ρs tbl → IGood ρh hn G →
    LoadsMatchSym ρh ρs hn loads tbl.loads → (∀ i, Dvn i = true → i < tbl.vnNext) →
    {cont : Nat → List ((t : Ty) × IVal Val t) → Arg (IVal Val) st → Arg (IVal Val) i64 →
      Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ hn' ρh' v₁ (v₂ : Val st) (a₁ : Arg (IVal Val) i64) args₁ vs₂,
      hn ≤ hn' → (∀ {u} (fk : FKey u), fk.FLt hn → fk.fev ρh' = fk.fev ρh) →
      IArgGood ρh' hn' v₁ v₂ → IArgsGood ρh' hn' args₁ vs₂ →
      wp Γ Q X (cont hn' loads v₁ a₁ args₁) m) →
    wp Γ Q X (hoistStoreStep jTs st p hn loads e₁ cont) m
  | .let_ rest, hn, loads, ρh, ρs, tbl, Dvn, hits, aGoal, _, _, _, _, hwf, hsp,
    hTwf, hOk, hG, hL, hDlt, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code args₁ args₂ hargs =>
        rcases hsp with ⟨hsafe, kArgs, hkev, _, hkLt, hsp'⟩
        dsimp only [hoistStoreStep, wp, Op.wp]
        rw [TRel.iout_vals hG hargs]
        obtain ⟨r₀, hiff⟩ := OpCode.wp_isSafeOp_iff code hsafe (vals args₂)
        have hiff_k : ∀ P, OpCode.wp code (fKeysEval ρs kArgs) P ↔ P r₀ := fun P => by
          rw [hkev]; exact hiff P
        rcases symTblOk_step_let hTwf hOk code hsafe kArgs hkLt r₀ hiff_k with
          ⟨ρs', hsEq, hresEq, hOk'⟩
        have hInt := symTblWf_internOp hTwf code hsafe kArgs hkLt
        refine (hiff _).2 ?_
        have hG' := hG.freshIVals r₀
        have hDlt' : ∀ i, addKeys Dvn (tbl.internOp code kArgs).1 i = true →
            i < (tbl.internOp code kArgs).2.vnNext :=
          addKeys_disjoint_lt hInt.2.2.1 (fun i hi => Nat.lt_of_lt_of_le (hDlt i hi) hInt.2.1)
        have hsp_next := hsp' r₀ ρs' (fun fk hk => by
          cases fk with | imm _ => rfl | var w => exact hsEq _ (hDlt w hk)) hresEq
        refine hoistStoreStep_untaken_E_wp tgt st base Qend rest (hn + _) loads
          (fupdTup ρh hn r₀) ρs' (tbl.internOp code kArgs).2
          (addKeys Dvn (tbl.internOp code kArgs).1) hits aGoal
          (hk (freshIVals _ r₀ hn) r₀) hsp_next hInt.1 hOk' hG'
          (loadsMatchSym_mono_h (Nat.le_add_right _ _)
            (fun fk hfk => FKey.fev_fupdTup r₀ hfk)
            (hInt.2.2.2.2 ▸ loadsMatchSym_mono_s hTwf hsEq hL))
          hDlt' fun hn' ρh' v₁ v₂ a₁ args₁ vs₂ hle hev hv hargs' => ?_
        exact hcont hn' ρh' v₁ v₂ a₁ args₁ vs₂ (Nat.le_trans (Nat.le_add_right _ _) hle)
          (fun fk hk => (hev fk (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r₀ hk))
          hv hargs'
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .loadEmit _, _, _, _, _, _, _, _, _, _, _, _, _, hwf, hsp, _, _, _, _, _, _, _ => by
    cases hwf with
    | load _ _ _ => exact False.elim (Bool.false_ne_true hsp.1)
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .loadReuse slot rest, hn, loads, ρh, ρs, tbl, Dvn, hits, aGoal, G, _, _, _, hwf, hsp,
    hTwf, hOk, hG, hL, hDlt, cont, hcont => by
    cases hwf with
    | load t _ hk =>
      rcases hsp with ⟨aKey, entry, _, _, _, hfind, rfl, hsp'⟩
      have hmem := findSymLoad_mem tbl.loads t aKey entry hfind
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem.1
      have ⟨hsl, _, hvn, _⟩ := hTwf.2.2.1 j entry hj
      rcases loadsMatchSym_lookup hL (hsl ▸ hj) hmem.2.1 with
        ⟨iv, hl_eq, hiv1, hiv2, hivlt⟩
      dsimp only [hoistStoreStep]
      rw [hl_eq]; dsimp only
      cases hdec : tyDecEq t t with
      | isFalse hne => exact absurd rfl hne
      | isTrue _ =>
        have hG' : IGood ρh hn (⟨t, iv, ρs t entry.vn⟩ :: G) := fun p hp => by
          cases hp with
          | head => exact ⟨by rw [hiv1]; rfl, hiv2, hivlt⟩
          | tail _ hm => exact hG p hm
        have hDlt' : ∀ i, addVN Dvn entry.vn i = true → i < tbl.vnNext := by
          intro i hi
          simp only [addVN, Bool.or_eq_true, beq_iff_eq] at hi
          rcases hi with hi | rfl
          · exact hDlt i hi
          · exact hvn
        have hsp_next := hsp' (ρs t entry.vn) ρs (fun _ _ => rfl) rfl
        exact hoistStoreStep_untaken_E_wp tgt st base Qend rest hn loads ρh ρs tbl
          (addVN Dvn entry.vn) _ aGoal (hk iv (ρs t entry.vn)) hsp_next hTwf hOk hG' hL hDlt'
          hcont
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .store tail, hn, loads, ρh, ρs, tbl, _, _, _, _, _, _, _, hwf, hsp,
    _, _, hG, _, _, cont, hcont => by
    cases hwf with
    | store hv ha hk =>
      rcases hsp with ⟨hst, _, _, _, htail⟩
      subst hst
      dsimp only [hoistStoreStep]
      cases hdec : tyDecEq _ _ with
      | isFalse hne => exact absurd rfl hne
      | isTrue _ =>
        refine hoistStoreTail_untaken_wp tgt tail hn hk htail hG
          fun hn' ρh' args₁ vs₂ hle hev hargs' => ?_
        have hv' := iargGood_mono hle hev (iargGood_of_argRel hG hv)
        exact hcont hn' ρh' _ _ _ args₁ vs₂ hle hev hv' hargs'
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

@[expose] def PartialTblOk (m : Mem 64) (D : Nat → Bool) (ρ : FEnv) (tbl : SymTbl) : Prop :=
  (∀ e ∈ tbl.ops, fKeysIn D e.res →
    fKeysIn D e.args ∧
    ∀ {P : Tup Val e.ts → Prop}, OpCode.wp e.code (fKeysEval ρ e.args) P ↔ P (fKeysEval ρ e.res)) ∧
  (∀ l ∈ tbl.loads, D l.vn = true →
    KeyIn D l.addr ∧ loadVal m l.lt (l.addr.fev ρ) = some (ρ l.lt l.vn))

@[expose] def DAtom (ops : List SymOpEntry) (D : Nat → Bool) : Prop :=
  ∀ e ∈ ops, ∀ s, e.res = freshFKeys e.ts s →
    (∀ i, s ≤ i → i < s + e.ts.length → D i = true) ∨
    (∀ i, s ≤ i → i < s + e.ts.length → D i = false)

private theorem not_fKeysIn_freshFKeys_of_lt (base : Nat) :
    (ts : List Ty) → ts ≠ [] → ∀ s, base ≤ s →
    ¬ fKeysIn (fun i => decide (i < base)) (freshFKeys ts s)
  | [], hne, _, _, _ => absurd rfl hne
  | _ :: _, _, s, hbs, hIn => by
    dsimp only [fKeysIn, freshFKeys, KeyIn] at hIn
    have hD : decide (s < base) = true := hIn.1
    simp only [decide_eq_true_eq] at hD; omega

private theorem partialTblOk_of_symTblWf_base (m : Mem 64) (ρ : FEnv) {base : Nat}
    {tbl : SymTbl} (hTwf : SymTblWf base tbl) :
    PartialTblOk m (fun i => decide (i < base)) ρ tbl ∧
    DAtom tbl.ops (fun i => decide (i < base)) := by
  have hallF : ∀ e ∈ tbl.ops, ∀ s, e.res = freshFKeys e.ts s →
      ∀ i, s ≤ i → i < s + e.ts.length → decide (i < base) = false := by
    intro e he s hrs i hi1 _
    rcases hTwf.2.1 e he with ⟨s', hrs', hbs, _, hsafe, _⟩
    have hpos := isSafeOp_ts_pos e.code hsafe
    rcases freshFKeys_start_eq (hrs.symm.trans hrs') with hnil | rfl
    · have : e.ts.length = 0 := by simp [hnil]
      omega
    · exact decide_eq_false (by omega)
  refine ⟨⟨fun e he hIn => ?_, fun l hl hIn => ?_⟩, fun e he s hrs => Or.inr (hallF e he s hrs)⟩
  · rcases hTwf.2.1 e he with ⟨s, hrs, hbs, _, hsafe, _⟩
    have hpos := isSafeOp_ts_pos e.code hsafe
    have hne : e.ts ≠ [] := by intro hnil; rw [hnil] at hpos; cases hpos
    rw [hrs] at hIn
    exact absurd hIn (not_fKeysIn_freshFKeys_of_lt base e.ts hne s hbs)
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hl
    have hbs := (hTwf.2.2.1 j l hj).2.1
    exact absurd hIn (by simp; omega)

private theorem dAtom_mono_eq {ops : List SymOpEntry} {D₁ D₂ : Nat → Bool}
    (heq : ∀ i, D₂ i = D₁ i) (hA : DAtom ops D₁) : DAtom ops D₂ := by
  intro e he s hrs
  rcases hA e he s hrs with hT | hF
  · exact Or.inl fun i h1 h2 => (heq i).symm ▸ hT i h1 h2
  · exact Or.inr fun i h1 h2 => (heq i).symm ▸ hF i h1 h2

private theorem partialTblOk_mono_eq {m : Mem 64} {D₁ D₂ : Nat → Bool} {ρ : FEnv}
    {tbl : SymTbl} (heq : ∀ i, D₂ i = D₁ i) (hOk : PartialTblOk m D₁ ρ tbl) :
    PartialTblOk m D₂ ρ tbl := by
  have hsub1 : ∀ i, D₂ i = true → D₁ i = true := fun i h => by rw [← heq i]; exact h
  have hsub2 : ∀ i, D₁ i = true → D₂ i = true := fun i h => by rw [heq i]; exact h
  refine ⟨fun e he hIn => ?_, fun l hl hIn => ?_⟩
  · rcases hOk.1 e he (fKeysIn_mono hsub1 hIn) with ⟨h1, h2⟩
    exact ⟨fKeysIn_mono hsub2 h1, h2⟩
  · rcases hOk.2 l hl (hsub1 l.vn hIn) with ⟨h1, h2⟩
    exact ⟨keyIn_mono hsub2 h1, h2⟩

private theorem symTblWf_res_eq_or_disjoint {base : Nat} {tbl : SymTbl}
    (hTwf : SymTblWf base tbl)
    {e₁ e₂ : SymOpEntry} (he₁ : e₁ ∈ tbl.ops) (he₂ : e₂ ∈ tbl.ops)
    {s₁ s₂ : Nat} (hrs₁ : e₁.res = freshFKeys e₁.ts s₁)
    (hrs₂ : e₂.res = freshFKeys e₂.ts s₂) :
    e₁ = e₂ ∧ s₁ = s₂ ∨ (s₁ + e₁.ts.length ≤ s₂ ∨ s₂ + e₂.ts.length ≤ s₁) := by
  obtain ⟨i₁, hi₁⟩ := List.mem_iff_getElem?.1 he₁
  obtain ⟨i₂, hi₂⟩ := List.mem_iff_getElem?.1 he₂
  by_cases h : i₁ = i₂
  · subst h; rw [hi₁] at hi₂; cases Option.some.inj hi₂
    rcases hTwf.2.1 e₁ he₁ with ⟨_, _, _, _, hsafe, _⟩
    have hpos := isSafeOp_ts_pos e₁.code hsafe
    rcases freshFKeys_start_eq (hrs₁.symm.trans hrs₂) with hnil | rfl
    · have : e₁.ts.length = 0 := by simp [hnil]
      omega
    · exact Or.inl ⟨rfl, rfl⟩
  · rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · exact Or.inr (Or.inr (hTwf.2.2.2.1 i₁ i₂ e₁ e₂ hlt hi₁ hi₂ s₁ s₂ hrs₁ hrs₂))
    · exact Or.inr (Or.inl (hTwf.2.2.2.1 i₂ i₁ e₂ e₁ hgt hi₂ hi₁ s₂ s₁ hrs₂ hrs₁))

private theorem partialTblOk_let_step {m : Mem 64} {base : Nat} {tbl : SymTbl}
    {D : Nat → Bool} {ρ : FEnv} (hTwf : SymTblWf base tbl) (hOk : PartialTblOk m D ρ tbl)
    (hDlt : ∀ i, D i = true → i < tbl.vnNext) (hAtom : DAtom tbl.ops D)
    {sig ts : List Ty} (code : OpCode sig ts) (hs : isSafeOp code = true)
    (kArgs : Tup FKey sig) (hkIn : fKeysIn D kArgs) (hkLt : fKeysLt tbl.vnNext kArgs)
    (r₀ : Tup Val ts)
    (hiff : ∀ (P : Tup Val ts → Prop), OpCode.wp code (fKeysEval ρ kArgs) P ↔ P r₀) :
    let (resKeys, tbl1) := tbl.internOp code kArgs
    let D' := addKeys D resKeys
    ∃ ρ₁, (∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ₁ = fk.fev ρ) ∧
      fKeysEval ρ₁ resKeys = r₀ ∧ PartialTblOk m D' ρ₁ tbl1 ∧ DAtom tbl1.ops D' := by
  dsimp only
  revert hiff; revert hkLt; revert hkIn
  unfold SymTbl.internOp
  split
  · intro hkIn _ hiff
    have hD_eq := addKeys_eq_of_fKeysIn hkIn
    refine ⟨ρ, fun _ _ => rfl, ?_, partialTblOk_mono_eq hD_eq hOk, dAtom_mono_eq hD_eq hAtom⟩
    exact ((hiff (fun x => x = _)).1 rfl).symm
  · intro hkIn hkLt hiff
    cases hf : findSymOp tbl.ops sig ts code kArgs with
    | some res =>
      have hmem := findSymOp_mem tbl.ops sig ts code kArgs res hf
      rcases hTwf.2.1 _ hmem with ⟨s, hrs, _, _, _, _⟩
      dsimp only at hrs
      have hAddSpec : ∀ i, addKeys D res i =
          (D i || (decide (s ≤ i) && decide (i < s + ts.length))) :=
        fun i => by rw [hrs]; exact addKeys_freshFKeys_spec ts D s i
      rcases hAtom _ hmem s hrs with hAllT | hAllF
      · have hIn : fKeysIn D res := hrs ▸ fKeysIn_freshFKeys_of_all ts s hAllT
        have hD_eq := addKeys_eq_of_fKeysIn hIn
        rcases hOk.1 _ hmem hIn with ⟨_, hOkE⟩
        have heq : fKeysEval ρ res = r₀ :=
          ((hiff _).1 ((hOkE (P := fun x => x = fKeysEval ρ res)).2 rfl)).symm
        exact ⟨ρ, fun _ _ => rfl, heq, partialTblOk_mono_eq hD_eq hOk, dAtom_mono_eq hD_eq hAtom⟩
      · let ρ₁ := fupdTup ρ s r₀
        have hfev1 : ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ₁ = fk.fev ρ :=
          fev_fupdTup_of_disjoint s r₀ hAllF
        have hres1 : fKeysEval ρ₁ res = r₀ := by
          rw [hrs]; exact fKeysEval_freshFKeys ρ ts s r₀
        have hkArgs1 : fKeysEval ρ₁ kArgs = fKeysEval ρ kArgs := fKeysEval_congr_in hfev1 hkIn
        refine ⟨ρ₁, hfev1, hres1, ⟨fun e' he' hIn' => ?_, fun l hl hIn' => ?_⟩, ?_⟩
        · rcases hTwf.2.1 e' he' with ⟨s', hrs', _, _, _, _⟩
          rcases symTblWf_res_eq_or_disjoint hTwf he' hmem hrs' hrs with ⟨rfl, rfl⟩ | hdisj'
          · refine ⟨fKeysIn_mono (addKeys_sub D res) hkIn, fun {P} => ?_⟩
            dsimp only
            rw [hkArgs1, hres1]
            exact hiff P
          · have hIn0 : fKeysIn D e'.res :=
              hrs' ▸ fKeysIn_freshFKeys_addKeys_disjoint e'.ts s' hdisj' (hrs ▸ hrs' ▸ hIn')
            rcases hOk.1 e' he' hIn0 with ⟨hargs0, hwp0⟩
            refine ⟨fKeysIn_mono (addKeys_sub D res) hargs0, fun {P} => ?_⟩
            rw [fKeysEval_congr_in hfev1 hargs0, fKeysEval_congr_in hfev1 hIn0]; exact hwp0
        · have hdisj_l := hTwf.2.2.2.2.1 _ hmem l hl s hrs
          dsimp only at hdisj_l
          have hIn0 : D l.vn = true := by
            rw [hAddSpec] at hIn'
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hIn'
            exact hIn'.resolve_right (by omega)
          rcases hOk.2 l hl hIn0 with ⟨ha0, hld0⟩
          refine ⟨keyIn_mono (addKeys_sub D res) ha0, ?_⟩
          have hveq : ρ₁ l.lt l.vn = ρ l.lt l.vn := hfev1 (.var l.vn) hIn0
          rw [hfev1 l.addr ha0, hveq]
          exact hld0
        · intro e' he' s' hrs'
          rcases symTblWf_res_eq_or_disjoint hTwf he' hmem hrs' hrs with ⟨rfl, rfl⟩ | hdisj'
          · left; intro i h1 h2; rw [hAddSpec]; simp [h1, h2]
          · dsimp only at hdisj'
            rcases hAtom e' he' s' hrs' with hT | hF
            · left; intro i h1 h2; exact addKeys_sub D res i (hT i h1 h2)
            · right; intro i h1 h2
              have hnot' : (decide (s ≤ i) && decide (i < s + ts.length)) = false := by
                simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
              rw [hAddSpec, hF i h1 h2, hnot']; rfl
    | none =>
      let res := freshFKeys ts tbl.vnNext
      let ρ₁ := fupdTup ρ tbl.vnNext r₀
      have hdisj : ∀ i, tbl.vnNext ≤ i → i < tbl.vnNext + ts.length → D i = false :=
        fun i h1 _ => Bool.eq_false_iff.2 fun ht => absurd (hDlt i ht) (by omega)
      have hfev1 : ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ₁ = fk.fev ρ :=
        fev_fupdTup_of_disjoint tbl.vnNext r₀ hdisj
      have hfev_lt : ∀ {u} (fk : FKey u), fk.FLt tbl.vnNext → fk.fev ρ₁ = fk.fev ρ :=
        fun fk hfk => FKey.fev_fupdTup r₀ hfk
      have hAddSpec : ∀ i, addKeys D res i =
          (D i || (decide (tbl.vnNext ≤ i) && decide (i < tbl.vnNext + ts.length))) :=
        fun i => addKeys_freshFKeys_spec ts D tbl.vnNext i
      refine ⟨ρ₁, hfev1, fKeysEval_freshFKeys ρ ts tbl.vnNext r₀, ⟨fun e' he' hIn' => ?_,
          fun l hl hIn' => ?_⟩, ?_⟩
      · cases he' with
        | head =>
          refine ⟨fKeysIn_mono (addKeys_sub D res) hkIn, fun {P} => ?_⟩
          dsimp only
          rw [fKeysEval_fupdTup hfev_lt hkLt, fKeysEval_freshFKeys ρ ts tbl.vnNext r₀]
          exact hiff P
        | tail _ he' =>
          rcases hTwf.2.1 e' he' with ⟨s', hrs', _, hsle', _, hka'⟩
          have hIn0 : fKeysIn D e'.res :=
            hrs' ▸ fKeysIn_freshFKeys_addKeys_disjoint e'.ts s' (Or.inl hsle') (hrs' ▸ hIn')
          rcases hOk.1 e' he' hIn0 with ⟨hargs0, hwp0⟩
          refine ⟨fKeysIn_mono (addKeys_sub D res) hargs0, fun {P} => ?_⟩
          rw [fKeysEval_fupdTup hfev_lt (hka'.le (by omega)),
              fKeysEval_fupdTup hfev_lt (hrs' ▸ (fKeysLt_freshFKeys e'.ts s').le hsle')]
          exact hwp0
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hl
        have hvn := (hTwf.2.2.1 j l hj).2.2.1
        have hIn0 : D l.vn = true := by
          rw [hAddSpec] at hIn'
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hIn'
          exact hIn'.resolve_right (by omega)
        rcases hOk.2 l hl hIn0 with ⟨ha0, hld0⟩
        refine ⟨keyIn_mono (addKeys_sub D res) ha0, ?_⟩
        have hveq : ρ₁ l.lt l.vn = ρ l.lt l.vn := hfev_lt (.var l.vn) hvn
        rw [hfev1 l.addr ha0, hveq]
        exact hld0
      · intro e' he' s' hrs'
        cases he' with
        | head =>
          dsimp only at hrs'
          have hpos := isSafeOp_ts_pos code hs
          rcases freshFKeys_start_eq hrs' with hnil | rfl
          · have : ts.length = 0 := by simp [hnil]
            omega
          · left; intro i h1 h2; rw [hAddSpec]; simp [h1, h2]
        | tail _ he' =>
          rcases hTwf.2.1 e' he' with ⟨s₂, hrs₂, _, hsle₂, hsafe₂, _⟩
          have hpos₂ := isSafeOp_ts_pos e'.code hsafe₂
          rcases freshFKeys_start_eq (hrs'.symm.trans hrs₂) with hnil | rfl
          · have : e'.ts.length = 0 := by simp [hnil]
            omega
          · rcases hAtom e' he' s' hrs' with hT | hF
            · left; intro i h1 h2; exact addKeys_sub D res i (hT i h1 h2)
            · right; intro i h1 h2
              have hnot' :
                  (decide (tbl.vnNext ≤ i) && decide (i < tbl.vnNext + ts.length)) = false := by
                simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
              rw [hAddSpec, hF i h1 h2, hnot']; rfl

private theorem partialTblOk_loadReuse_step {m : Mem 64} {base : Nat} {tbl : SymTbl}
    {D : Nat → Bool} {ρ : FEnv} (hTwf : SymTblWf base tbl) (hOk : PartialTblOk m D ρ tbl)
    (hDlt : ∀ i, D i = true → i < tbl.vnNext) (hAtom : DAtom tbl.ops D)
    {t : Ty} (aKey : FKey i64) (haIn : KeyIn D aKey) {aVal : Val i64} (haev : aKey.fev ρ = aVal)
    (entry : SymLoadEntry) (hmem : entry ∈ tbl.loads) (het : entry.lt = t)
    (haddr : entry.addr = aKey) (v : Val t)
    (hv : loadVal m t aVal = some v) :
    ∃ ρ₁, (∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ₁ = fk.fev ρ) ∧
      ρ₁ t entry.vn = v ∧ PartialTblOk m (addVN D entry.vn) ρ₁ tbl ∧
      (∀ i, addVN D entry.vn i = true → i < tbl.vnNext) ∧ DAtom tbl.ops (addVN D entry.vn) := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem
  have hvn := (hTwf.2.2.1 j entry hj).2.2.1
  by_cases hDvn : D entry.vn = true
  · have hld := (hOk.2 entry hmem hDvn).2
    rw [haddr, het, haev] at hld
    have hveq : v = ρ t entry.vn := Option.some.inj (hv.symm.trans hld)
    have hD_eq : ∀ i, addVN D entry.vn i = D i := by
      intro i
      by_cases heq : i = entry.vn
      · subst heq; simp [addVN, hDvn]
      · simp [addVN, heq]
    exact ⟨ρ, fun _ _ => rfl, hveq.symm, partialTblOk_mono_eq hD_eq hOk,
      fun i hi => hDlt i (by rw [← hD_eq i]; exact hi), dAtom_mono_eq hD_eq hAtom⟩
  · have hnot : D entry.vn = false := Bool.eq_false_iff.2 hDvn
    let ρ₁ := fupd ρ entry.vn v
    have hfev1 : ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ₁ = fk.fev ρ :=
      fev_fupd_of_not_in entry.vn v hnot
    refine ⟨ρ₁, hfev1, by dsimp only [ρ₁]; exact fupd_eq ρ entry.vn v,
        ⟨fun e he hIn => ?_, fun l hl hIn => ?_⟩, ?_, ?_⟩
    · rcases hTwf.2.1 e he with ⟨s, hrs, _, _, _, _⟩
      have hdisj := hTwf.2.2.2.2.1 e he entry hmem s hrs
      have hIn0 : fKeysIn D e.res := hrs ▸ fKeysIn_freshFKeys_addVN e.ts s hdisj (hrs ▸ hIn)
      rcases hOk.1 e he hIn0 with ⟨hargs0, hwp0⟩
      refine ⟨fKeysIn_mono (addVN_sub D entry.vn) hargs0, fun {P} => ?_⟩
      rw [fKeysEval_congr_in hfev1 hargs0, fKeysEval_congr_in hfev1 hIn0]; exact hwp0
    · by_cases hvnEq : l.vn = entry.vn
      · obtain ⟨jl, hjl⟩ := List.mem_iff_getElem?.1 hl
        if hjeq : jl = j then
          subst hjeq; rw [hj] at hjl; cases Option.some.inj hjl
          refine ⟨keyIn_mono (addVN_sub D entry.vn) (haddr ▸ haIn), ?_⟩
          dsimp only [ρ₁]
          rw [het, haddr, hfev1 aKey haIn, haev, fupd_eq]
          exact hv
        else
          exact absurd hvnEq (hTwf.2.2.2.2.2 jl j l entry hjeq hjl hj)
      · have hIn0 : D l.vn = true := by
          simp only [addVN, Bool.or_eq_true, beq_iff_eq] at hIn
          exact hIn.resolve_right hvnEq
        rcases hOk.2 l hl hIn0 with ⟨ha0, hld0⟩
        refine ⟨keyIn_mono (addVN_sub D entry.vn) ha0, ?_⟩
        have hveq : ρ₁ l.lt l.vn = ρ l.lt l.vn := fupd_ne ρ v hvnEq
        rw [hfev1 l.addr ha0, hveq]
        exact hld0
    · intro i hi
      simp only [addVN, Bool.or_eq_true, beq_iff_eq] at hi
      rcases hi with hi | rfl
      · exact hDlt i hi
      · exact hvn
    · intro e he s hrs
      have hdisj := hTwf.2.2.2.2.1 e he entry hmem s hrs
      rcases hAtom e he s hrs with hT | hF
      · left; intro i h1 h2; exact addVN_sub D entry.vn i (hT i h1 h2)
      · right; intro i h1 h2
        have hne : i ≠ entry.vn := by omega
        simp [addVN, hF i h1 h2, hne]

private theorem storeArmE_extract_taken {Γ : Env} {rs jTs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {tgt : TermTarget rs jTs} (st : Ty) (base : Nat)
    (Qend : List Nat → SymTbl → Prop) (aGoal : FKey i64) :
    ∀ (p : StoreStep) {tbl : SymTbl} {D : Nat → Bool} {hits : List Nat} {ρ : FEnv}
      {e₂ : Expr Val Cont rs},
    StoreStepSpec tgt st false Qend p tbl D hits aGoal ρ e₂ →
    SymTblWf base tbl → PartialTblOk m D ρ tbl →
    (∀ i, D i = true → i < tbl.vnNext) → DAtom tbl.ops D →
    (∀ l ∈ tbl.loads, l.slot ∈ hits → D l.vn = true) → wp Γ Q X e₂ m →
    ∃ (D' : Nat → Bool) (ρ' : FEnv) (tbl' : SymTbl) (hits' : List Nat),
      (∀ i, D i = true → D' i = true) ∧
      (∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ' = fk.fev ρ) ∧
      SymTblWf base tbl' ∧ tbl.vnNext ≤ tbl'.vnNext ∧ tbl'.loads = tbl.loads ∧
      (∀ e ∈ tbl.ops, e ∈ tbl'.ops) ∧
      PartialTblOk m D' ρ' tbl' ∧ DAtom tbl'.ops D' ∧
      (∀ l ∈ tbl'.loads, l.slot ∈ hits' → D' l.vn = true) ∧
      Qend hits' tbl' ∧ KeyIn D' aGoal
  | .let_ rest, tbl, D, hits, ρ, .let_ op k, hsp, hTwf, hOk, hDlt, hAtom, hHits, hwp => by
    rcases hsp with ⟨hsafe, kArgs, hkev, hkIn, hkLt, hsp'⟩
    dsimp only [wp, Op.wp] at hwp
    obtain ⟨r₀, hiff⟩ := OpCode.wp_isSafeOp_iff op.code hsafe (vals op.args)
    have hk_wp := (hiff _).1 hwp
    have hiff_k : ∀ P, OpCode.wp op.code (fKeysEval ρ kArgs) P ↔ P r₀ := fun P => by
      rw [hkev]; exact hiff P
    have hInt := symTblWf_internOp hTwf op.code hsafe kArgs hkLt
    rcases partialTblOk_let_step hTwf hOk hDlt hAtom op.code hsafe kArgs hkIn hkLt r₀ hiff_k
      with ⟨ρ₁, hfev1, hres1, hOk1, hAtom1⟩
    have hDlt1 : ∀ i, addKeys D (tbl.internOp op.code kArgs).1 i = true →
        i < (tbl.internOp op.code kArgs).2.vnNext :=
      addKeys_disjoint_lt hInt.2.2.1 (fun i hi => Nat.lt_of_lt_of_le (hDlt i hi) hInt.2.1)
    have hHits1 : ∀ l ∈ (tbl.internOp op.code kArgs).2.loads, l.slot ∈ hits →
        addKeys D (tbl.internOp op.code kArgs).1 l.vn = true :=
      fun l hl hm => addKeys_sub D _ l.vn (hHits l (hInt.2.2.2.2 ▸ hl) hm)
    rcases storeArmE_extract_taken st base Qend aGoal rest
      (hsp' r₀ ρ₁ hfev1 hres1) hInt.1 hOk1 hDlt1 hAtom1 hHits1 hk_wp with
      ⟨D', ρ', tbl', hits', hsub', hfev', hTwf', hle', hloads', hops', hOk', hAtom',
        hHits', hQend, haG⟩
    exact ⟨D', ρ', tbl', hits',
      fun i hi => hsub' i (addKeys_sub D _ i hi),
      fun fk hk => (hfev' fk (keyIn_mono (addKeys_sub D _) hk)).trans (hfev1 fk hk),
      hTwf', Nat.le_trans hInt.2.1 hle', hloads'.trans hInt.2.2.2.2,
      fun e he => hops' e (hInt.2.2.2.1 e he), hOk', hAtom', hHits', hQend, haG⟩
  | .loadEmit _, _, _, _, _, .load _ _ _, hsp, _, _, _, _, _, _ =>
    False.elim (Bool.false_ne_true hsp.1)
  | .loadReuse slot rest, tbl, D, hits, ρ, .load t a k,
    hsp, hTwf, hOk, hDlt, hAtom, hHits, hwp => by
    rcases hsp with ⟨aKey, entry, haev, haIn, _, hfind, rfl, hsp'⟩
    dsimp only [wp] at hwp
    rcases hwp with ⟨v, hv, hk2⟩
    have hmem := findSymLoad_mem tbl.loads t aKey entry hfind
    rcases partialTblOk_loadReuse_step hTwf hOk hDlt hAtom aKey haIn haev entry
      hmem.1 hmem.2.1 hmem.2.2 v hv with ⟨ρ₁, hfev1, hveq, hOk1, hDlt1, hAtom1⟩
    have hHits1 : ∀ l ∈ tbl.loads,
        l.slot ∈ (if hits.contains entry.slot then hits else entry.slot :: hits) →
        addVN D entry.vn l.vn = true := by
      intro l hl hm
      by_cases hc : hits.contains entry.slot = true
      · simp only [hc, ↓reduceIte] at hm; exact addVN_sub D entry.vn _ (hHits l hl hm)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hm
        rcases hm with hslot | hm
        · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem.1
          obtain ⟨jl, hjl⟩ := List.mem_iff_getElem?.1 hl
          have hs1 := (hTwf.2.2.1 j entry hj).1
          have hs2 := (hTwf.2.2.1 jl l hjl).1
          by_cases hjne : j = jl
          · subst hjne; rw [hj] at hjl; cases Option.some.inj hjl; simp [addVN]
          · omega
        · exact addVN_sub D entry.vn _ (hHits l hl hm)
    rcases storeArmE_extract_taken st base Qend aGoal rest
      (hsp' v ρ₁ hfev1 hveq) hTwf hOk1 hDlt1 hAtom1 hHits1 hk2 with
      ⟨D', ρ', tbl', hits', hsub', hfev', hTwf', hle', hloads', hops', hOk', hAtom',
        hHits', hQend, haG⟩
    exact ⟨D', ρ', tbl', hits',
      fun i hi => hsub' i (addVN_sub D entry.vn i hi),
      fun fk hk => (hfev' fk (keyIn_mono (addVN_sub D entry.vn) hk)).trans (hfev1 fk hk),
      hTwf', hle', hloads', hops', hOk', hAtom', hHits', hQend, haG⟩
  | .store _, tbl, D, hits, ρ, .store _ _ _, hsp, hTwf, hOk, _, hAtom, hHits, _ => by
    rcases hsp with ⟨rfl, _, haIn, hQend, _⟩
    exact ⟨D, ρ, tbl, hits, fun _ h => h, fun _ _ => rfl, hTwf, Nat.le_refl _, rfl, fun _ h => h,
      hOk, hAtom, hHits, hQend, haIn⟩
  | .let_ _, _, _, _, _, .load _ _ _, hsp, _, _, _, _, _, _
  | .let_ _, _, _, _, _, .store _ _ _, hsp, _, _, _, _, _, _
  | .let_ _, _, _, _, _, .call _ _ _, hsp, _, _, _, _, _, _
  | .let_ _, _, _, _, _, .jnz _ _ _, hsp, _, _, _, _, _, _
  | .let_ _, _, _, _, _, .jump _ _, hsp, _, _, _, _, _, _
  | .let_ _, _, _, _, _, .ret _, hsp, _, _, _, _, _, _
  | .let_ _, _, _, _, _, .exit _ _, hsp, _, _, _, _, _, _
  | .let_ _, _, _, _, _, .hlt, hsp, _, _, _, _, _, _
  | .let_ _, _, _, _, _, .group _ _, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .let_ _ _, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .store _ _ _, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .call _ _ _, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .jnz _ _ _, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .jump _ _, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .ret _, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .exit _ _, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .hlt, hsp, _, _, _, _, _, _
  | .loadEmit _, _, _, _, _, .group _ _, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .let_ _ _, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .store _ _ _, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .call _ _ _, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .jnz _ _ _, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .jump _ _, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .ret _, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .exit _ _, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .hlt, hsp, _, _, _, _, _, _
  | .loadReuse _ _, _, _, _, _, .group _ _, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .let_ _ _, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .load _ _ _, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .call _ _ _, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .jnz _ _ _, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .jump _ _, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .ret _, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .exit _ _, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .hlt, hsp, _, _, _, _, _, _
  | .store _, _, _, _, _, .group _ _, hsp, _, _, _, _, _, _ => False.elim hsp

private theorem opsFwd_reverse_of_symTblWf {base : Nat} {tbl : SymTbl}
    (hTwf : SymTblWf base tbl) :
    (∀ e ∈ tbl.ops.reverse, ∃ s, e.res = freshFKeys e.ts s ∧ base ≤ s ∧
      isSafeOp e.code = true ∧ fKeysLt s e.args) ∧
    (∀ (i₁ i₂ : Nat) (e₁ e₂ : SymOpEntry), i₁ < i₂ →
      tbl.ops.reverse[i₁]? = some e₁ → tbl.ops.reverse[i₂]? = some e₂ →
      ∀ s₁ s₂, e₁.res = freshFKeys e₁.ts s₁ → e₂.res = freshFKeys e₂.ts s₂ →
      s₁ + e₁.ts.length ≤ s₂) := by
  refine ⟨fun e he => ?_, fun i₁ i₂ e₁ e₂ hlt h1 h2 s₁ s₂ hrs₁ hrs₂ => ?_⟩
  · rcases hTwf.2.1 e (List.mem_reverse.1 he) with ⟨s, hrs, hbs, _, hsafe, hka⟩
    exact ⟨s, hrs, hbs, hsafe, hka⟩
  · have hl₁ := (List.getElem?_eq_some_iff.1 h1).1
    have hl₂ := (List.getElem?_eq_some_iff.1 h2).1
    rw [List.length_reverse] at hl₁ hl₂
    rw [List.getElem?_reverse (by simpa using hl₁)] at h1
    rw [List.getElem?_reverse (by simpa using hl₂)] at h2
    exact hTwf.2.2.2.1 (tbl.ops.length - 1 - i₂) (tbl.ops.length - 1 - i₁) e₂ e₁
      (by omega) h2 h1 s₂ s₁ hrs₂ hrs₁

private theorem completeSymTbl_aux (D : Nat → Bool) (ρ₀ : FEnv) :
    ∀ (ops : List SymOpEntry) (lo : Nat),
    (∀ e ∈ ops, ∃ s, e.res = freshFKeys e.ts s ∧ lo ≤ s ∧
      isSafeOp e.code = true ∧ fKeysLt s e.args) →
    (∀ (i₁ i₂ : Nat) (e₁ e₂ : SymOpEntry), i₁ < i₂ →
      ops[i₁]? = some e₁ → ops[i₂]? = some e₂ →
      ∀ s₁ s₂, e₁.res = freshFKeys e₁.ts s₁ → e₂.res = freshFKeys e₂.ts s₂ →
      s₁ + e₁.ts.length ≤ s₂) →
    (∀ e ∈ ops, fKeysIn D e.res →
      fKeysIn D e.args ∧ ∀ {P : Tup Val e.ts → Prop},
        OpCode.wp e.code (fKeysEval ρ₀ e.args) P ↔ P (fKeysEval ρ₀ e.res)) →
    DAtom ops D →
    ∀ (ρ : FEnv), (∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ = fk.fev ρ₀) →
    ∃ ρ',
      (∀ {u} (fk : FKey u), (KeyIn D fk ∨ fk.FLt lo) → fk.fev ρ' = fk.fev ρ) ∧
      (∀ e ∈ ops, ∀ {P : Tup Val e.ts → Prop},
        OpCode.wp e.code (fKeysEval ρ' e.args) P ↔ P (fKeysEval ρ' e.res))
  | [], _, _, _, _, _, ρ, _ => ⟨ρ, fun _ _ => rfl, fun _ h => by cases h⟩
  | e :: rest, lo, hAll, hOrd, hOkD, hAtom, ρ, hFix => by
    rcases hAll e List.mem_cons_self with ⟨s, hrs, hlo, hsafe, hka⟩
    have hstep : ∃ ρ₁,
        (∀ {u} (fk : FKey u), (KeyIn D fk ∨ fk.FLt lo) → fk.fev ρ₁ = fk.fev ρ) ∧
        ∀ {P : Tup Val e.ts → Prop},
          OpCode.wp e.code (fKeysEval ρ₁ e.args) P ↔ P (fKeysEval ρ₁ e.res) := by
      rcases hAtom e List.mem_cons_self s hrs with hT | hF
      · have hIn := hrs ▸ fKeysIn_freshFKeys_of_all e.ts s hT
        rcases hOkD e List.mem_cons_self hIn with ⟨hArgsIn, hOkE⟩
        refine ⟨ρ, fun _ _ => rfl, fun {P} => ?_⟩
        rw [fKeysEval_congr_in hFix hArgsIn, fKeysEval_congr_in hFix hIn]
        exact hOkE
      · obtain ⟨r, hiff⟩ := OpCode.wp_isSafeOp_iff e.code hsafe (fKeysEval ρ e.args)
        let ρ₁ := fupdTup ρ s r
        have hfev1 : ∀ {u} (fk : FKey u), (KeyIn D fk ∨ fk.FLt lo) → fk.fev ρ₁ = fk.fev ρ := by
          intro u fk hfk
          rcases hfk with hkD | hkLt
          · exact fev_fupdTup_of_disjoint s r hF fk hkD
          · exact FKey.fev_fupdTup r (hkLt.le hlo)
        refine ⟨ρ₁, hfev1, fun {P} => ?_⟩
        rw [fKeysEval_fupdTup (fun fk hfk => FKey.fev_fupdTup r hfk) hka,
            hrs, fKeysEval_freshFKeys ρ e.ts s r]
        exact hiff P
    rcases hstep with ⟨ρ₁, hfev1, hOkE⟩
    have hAll' : ∀ e' ∈ rest, ∃ s', e'.res = freshFKeys e'.ts s' ∧ s + e.ts.length ≤ s' ∧
        isSafeOp e'.code = true ∧ fKeysLt s' e'.args := by
      intro e' he'
      rcases hAll e' (List.mem_cons_of_mem _ he') with ⟨s', hrs', _, hs', hk'⟩
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 he'
      have hle := hOrd 0 (j + 1) e e' (Nat.succ_pos j) rfl hj s s' hrs hrs'
      exact ⟨s', hrs', hle, hs', hk'⟩
    have hOrd' : ∀ (i₁ i₂ : Nat) (e₁ e₂ : SymOpEntry), i₁ < i₂ →
        rest[i₁]? = some e₁ → rest[i₂]? = some e₂ →
        ∀ s₁ s₂, e₁.res = freshFKeys e₁.ts s₁ → e₂.res = freshFKeys e₂.ts s₂ →
        s₁ + e₁.ts.length ≤ s₂ :=
      fun i₁ i₂ e₁ e₂ hlt h1 h2 => hOrd (i₁ + 1) (i₂ + 1) e₁ e₂ (by omega) h1 h2
    have hOkD' : ∀ e' ∈ rest, fKeysIn D e'.res →
        fKeysIn D e'.args ∧ ∀ {P : Tup Val e'.ts → Prop},
          OpCode.wp e'.code (fKeysEval ρ₀ e'.args) P ↔ P (fKeysEval ρ₀ e'.res) :=
      fun e' he' => hOkD e' (List.mem_cons_of_mem _ he')
    have hAtom' : DAtom rest D := fun e' he' => hAtom e' (List.mem_cons_of_mem _ he')
    have hFix' : ∀ {u} (fk : FKey u), KeyIn D fk → fk.fev ρ₁ = fk.fev ρ₀ :=
      fun fk hk => (hfev1 fk (Or.inl hk)).trans (hFix fk hk)
    rcases completeSymTbl_aux D ρ₀ rest (s + e.ts.length)
        hAll' hOrd' hOkD' hAtom' ρ₁ hFix' with
      ⟨ρ₂, hfev2, hDone2⟩
    refine ⟨ρ₂, fun fk hk => ?_, fun e' he' {P} => ?_⟩
    · rcases hk with hkD | hkLt
      · exact (hfev2 fk (Or.inl hkD)).trans (hfev1 fk (Or.inl hkD))
      · exact (hfev2 fk (Or.inr (hkLt.le (by omega)))).trans (hfev1 fk (Or.inr hkLt))
    · cases he' with
      | head =>
        have hevA : fKeysEval ρ₂ e.args = fKeysEval ρ₁ e.args :=
          fKeysEval_fupdTup (fun fk hfk => hfev2 fk (Or.inr hfk)) (hka.le (Nat.le_add_right _ _))
        have hevR : fKeysEval ρ₂ e.res = fKeysEval ρ₁ e.res :=
          fKeysEval_fupdTup (fun fk hfk => hfev2 fk (Or.inr hfk))
            (hrs ▸ fKeysLt_freshFKeys e.ts s)
        rw [hevA, hevR]; exact hOkE
      | tail _ hm => exact hDone2 e' hm

private theorem completeSymTbl {m : Mem 64} {base : Nat} {tbl : SymTbl} {D : Nat → Bool}
    {ρ₀ : FEnv} (hTwf : SymTblWf base tbl) (hOk : PartialTblOk m D ρ₀ tbl)
    (hAtom : DAtom tbl.ops D) (hLoads : ∀ l ∈ tbl.loads, D l.vn = true) :
    ∃ ρ', (∀ {u} (fk : FKey u), (KeyIn D fk ∨ fk.FLt base) → fk.fev ρ' = fk.fev ρ₀) ∧
      SymTblOk m ρ' tbl := by
  have hFwd := opsFwd_reverse_of_symTblWf hTwf
  have hOkRev : ∀ e ∈ tbl.ops.reverse, fKeysIn D e.res →
      fKeysIn D e.args ∧ ∀ {P : Tup Val e.ts → Prop},
        OpCode.wp e.code (fKeysEval ρ₀ e.args) P ↔ P (fKeysEval ρ₀ e.res) :=
    fun e he => hOk.1 e (List.mem_reverse.1 he)
  have hAtomRev : DAtom tbl.ops.reverse D := fun e he => hAtom e (List.mem_reverse.1 he)
  rcases completeSymTbl_aux D ρ₀ tbl.ops.reverse base hFwd.1 hFwd.2 hOkRev hAtomRev ρ₀
      (fun _ _ => rfl) with
    ⟨ρ', hfev, hOps⟩
  refine ⟨ρ', hfev, fun e he {P} => hOps e (List.mem_reverse.2 he), fun l hl => ?_⟩
  have hDvn := hLoads l hl
  rcases hOk.2 l hl hDvn with ⟨haD, hld⟩
  have ha : l.addr.fev ρ' = l.addr.fev ρ₀ := hfev l.addr (Or.inl haD)
  have hv : ρ' l.lt l.vn = ρ₀ l.lt l.vn := hfev (.var l.vn) (Or.inl hDvn)
  rw [ha, hv]
  exact hld

@[expose] def TblSub (t₁ t₂ : SymTbl) : Prop :=
  (∀ e ∈ t₁.ops, e ∈ t₂.ops) ∧ (∀ l ∈ t₁.loads, l ∈ t₂.loads)

private theorem internOp_sub (tbl : SymTbl) : {sig ts : List Ty} →
    (code : OpCode sig ts) → (args : Tup FKey sig) →
    (∀ e ∈ tbl.ops, e ∈ (tbl.internOp code args).2.ops) ∧
    (tbl.internOp code args).2.loads = tbl.loads
  | _, _, .copy _, (_, ()) => ⟨fun _ h => h, rfl⟩
  | sig, ts, code, args => by
    unfold SymTbl.internOp
    split
    · exact ⟨fun _ h => h, rfl⟩
    · cases findSymOp tbl.ops sig ts code args with
      | some _ => exact ⟨fun _ h => h, rfl⟩
      | none => exact ⟨fun _ h => List.mem_cons_of_mem _ h, rfl⟩

private theorem symTblOk_internOp_wp {m : Mem 64} {tbl tbl₁ : SymTbl} {ρs : FEnv}
    (hOk1 : SymTblOk m ρs tbl₁)
    {sig ts : List Ty} (code : OpCode sig ts) (kArgs : Tup FKey sig)
    (hSub0 : ∀ e ∈ tbl.ops, e ∈ tbl₁.ops)
    (hSub1 : ∀ e ∈ (tbl.internOp code kArgs).2.ops, e ∈ tbl₁.ops)
    {P : Tup Val ts → Prop} :
    OpCode.wp code (fKeysEval ρs kArgs) P ↔ P (fKeysEval ρs (tbl.internOp code kArgs).1) := by
  revert hSub1
  unfold SymTbl.internOp
  split
  · intro _; exact Iff.rfl
  · intro hSub1
    cases hf : findSymOp tbl.ops sig ts code kArgs with
    | some res =>
      exact hOk1.1 _ (hSub0 _ (findSymOp_mem tbl.ops sig ts code kArgs res hf))
    | none =>
      rw [hf] at hSub1
      exact hOk1.1 _ (hSub1 _ List.mem_cons_self)

private theorem tblSub_of_storeStepSpec {rs jTs : List Ty} {tgt : TermTarget rs jTs} {st : Ty}
    {tbl₁ : SymTbl} :
    ∀ (p : StoreStep) {tbl : SymTbl} {D : Nat → Bool} {hits : List Nat} {aGoal : FKey i64}
      {ρ : FEnv} {e₂ : Expr Val Cont rs},
    StoreStepSpec tgt st true (fun _ t => t = tbl₁) p tbl D hits aGoal ρ e₂ →
    TblSub tbl tbl₁
  | .let_ rest, tbl, _, _, _, ρ, .let_ op k, hsp => by
    rcases hsp with ⟨_, kArgs, _, _, _, hsp'⟩
    have ih : TblSub (tbl.internOp op.code kArgs).2 tbl₁ := tblSub_of_storeStepSpec rest
      (hsp' (fKeysEval ρ (tbl.internOp op.code kArgs).1) ρ (fun _ _ => rfl) rfl)
    have hsub := internOp_sub tbl op.code kArgs
    exact ⟨fun e he => ih.1 e (hsub.1 e he), fun l hl => ih.2 l (by rw [hsub.2]; exact hl)⟩
  | .loadEmit rest, tbl, _, _, _, ρ, .load t _ k, hsp => by
    rcases hsp with ⟨_, _, _, _, _, _, hsp'⟩
    have ih := tblSub_of_storeStepSpec rest (hsp' (ρ t tbl.vnNext) ρ (fun _ _ => rfl) rfl)
    exact ⟨ih.1, fun l hl => ih.2 l (List.mem_append_left _ hl)⟩
  | .loadReuse _ rest, tbl, _, _, _, ρ, .load t _ k, hsp => by
    rcases hsp with ⟨_, entry, _, _, _, _, _, hsp'⟩
    exact tblSub_of_storeStepSpec rest (hsp' (ρ t entry.vn) ρ (fun _ _ => rfl) rfl)
  | .store _, _, _, _, _, _, .store _ _ _, hsp => by
    rcases hsp with ⟨_, _, _, rfl, _⟩
    exact ⟨fun _ h => h, fun _ h => h⟩
  | .let_ _, _, _, _, _, _, .load _ _ _, hsp | .let_ _, _, _, _, _, _, .store _ _ _, hsp
  | .let_ _, _, _, _, _, _, .call _ _ _, hsp | .let_ _, _, _, _, _, _, .jnz _ _ _, hsp
  | .let_ _, _, _, _, _, _, .jump _ _, hsp | .let_ _, _, _, _, _, _, .ret _, hsp
  | .let_ _, _, _, _, _, _, .exit _ _, hsp | .let_ _, _, _, _, _, _, .hlt, hsp
  | .let_ _, _, _, _, _, _, .group _ _, hsp
  | .loadEmit _, _, _, _, _, _, .let_ _ _, hsp | .loadEmit _, _, _, _, _, _, .store _ _ _, hsp
  | .loadEmit _, _, _, _, _, _, .call _ _ _, hsp | .loadEmit _, _, _, _, _, _, .jnz _ _ _, hsp
  | .loadEmit _, _, _, _, _, _, .jump _ _, hsp | .loadEmit _, _, _, _, _, _, .ret _, hsp
  | .loadEmit _, _, _, _, _, _, .exit _ _, hsp | .loadEmit _, _, _, _, _, _, .hlt, hsp
  | .loadEmit _, _, _, _, _, _, .group _ _, hsp
  | .loadReuse _ _, _, _, _, _, _, .let_ _ _, hsp
  | .loadReuse _ _, _, _, _, _, _, .store _ _ _, hsp
  | .loadReuse _ _, _, _, _, _, _, .call _ _ _, hsp
  | .loadReuse _ _, _, _, _, _, _, .jnz _ _ _, hsp
  | .loadReuse _ _, _, _, _, _, _, .jump _ _, hsp
  | .loadReuse _ _, _, _, _, _, _, .ret _, hsp
  | .loadReuse _ _, _, _, _, _, _, .exit _ _, hsp | .loadReuse _ _, _, _, _, _, _, .hlt, hsp
  | .loadReuse _ _, _, _, _, _, _, .group _ _, hsp
  | .store _, _, _, _, _, _, .let_ _ _, hsp | .store _, _, _, _, _, _, .load _ _ _, hsp
  | .store _, _, _, _, _, _, .call _ _ _, hsp | .store _, _, _, _, _, _, .jnz _ _ _, hsp
  | .store _, _, _, _, _, _, .jump _ _, hsp | .store _, _, _, _, _, _, .ret _, hsp
  | .store _, _, _, _, _, _, .exit _ _, hsp | .store _, _, _, _, _, _, .hlt, hsp
  | .store _, _, _, _, _, _, .group _ _, hsp => False.elim hsp

private theorem hoistStoreStep_untaken_T_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {jTs : List Ty} (tgt : TermTarget rs jTs) (st : Ty)
    (base : Nat) (tbl₁ : SymTbl) (ρs : FEnv) (hOk1 : SymTblOk m ρs tbl₁) :
    ∀ (p : StoreStep) (hn : Nat) (loads : List ((t : Ty) × IVal Val t))
      (ρh : FEnv) (tbl : SymTbl) (Dvn : Nat → Bool) (hits : List Nat) (aGoal : FKey i64)
      {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
      {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → StoreStepSpec tgt st true (fun _ t => t = tbl₁) p tbl Dvn hits aGoal ρs e₂ →
    SymTblWf base tbl → TblSub tbl tbl₁ → IGood ρh hn G →
    LoadsMatchSym ρh ρs hn loads tbl.loads →
    {cont : Nat → List ((t : Ty) × IVal Val t) → Arg (IVal Val) st → Arg (IVal Val) i64 →
      Tup (Arg (IVal Val)) jTs → Expr Val Cont rs} →
    (∀ hn' loads' ρh' v₁ (v₂ : Val st) a₁ (a₂ : Arg Val i64) args₁ vs₂,
      hn ≤ hn' → (∀ {u} (fk : FKey u), fk.FLt hn → fk.fev ρh' = fk.fev ρh) →
      LoadsMatchSym ρh' ρs hn' loads' tbl₁.loads →
      IArgGood ρh' hn' v₁ v₂ → IArgGood ρh' hn' a₁ a₂.val →
      aGoal.fev ρs = a₂.val → IArgsGood ρh' hn' args₁ vs₂ →
      wp Γ Q X (cont hn' loads' v₁ a₁ args₁) m) →
    wp Γ Q X (hoistStoreStep jTs st p hn loads e₁ cont) m
  | .let_ rest, hn, loads, ρh, tbl, Dvn, hits, aGoal, _, _, _, _, hwf, hsp,
    hTwf, hSub, hG, hL, cont, hcont => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code args₁ args₂ hargs =>
        rcases hsp with ⟨hsafe, kArgs, hkev, _, hkLt, hsp'⟩
        dsimp only [hoistStoreStep, wp, Op.wp]
        rw [TRel.iout_vals hG hargs]
        let r₀ := fKeysEval ρs (tbl.internOp code kArgs).1
        have hsp_next := hsp' r₀ ρs (fun _ _ => rfl) rfl
        have hSub1 := tblSub_of_storeStepSpec rest hsp_next
        have hInt := symTblWf_internOp hTwf code hsafe kArgs hkLt
        have hiff : ∀ (P : Tup Val _ → Prop), OpCode.wp code (vals args₂) P ↔ P r₀ := fun P => by
          rw [← hkev]
          exact symTblOk_internOp_wp hOk1 code kArgs hSub.1 hSub1.1
        refine (hiff _).2 ?_
        refine hoistStoreStep_untaken_T_wp tgt st base tbl₁ ρs hOk1 rest (hn + _) loads
          (fupdTup ρh hn r₀) (tbl.internOp code kArgs).2
          (addKeys Dvn (tbl.internOp code kArgs).1) hits aGoal
          (hk (freshIVals _ r₀ hn) r₀) hsp_next hInt.1 hSub1 (hG.freshIVals r₀)
          (loadsMatchSym_mono_h (Nat.le_add_right _ _)
            (fun fk hfk => FKey.fev_fupdTup r₀ hfk) (hInt.2.2.2.2 ▸ hL))
          fun hn' loads' ρh' v₁ v₂ a₁ a₂ args₁ vs₂ hle hev hL'' hv ha haev hargs' => ?_
        exact hcont hn' loads' ρh' v₁ v₂ a₁ a₂ args₁ vs₂
          (Nat.le_trans (Nat.le_add_right _ _) hle)
          (fun fk hk => (hev fk (hk.le (Nat.le_add_right _ _))).trans (FKey.fev_fupdTup r₀ hk))
          hL'' hv ha haev hargs'
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .loadEmit rest, hn, loads, ρh, tbl, Dvn, hits, aGoal, _, _, _, _, hwf, hsp,
    hTwf, _, hG, hL, cont, hcont => by
    cases hwf with
    | load t ha hk =>
      rcases hsp with ⟨_, aKey, haev, _, haLt, _, hsp'⟩
      dsimp only [hoistStoreStep, wp]
      rw [argRel_iout_val hG ha, ← haev]
      let v : Val t := ρs t tbl.vnNext
      have hsp_next := hsp' v ρs (fun _ _ => rfl) rfl
      have hSub1 := tblSub_of_storeStepSpec rest hsp_next
      have hentry_in : ⟨tbl.loads.length, t, aKey, tbl.vnNext⟩ ∈ tbl₁.loads :=
        hSub1.2 _ (by simp)
      have hv : loadVal m t (aKey.fev ρs) = some v := hOk1.2 _ hentry_in
      refine ⟨v, hv, ?_⟩
      have hTwf1 := symTblWf_loadEmit hTwf t aKey haLt
      have hL' := loadsMatchSym_append aKey v hL (fupd ρh hn v) ρs
        (fun fk hfk => FKey.fev_fupd v hfk) (fun _ _ => rfl)
        (by dsimp only [FKey.fev]; exact fupd_eq ρh hn v) rfl
      refine hoistStoreStep_untaken_T_wp tgt st base tbl₁ ρs hOk1 rest (hn + 1)
        (loads ++ [⟨t, (.var v, .var hn)⟩]) (fupd ρh hn v) _
        (addVN Dvn tbl.vnNext) (tbl.loads.length :: hits) aGoal
        (hk (.var v, .var hn) v) hsp_next hTwf1 hSub1 (hG.freshOne v) hL'
        fun hn' loads' ρh' v₁ v₂ a₁ a₂ args₁ vs₂ hle hev hL'' hv' ha' haev' hargs' => ?_
      exact hcont hn' loads' ρh' v₁ v₂ a₁ a₂ args₁ vs₂ (Nat.le_trans (Nat.le_succ _) hle)
        (fun fk hk => (hev fk (hk.le (Nat.le_succ _))).trans (FKey.fev_fupd v hk))
        hL'' hv' ha' haev' hargs'
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .loadReuse slot rest, hn, loads, ρh, tbl, Dvn, hits, aGoal, G, _, _, _, hwf, hsp,
    hTwf, hSub, hG, hL, cont, hcont => by
    cases hwf with
    | load t _ hk =>
      rcases hsp with ⟨aKey, entry, _, _, _, hfind, rfl, hsp'⟩
      have hmem := findSymLoad_mem tbl.loads t aKey entry hfind
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hmem.1
      have hsl := (hTwf.2.2.1 j entry hj).1
      rcases loadsMatchSym_lookup hL (hsl ▸ hj) hmem.2.1 with
        ⟨iv, hl_eq, hiv1, hiv2, hivlt⟩
      dsimp only [hoistStoreStep]
      rw [hl_eq]; dsimp only
      cases hdec : tyDecEq t t with
      | isFalse hne => exact absurd rfl hne
      | isTrue _ =>
        have hG' : IGood ρh hn (⟨t, iv, ρs t entry.vn⟩ :: G) := fun p hp => by
          cases hp with
          | head => exact ⟨by rw [hiv1]; rfl, hiv2, hivlt⟩
          | tail _ hm => exact hG p hm
        have hsp_next := hsp' (ρs t entry.vn) ρs (fun _ _ => rfl) rfl
        exact hoistStoreStep_untaken_T_wp tgt st base tbl₁ ρs hOk1 rest hn loads ρh tbl
          (addVN Dvn entry.vn) _ aGoal (hk iv (ρs t entry.vn)) hsp_next hTwf hSub hG' hL hcont
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .store tail, hn, loads, ρh, tbl, _, _, aGoal, _, _, _, _, hwf, hsp,
    _, _, hG, hL, cont, hcont => by
    cases hwf with
    | store hv ha hk =>
      rcases hsp with ⟨hst, haev, _, htbl, htail⟩
      subst hst; subst htbl
      dsimp only [hoistStoreStep]
      cases hdec : tyDecEq _ _ with
      | isFalse hne => exact absurd rfl hne
      | isTrue _ =>
        refine hoistStoreTail_untaken_wp tgt tail hn hk htail hG
          fun hn' ρh' args₁ vs₂ hle hev hargs' => ?_
        have hL' := loadsMatchSym_mono_h hle hev hL
        have hv' := iargGood_mono hle hev (iargGood_of_argRel hG hv)
        have ha' := iargGood_mono hle hev (iargGood_of_argRel hG ha)
        exact hcont hn' loads ρh' _ _ _ _ args₁ vs₂ hle hev hL' hv' ha' haev hargs'
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

/-! ## Store-sinking diamond hoisting `WP` (`hoistStoreArms_wp`) -/

theorem hoistStoreArms_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {jTs : List Ty} (tgt : TermTarget rs jTs) (hsig : isSelectSig jTs = true)
    (sp : StoreDiamondPlan) (next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val}
    {D : Ctx (JLabel Cont) Cont}
    {c₁ : Arg (IVal Val) .bool} {c₂ : Arg Val .bool}
    {t₁ e₁ : Expr (IVal Val) (JLabel Cont) rs} {t₂ e₂ : Expr Val Cont rs}
    (hc : ArgRel G .bool c₁ c₂) (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hsp : StoreDiamondSpec tgt sp next ρ t₂ e₂) (hG : IGood ρ next G)
    (hwp : wp Γ Q X (.jnz c₂ t₂ e₂) m)
    {fin : Tup (Arg Val) jTs → Expr Val Cont rs}
    (hfin : ∀ (sel : Tup (Arg Val) jTs) (m' : Mem 64),
      tgt.wp Q (vals sel) m' → wp Γ Q X (fin sel) m') :
    wp Γ Q X (hoistStoreArms jTs sp next c₁ t₁ e₁ fin) m := by
  rcases hsp with ⟨hselTy, tbl₁, aGoal, hTwf1, _, haLt, hspT, hspE⟩
  dsimp only [hoistStoreArms]
  dsimp only [wp] at hwp
  have hce := argRel_iout_val hG hc
  refine bool_val_cases hce (fun hcv hcv1 => ?_) (fun hcv hcv1 => ?_)
  · have hspT0 := hspT ρ (fun _ _ => rfl)
    refine hoistStoreStep_taken_wp tgt sp.storeTy true next (fun _ tbl => tbl = tbl₁) sp.armT
      next [] ρ ρ ⟨next, [], []⟩ (fun i => decide (i < next)) [] aGoal ht hspT0
      (symTblWf_empty next) (symTblOk_empty m ρ next) hG (loadsMatchSym_empty ρ ρ next)
      (fun i hi => by simpa using hi) (hwp.1 hcv)
      fun hn₁ loads₁ ρh₁ ρs₁ tbl₁' _ vT₁ vT₂ aT₁ aT₂ argsT₁ vsT hleH₁ _
        heqH₁ heqS₁ _ hOk₁ htblEq hL₁ hvT haT haevT hargsT htgtT hstokT => ?_
    rw [htblEq] at hOk₁ hL₁
    have hspE1 := hspE ρs₁ (fun fk hfk => heqS₁ fk hfk)
    refine hoistStoreStep_untaken_E_wp tgt sp.storeTy next
      (fun hits tbl => tbl.loads = tbl₁.loads ∧ ∀ s, s < tbl₁.loads.length → s ∈ hits)
      sp.armE hn₁ loads₁ ρh₁ ρs₁ tbl₁ (fun i => decide (i < next)) [] aGoal he hspE1
      hTwf1 hOk₁ (hG.mono hleH₁ heqH₁) hL₁
      (fun i hi => Nat.lt_of_lt_of_le (by simpa using hi) hTwf1.1)
      fun hn₂ ρh₂ vE₁ vE₂ _ argsE₁ vsE hleH₂ heqH₂ hvE hargsE => ?_
    have hvT₂ := iargGood_mono hleH₂ heqH₂ hvT
    have haT₂ := iargGood_mono hleH₂ heqH₂ haT
    have hargsT₂ := iargsGood_mono hleH₂ heqH₂ hargsT
    refine emitSelectTy_ext_wp (iout c₁) sp.storeTy hselTy ρh₂ hn₂ hvT₂ hvE
      fun ρh₃ hn₃ selV hle₃ heq₃ hselV => ?_
    have haT₃ := iargGood_mono hle₃ heq₃ haT₂
    have hargsT₃ := iargsGood_mono hle₃ heq₃ hargsT₂
    have hargsE₃ := iargsGood_mono hle₃ heq₃ hargsE
    dsimp only [wp]
    rw [haT₃.1, hselV, hcv1]
    refine ⟨hstokT, ?_⟩
    refine emitSelectTup_wp (iout c₁) jTs hsig ρh₃ hn₃ hargsT₃ hargsE₃ fun sel hsel_eq => ?_
    refine hfin sel (storeMem m sp.storeTy aT₂.val vT₂) ?_
    simpa [hsel_eq, hcv1] using htgtT
  · have hD0_lt : ∀ i, decide (i < next) = true → i < tbl₁.vnNext :=
      fun i hi => Nat.lt_of_lt_of_le (by simpa using hi) hTwf1.1
    rcases partialTblOk_of_symTblWf_base m ρ hTwf1 with ⟨hPOk0, hAtom0⟩
    rcases storeArmE_extract_taken sp.storeTy next
      (fun hits tbl => tbl.loads = tbl₁.loads ∧ ∀ s, s < tbl₁.loads.length → s ∈ hits) aGoal
      sp.armE (hspE ρ (fun _ _ => rfl)) hTwf1 hPOk0 hD0_lt hAtom0
      (fun _ _ hm => by cases hm) (hwp.2 hcv) with
      ⟨D_E, ρ_E, tbl_E, _, hsubE, hfevE, _, _, hloadsE, hopsE, hPOkE, hAtomE, hHitsE,
        ⟨_, hallHits⟩, _⟩
    have hPOk1 : PartialTblOk m D_E ρ_E tbl₁ :=
      ⟨fun e he => hPOkE.1 e (hopsE e he), fun l hl => hPOkE.2 l (hloadsE.symm ▸ hl)⟩
    have hAtom1 : DAtom tbl₁.ops D_E := fun e he => hAtomE e (hopsE e he)
    have hLoads1 : ∀ l ∈ tbl₁.loads, D_E l.vn = true := by
      intro l hl
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hl
      have hsl := (hTwf1.2.2.1 j l hj).1
      have hjlt : j < tbl₁.loads.length := (List.getElem?_eq_some_iff.1 hj).1
      exact hHitsE l (hloadsE.symm ▸ hl) (hsl ▸ hallHits j hjlt)
    rcases completeSymTbl hTwf1 hPOk1 hAtom1 hLoads1 with ⟨ρ_sh, hfev_sh, hOk_sh⟩
    have hEq_sh : ∀ {u} (fk : FKey u), fk.FLt next → fk.fev ρ_sh = fk.fev ρ := by
      intro u fk hfk
      have hD : KeyIn (fun i => decide (i < next)) fk := by
        cases fk with | imm _ => trivial | var i => exact decide_eq_true hfk
      have hDE : KeyIn D_E fk := keyIn_mono hsubE hD
      exact (hfev_sh fk (Or.inl hDE)).trans (hfevE fk hD)
    refine hoistStoreStep_untaken_T_wp tgt sp.storeTy next tbl₁ ρ_sh hOk_sh sp.armT
      next [] ρ ⟨next, [], []⟩ (fun i => decide (i < next)) [] aGoal ht
      (hspT ρ_sh hEq_sh) (symTblWf_empty next) ⟨(fun _ h => by cases h), (fun _ h => by cases h)⟩
      hG (loadsMatchSym_empty ρ ρ_sh next)
      fun hn₁ loads₁ ρh₁ vT₁ vT₂ aT₁ aT₂ argsT₁ vsT hleH₁ heqH₁ hL₁ hvT haT haevT hargsT => ?_
    refine hoistStoreStep_taken_wp tgt sp.storeTy false next
      (fun hits tbl => tbl.loads = tbl₁.loads ∧ ∀ s, s < tbl₁.loads.length → s ∈ hits)
      sp.armE hn₁ loads₁ ρh₁ ρ_sh tbl₁ (fun i => decide (i < next)) [] aGoal he
      (hspE ρ_sh hEq_sh) hTwf1 hOk_sh (hG.mono hleH₁ heqH₁) hL₁
      (fun i hi => Nat.lt_of_lt_of_le (by simpa using hi) hTwf1.1) (hwp.2 hcv)
      fun hn₂ loads₂ ρh₂ ρs₂ tbl₂ _ vE₁ vE₂ _ aE₂ argsE₁ vsE hleH₂ _
        heqH₂ heqS₂ _ _ _ _ hvE _ haevE hargsE htgtE hstokE => ?_
    have hvT₂ := iargGood_mono hleH₂ heqH₂ hvT
    have haT₂ := iargGood_mono hleH₂ heqH₂ haT
    have hargsT₂ := iargsGood_mono hleH₂ heqH₂ hargsT
    have haeq : aE₂.val = aT₂.val :=
      haevE.symm.trans ((heqS₂ aGoal haLt).trans haevT)
    refine emitSelectTy_ext_wp (iout c₁) sp.storeTy hselTy ρh₂ hn₂ hvT₂ hvE
      fun ρh₃ hn₃ selV hle₃ heq₃ hselV => ?_
    have haT₃ := iargGood_mono hle₃ heq₃ haT₂
    have hargsT₃ := iargsGood_mono hle₃ heq₃ hargsT₂
    have hargsE₃ := iargsGood_mono hle₃ heq₃ hargsE
    dsimp only [wp]
    rw [haT₃.1, hselV, hcv1, ← haeq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨hstokE, ?_⟩
    refine emitSelectTup_wp (iout c₁) jTs hsig ρh₃ hn₃ hargsT₃ hargsE₃ fun sel hsel_eq => ?_
    refine hfin sel (storeMem m sp.storeTy aE₂.val vE₂) ?_
    simpa [hsel_eq, hcv1] using htgtE

end IfOptImpl

end LeanQbe.T
