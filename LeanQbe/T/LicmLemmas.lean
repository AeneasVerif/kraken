module

public import LeanQbe.T.Licm
public import LeanQbe.T.GvnLemmas
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.Legal

/-!
# Correctness of Loop-Invariant Code Motion (`Func.licm`)

* `OpCode.isLicmPure_spec`: every `OpCode` accepted by `isLicmPure` is unconditionally total and
  deterministic (`∃ r, ∀ post, c.wp args post ↔ post r`), allowing sound hoisting out of loops
  and conditional branches without side conditions or trip-count guards.
* `EnvWp` / `resolveArgs_wp` / `emitHoists_wp` / `licmSweep_wp`: WP preservation for arbitrary
  (untrusted) `HoistPlan`s, reusing `GoodG` and `GoodT` from `GvnLemmas`.
* `EnvRel` / `resolveArgs_rel` / `emitHoists_wf` / `licmSweep_wf`: relational `Wf` preservation
  for arbitrary `HoistPlan`s, reusing `RelG` and `RelT` from `GvnLemmas` and `castTy_rel` from
  `FlatLemmas`.
* `Func.licm_supportsSource`: `Func.licm` preserves `Func.supportsSource target` for any
  `LegalTarget` and well-formed `f`.
* `Func.licm_wf`, `Func.licm_spec`, `Fn.licm_wf`, `Fn.licm_spec`: closed-function specifications.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Pure total determinism (`OpCode.isLicmPure_spec`) -/

private theorem cond_false_det {b : Bool} {rs : List Ty} (r : Tup Val rs) (hb : (!b) = true) :
    ∃ r' : Tup Val rs, ∀ post : Tup Val rs → Prop, (if b then False else post r) ↔ post r' := by
  cases b with
  | false => exact ⟨r, fun _ => Iff.rfl⟩
  | true => cases hb

private theorem cond1_det {c : Prop} {rs : List Ty} (r : Tup Val rs) (hc : c) :
    ∃ r' : Tup Val rs, ∀ post : Tup Val rs → Prop, (c ∧ post r) ↔ post r' :=
  ⟨r, fun _ => ⟨fun hp => hp.2, fun hp => ⟨hc, hp⟩⟩⟩

private theorem cond2_det {c₁ c₂ : Prop} {rs : List Ty} (r : Tup Val rs) (h1 : c₁) (h2 : c₂) :
    ∃ r' : Tup Val rs, ∀ post : Tup Val rs → Prop, (c₁ ∧ c₂ ∧ post r) ↔ post r' :=
  ⟨r, fun _ => ⟨fun hp => hp.2.2, fun hp => ⟨h1, h2, hp⟩⟩⟩

/-- Every `OpCode` accepted by `OpCode.isLicmPure` is unconditionally total and deterministic. -/
theorem OpCode.isLicmPure_spec : {as rs : List Ty} → (c : OpCode as rs) →
    c.isLicmPure = true → (args : Tup Val as) →
    ∃ r : Tup Val rs, ∀ post : Tup Val rs → Prop, c.wp args post ↔ post r
  | _, _, .copy _, _, (a, ()) => ⟨(a, ()), fun _ => Iff.rfl⟩
  | _, _, .add _, h, (_, _, ()) => cond_false_det _ h
  | _, _, .sub _, h, (_, _, ()) => cond_false_det _ h
  | _, _, .mul _, h, (_, _, ()) => cond_false_det _ h
  | _, _, .neg _, h, (_, ()) => cond_false_det _ h
  | _, _, .and _, _, (_, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .or _, _, (_, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .xor _, _, (_, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .not _, _, (_, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .ternlog _ _, _, (_, _, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .shl _, h, (_, _, ()) => cond_false_det _ h
  | _, _, .lshr _, h, (_, _, ()) => cond_false_det _ h
  | _, _, .ashr _, h, (_, _, ()) => cond_false_det _ h
  | _, _, .rotl _, h, (_, _, ()) => cond_false_det _ h
  | _, _, .rotr _, h, (_, _, ()) => cond_false_det _ h
  | _, _, .fshl _, _, (_, _, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .fshr _, _, (_, _, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .bswap t, h, (a, ()) => by
    have hb : t.bswapOk = true := h
    exact cond_false_det (b := !t.bswapOk) (rs := [t]) (lift1 bswapBits id t a, ()) (by simp [hb])
  | _, _, .clz _, _, (_, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .cls _, _, (_, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .rbit _, _, (_, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .ctz _, _, (_, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .popcnt _, _, (_, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .cmp _ _ _ rfl, h, (_, _, ()) => cond_false_det _ h
  | _, _, .select _, _, (_, _, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .blend _ _ rfl, _, (_, _, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .zext m n, h, (a, ()) =>
    cond1_det (rs := [.bits n]) (a.setWidth n, ()) (Nat.le_of_ble_eq_true h)
  | _, _, .sext m n, h, (a, ()) =>
    cond1_det (rs := [.bits n]) (a.signExtend n, ()) (Nat.le_of_ble_eq_true h)
  | _, _, .trunc m n, h, (a, ()) =>
    cond1_det (rs := [.bits n]) (a.setWidth n, ()) (Nat.le_of_ble_eq_true h)
  | _, _, .ofBool _, _, (_, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .addc _, _, (_, _, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .subb _, _, (_, _, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .umulw _, _, (_, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .smulw _, _, (_, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .bitcast _ _ _, _, (_, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .shufd t imm, h, (a, ()) => by
    have h' : (!t.hasFloat && t.size != 0 && t.size % 128 == 0) = true := h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h'
    exact cond2_det (rs := [t]) (ofBits t (shuffleDwords (toBits t a) imm), ()) h'.1.2 h'.2
  | _, _, .shufb t, h, (a, m, ()) => by
    have h' : (!t.hasFloat && t.size != 0 && t.size % 128 == 0) = true := h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h'
    exact cond2_det (rs := [t]) (ofBits t (shuffleBytes (toBits t a) (toBits t m)), ()) h'.1.2 h'.2
  | _, _, .alignr t imm, h, (hi, lo, ()) => by
    have h' : (!t.hasFloat && t.size != 0 && t.size % 128 == 0) = true := h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h'
    exact cond2_det (rs := [t]) (ofBits t (alignBytes (toBits t hi) (toBits t lo) imm), ())
      h'.1.2 h'.2
  | _, _, .blendw t imm, h, (a, b, ()) => by
    have h' : (!t.hasFloat && t.size != 0 && t.size % 128 == 0) = true := h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h'
    exact cond2_det (rs := [t]) (ofBits t (blendWords (toBits t a) (toBits t b) imm), ())
      h'.1.2 h'.2
  | _, _, .sha256rnds2, _, (_, _, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .sha256msg1, _, (_, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .sha256msg2, _, (_, _, ()) => ⟨_, fun _ => Iff.rfl⟩
  | _, _, .udiv _, h, _ | _, _, .sdiv _, h, _ | _, _, .urem _, h, _ | _, _, .srem _, h, _
  | _, _, .udiv0 _, h, _ | _, _, .sdiv0 _, h, _ | _, _, .mkpair _ _, h, _
  | _, _, .unpair _ _, h, _ | _, _, .fadd _, h, _ | _, _, .fsub _, h, _
  | _, _, .fmul _, h, _ | _, _, .fdiv _, h, _ | _, _, .ffma _, h, _ | _, _, .fsqrt _, h, _
  | _, _, .fneg _, h, _ | _, _, .fabs _, h, _ | _, _, .fcmp _ _ _ _, h, _
  | _, _, .fptoui _ _, h, _ | _, _, .fptosi _ _, h, _ | _, _, .uitofp _ _, h, _
  | _, _, .sitofp _ _, h, _ | _, _, .fcvt _ _, h, _ => nomatch h

/-! ## Lexical environment WP invariants (`EnvWp`, `resolveArgs_wp`, `emitHoists_wp`) -/

private theorem castTy_some_eq {V : Ty → Type} :
    {t' t : Ty} → {v : V t'} → {v' : V t} →
    castTy t' t v = some v' → ∃ h : t' = t, h ▸ v = v'
  | .bool, .bool, _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | .bits m, .bits n, _, _, h => by
    simp only [castTy] at h
    split at h
    · next heq => subst heq; cases h; exact ⟨rfl, rfl⟩
    · cases h
  | .float f, .float g, _, _, h => by
    simp only [castTy] at h
    split at h
    · next heq => subst heq; cases h; exact ⟨rfl, rfl⟩
    · cases h
  | .pair a1 b1, .pair a2 b2, _, _, h => by
    simp only [castTy] at h
    cases h1 : tyDecEq a1 a2 with
    | isFalse _ => simp [h1] at h
    | isTrue heq1 =>
      subst heq1
      cases h2 : tyDecEq b1 b2 with
      | isFalse _ => simp [h1, h2] at h
      | isTrue heq2 =>
        subst heq2
        simp only [h1, h2, Option.some.injEq] at h
        exact ⟨rfl, h⟩
  | .bool, .bits _, _, _, h | .bool, .float _, _, _, h | .bool, .pair _ _, _, _, h
  | .bits _, .bool, _, _, h | .bits _, .float _, _, _, h | .bits _, .pair _ _, _, _, h
  | .float _, .bool, _, _, h | .float _, .bits _, _, _, h | .float _, .pair _ _, _, _, h
  | .pair _ _, .bool, _, _, h | .pair _ _, .bits _, _, _, h | .pair _ _, .float _, _, _, h =>
    nomatch h

/-- Every entry in `env : VEnv Val` has level `< b` and agrees with valuation `ρ`. -/
def EnvWp (ρ : FEnv) (b : Nat) (env : VEnv Val) : Prop :=
  ∀ (lvl : Nat) (p : (t : Ty) × Val t), env.find? lvl = some p → lvl < b ∧ ρ p.1 lvl = p.2

theorem EnvWp.empty (ρ : FEnv) (b : Nat) : EnvWp ρ b .empty :=
  fun _ _ h => nomatch h

theorem EnvWp.insert_fresh {ρ : FEnv} {b : Nat} {env : VEnv Val} (hE : EnvWp ρ b env)
    {t : Ty} (v : Val t) : EnvWp (fupd ρ b v) (b + 1) (env.insert b ⟨t, v⟩) := by
  intro lvl p hfind
  rw [Trie.find?_insert] at hfind
  split at hfind
  · next heq =>
    subst heq; cases hfind
    exact ⟨Nat.lt_succ_self _, fupd_eq ρ lvl v⟩
  · next hne =>
    obtain ⟨hlt, hev⟩ := hE lvl p hfind
    exact ⟨Nat.lt_succ_of_lt hlt, (fupd_ne ρ v hne).trans hev⟩

theorem EnvWp.insertTup {ρ : FEnv} {b : Nat} {env : VEnv Val} (hE : EnvWp ρ b env) :
    {ts : List Ty} → (xs : Tup Val ts) →
    EnvWp (fupdTup ρ b xs) (b + ts.length) (envInsertTup env b xs)
  | [], () => hE
  | _ :: ts, (x, xs) => by
    simp only [envInsertTup, fupdTup, List.length_cons]
    have h1 := (hE.insert_fresh x).insertTup xs
    rwa [show b + 1 + ts.length = b + (ts.length + 1) by omega] at h1

theorem resolveArg_wp {ρ : FEnv} {b : Nat} {env : VEnv Val} (hE : EnvWp ρ b env)
    {t : Ty} {a : Arg K t} {a' : Arg Val t} (h : resolveArg env a = some a') :
    FKey.FLt b a ∧ a'.val = FKey.fev ρ a := by
  cases a with
  | imm c => cases h; exact ⟨trivial, rfl⟩
  | var lvl =>
    simp only [resolveArg] at h
    cases hfind : env.find? lvl with
    | none => simp [hfind] at h
    | some p =>
      rcases p with ⟨t', v⟩
      simp only [hfind] at h
      cases hcast : castTy t' t v with
      | none => simp [hcast] at h
      | some v' =>
        simp only [hcast, Option.some.injEq] at h
        subst h
        obtain ⟨rfl, rfl⟩ := castTy_some_eq hcast
        obtain ⟨hlt, hev⟩ := hE lvl ⟨t', v⟩ hfind
        exact ⟨hlt, hev.symm⟩

theorem resolveArgs_wp {ρ : FEnv} {b : Nat} {env : VEnv Val} (hE : EnvWp ρ b env) :
    {ts : List Ty} → {args : Tup (Arg K) ts} → {vArgs : Tup (Arg Val) ts} →
    resolveArgs env args = some vArgs →
    TupKeyLt b args ∧ vals vArgs = tupGev ρ args
  | [], (), (), _ => ⟨trivial, rfl⟩
  | _ :: _, (a, as), _, h => by
    simp only [resolveArgs] at h
    cases ha : resolveArg env a with
    | none => simp [ha] at h
    | some a' =>
      cases has : resolveArgs env as with
      | none => simp [ha, has] at h
      | some as' =>
        simp only [ha, has, Option.some.injEq] at h
        subst h
        obtain ⟨hlt1, hv1⟩ := resolveArg_wp hE ha
        obtain ⟨hlt2, hv2⟩ := resolveArgs_wp hE has
        exact ⟨⟨hlt1, hlt2⟩, Prod.ext hv1 hv2⟩

theorem emitHoists_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {G : Ctx (GVal Val) Val}
    (cont : Nat → VEnv Val → GvnTbl Val → Expr Val Cont rs) :
    ∀ (hoists : List HoistOp) (b : Nat) (ρ : FEnv) (env : VEnv Val) (tbl : GvnTbl Val),
      GoodG ρ b G → EnvWp ρ b env → GoodT ρ b tbl →
      (∀ b' ρ' env' tbl', GoodG ρ' b' G → EnvWp ρ' b' env' → GoodT ρ' b' tbl' →
        wp Γ Q X (cont b' env' tbl') m) →
      wp Γ Q X (emitHoists hoists b env tbl cont) m
  | [], b, ρ, env, tbl, hG, hE, hT, hcont => hcont b ρ env tbl hG hE hT
  | h :: rest, b, ρ, env, tbl, hG, hE, hT, hcont => by
    simp only [emitHoists]
    cases hp : h.code.isLicmPure with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact emitHoists_wp cont rest b ρ env tbl hG hE hT hcont
    | true =>
      simp only [↓reduceIte]
      cases hfind : tbl.find h.sig h.ts h.code h.args with
      | some _ => exact emitHoists_wp cont rest b ρ env tbl hG hE hT hcont
      | none =>
        cases hres : resolveArgs env h.args with
        | none => exact emitHoists_wp cont rest b ρ env tbl hG hE hT hcont
        | some vArgs =>
          obtain ⟨hlt, hvals⟩ := resolveArgs_wp hE hres
          obtain ⟨r, hr⟩ := OpCode.isLicmPure_spec h.code hp (vals vArgs)
          simp only [wp, Op.wp]
          apply (hr _).2
          have hT' : GoodT (fupdTup ρ b r) (b + h.ts.length)
              (tbl.insert h.sig h.ts h.code h.args (freshGVals h.ts r b)) := by
            refine (hT.upd_all r).insert ⟨hlt.mono (Nat.le_add_right _ _),
              TupGValGood.freshGVals ρ r b, fun P hP => ?_⟩
            dsimp only at hP ⊢
            rw [tupGev_fupdTup ρ r hlt, ← hvals] at hP
            rw [gvalVals_freshGVals]
            exact (hr P).1 hP
          exact emitHoists_wp cont rest (b + h.ts.length) (fupdTup ρ b r)
            (envInsertTup env b r) _ (hG.upd_all r) (hE.insertTup r) hT' hcont

/-! ## `licmSweep_wp` via `Wf.induct` -/

/-- Positional projection of `HoistBlocks` at block index `i`. -/
def HoistBlocks.get {sig : List (List Ty)} {ts : List Ty} :
    HoistBlocks → Member ts sig → HoistPlan
  | .nil, _ => .leaf
  | .cons ph _, .here => ph
  | .cons _ pt, .there i => pt.get i

theorem licmSweepB_get_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (b : Nat) (env : VEnv V) (tbl : GvnTbl V) :
    {sig : List (List Ty)} → (bsPlan : HoistBlocks) → (bs : Blocks (GVal V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
      (licmSweepB b env tbl bsPlan bs).get i xs =
        licmSweep (b + ts.length) (envInsertTup env b xs) tbl (bsPlan.get i)
          (bs.get i (freshGVals ts xs b))
  | _ :: _, .nil, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .nil, .cons _ bs, _, .there i, xs => licmSweepB_get_eq b env tbl .nil bs i xs
  | _ :: _, .cons _ pt, .cons _ bs, _, .there i, xs => licmSweepB_get_eq b env tbl pt bs i xs

/-- Weakest-precondition preservation for `licmSweep` under any untrusted `HoistPlan`. -/
theorem licmSweep_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (GVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (GVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ b ρ env tbl plan, GoodG ρ b G → EnvWp ρ b env → GoodT ρ b tbl →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (licmSweep b env tbl plan e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD b ρ env tbl plan hG hE hT m hw
    simp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      dsimp only [Op.wp] at hw
      unfold licmSweep; dsimp only
      cases hfind : tbl.find sig ts code (tupGKey args₁) with
      | some cached =>
        dsimp only
        have hmem := GvnTbl.find_mem tbl hfind
        obtain ⟨_, hgs, hwp⟩ := hT (gvnHash code (tupGKey args₁)) _ hmem
        dsimp only at hgs hwp
        rw [← hargs.gkey_vals hG] at hw
        exact ih cached (gvalVals cached) hD b ρ env tbl _ (hG.append_tup_gval hgs) hE hT m
          (hwp (fun ys => wp Γ Q X (k₂ ys) m) hw)
      | none =>
        dsimp only [wp, Op.wp]
        rw [hargs.gout_vals hG]
        exact OpCode.wp_mono code (vals args₂) (fun xs hk2 =>
          ih (freshGVals ts xs b) xs hD (b + ts.length) (fupdTup ρ b xs)
            (envInsertTup env b xs) tbl _ (hG.freshGVals xs) (hE.insertTup xs)
            (hT.upd_all xs) m hk2) hw
  | load t ha _ ih =>
    intro hD b ρ env tbl plan hG hE hT m hw
    simp only [wp, licmSweep] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, ha.gout_val hG ▸ hv,
      ih (v, b) v hD (b + 1) (fupd ρ b v) (env.insert b ⟨t, v⟩) tbl _
        (hG.freshOne v) (hE.insert_fresh v)
        (by simpa [fupdTup] using hT.upd_all (ts := [t]) (v, ())) m hk⟩
  | store hv ha _ ih =>
    intro hD b ρ env tbl plan hG hE hT m hw
    simp only [wp, licmSweep] at hw ⊢
    rw [ha.gout_val hG, hv.gout_val hG]
    exact ⟨hw.1, ih hD b ρ env tbl _ hG hE hT _ hw.2⟩
  | call f hargs _ ih =>
    intro hD b ρ env tbl plan hG hE hT m hw
    simp only [wp, licmSweep] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE_ex⟩
    rw [hargs.gout_vals hG]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshGVals _ r b) r hD (b + _) (fupdTup ρ b r) (envInsertTup env b r) tbl _
        (hG.freshGVals r) (hE.insertTup r) (hT.upd_all r) m' (hP r m' hp), hE_ex⟩
  | jnz hc _ _ iht ihe =>
    intro hD b ρ env tbl plan hG hE hT m hw
    simp only [wp, licmSweep] at hw ⊢
    rw [hc.gout_val hG]
    exact ⟨fun h => iht hD b ρ env tbl _ hG hE hT m (hw.1 h),
           fun h => ihe hD b ρ env tbl _ hG hE hT m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD b ρ env tbl plan hG _ _ m hw
    have hj' := hD _ hj; dsimp only at hj'
    simp only [wp, licmSweep] at hw ⊢
    rw [hj', hargs.gout_vals hG]
    exact hw
  | ret hvs =>
    intro _ b ρ env tbl plan hG _ _ m hw
    simp only [wp, licmSweep] at hw ⊢
    rw [hvs.gout_vals hG]
    exact hw
  | exit f hargs =>
    intro _ b ρ env tbl plan hG _ _ m hw
    simp only [wp, licmSweep] at hw ⊢
    rw [hargs.gout_vals hG]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ _ _ _ hw
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD b ρ env tbl plan hG hE hT m hw
    simp only [licmSweep]
    refine emitHoists_wp _ _ b ρ env tbl hG hE hT fun b' ρ' env' tbl' hG' hE' hT' => ?_
    simp only [wp] at hw ⊢
    intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) b' ρ' env' tbl' _ hG' hE' hT' m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb
    exact hclosed i xs m' (by
      rw [licmSweepB_get_eq]
      exact ihb Js Js i (freshGVals ts xs b') xs (tup_zip_self_eq hD Js)
        (b' + ts.length) (fupdTup ρ' b' xs) (envInsertTup env' b' xs) tbl' _
        (hG'.freshGVals xs) (hE'.insertTup xs) (hT'.upd_all xs) m' hb)

/-! ## Relational well-formedness (`EnvRel`, `resolveArgs_rel`, `emitHoists_wf`, `licmSweep_wf`) -/

section
variable {V₁ V₂ : Ty → Type}

/-- Pointwise relational correspondence between two lexical `VEnv` tries under `G'`. -/
def EnvRel (G' : Ctx V₁ V₂) (env₁ : VEnv V₁) (env₂ : VEnv V₂) : Prop :=
  ∀ lvl : Nat, ORel (fun p q => ∃ t v₁ v₂, p = ⟨t, v₁⟩ ∧ q = ⟨t, v₂⟩ ∧ ⟨t, v₁, v₂⟩ ∈ G')
    (env₁.find? lvl) (env₂.find? lvl)

theorem EnvRel.empty {G' : Ctx V₁ V₂} : EnvRel G' .empty .empty := fun _ => trivial

theorem EnvRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {env₁ : VEnv V₁} {env₂ : VEnv V₂} (hE : EnvRel G₁ env₁ env₂) : EnvRel G₂ env₁ env₂ := by
  intro lvl
  have hl := hE lvl
  cases h1 : env₁.find? lvl <;> cases h2 : env₂.find? lvl <;> rw [h1, h2] at hl <;>
    simp only [ORel] at hl ⊢
  rcases hl with ⟨t, v₁, v₂, rfl, rfl, hm⟩
  exact ⟨t, v₁, v₂, rfl, rfl, hsub _ hm⟩

theorem EnvRel.insert {G' : Ctx V₁ V₂} {env₁ : VEnv V₁} {env₂ : VEnv V₂}
    (hE : EnvRel G' env₁ env₂) (b : Nat) {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t}
    (hm : ⟨t, v₁, v₂⟩ ∈ G') : EnvRel G' (env₁.insert b ⟨t, v₁⟩) (env₂.insert b ⟨t, v₂⟩) := by
  intro lvl
  rw [Trie.find?_insert, Trie.find?_insert]
  split
  · exact ⟨t, v₁, v₂, rfl, rfl, hm⟩
  · exact hE lvl

private theorem envRel_insertTup_aux {G' : Ctx V₁ V₂} :
    {ts : List Ty} → {xs₁ : Tup V₁ ts} → {xs₂ : Tup V₂ ts} →
    {env₁ : VEnv V₁} → {env₂ : VEnv V₂} → (b : Nat) →
    (∀ p ∈ Tup.zip xs₁ xs₂, p ∈ G') →
    EnvRel G' env₁ env₂ → EnvRel G' (envInsertTup env₁ b xs₁) (envInsertTup env₂ b xs₂)
  | [], (), (), _, _, _, _, hE => hE
  | _ :: _, (_, _), (_, _), _, _, b, hsub, hE =>
    envRel_insertTup_aux (b + 1) (fun _ hp => hsub _ (List.mem_cons_of_mem _ hp))
      (hE.insert b (hsub _ List.mem_cons_self))

theorem EnvRel.insertTup {G' : Ctx V₁ V₂} {env₁ : VEnv V₁} {env₂ : VEnv V₂}
    (hE : EnvRel G' env₁ env₂) {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    EnvRel (Tup.zip xs₁ xs₂ ++ G') (envInsertTup env₁ b xs₁) (envInsertTup env₂ b xs₂) :=
  envRel_insertTup_aux b (fun _ hp => List.mem_append_left G' hp)
    (hE.weaken fun _ hp => List.mem_append_right _ hp)

theorem resolveArg_rel {G' : Ctx V₁ V₂} {env₁ : VEnv V₁} {env₂ : VEnv V₂}
    (hE : EnvRel G' env₁ env₂) {t : Ty} (a : Arg K t) :
    ORel (ArgRel G' t) (resolveArg env₁ a) (resolveArg env₂ a) := by
  cases a with
  | imm c => exact .imm c
  | var lvl =>
    have hl := hE lvl
    simp only [resolveArg]
    cases e₁ : env₁.find? lvl <;> cases e₂ : env₂.find? lvl <;> rw [e₁, e₂] at hl <;>
      simp only [ORel] at hl ⊢
    rcases hl with ⟨t', v₁, v₂, rfl, rfl, hm⟩
    have hc := castTy_rel (t := t) hm
    cases c₁ : castTy t' t v₁ <;> cases c₂ : castTy t' t v₂ <;> rw [c₁, c₂] at hc <;>
      simp only [ORel] at hc ⊢
    exact .var hc

theorem resolveArgs_rel {G' : Ctx V₁ V₂} {env₁ : VEnv V₁} {env₂ : VEnv V₂}
    (hE : EnvRel G' env₁ env₂) :
    {ts : List Ty} → (args : Tup (Arg K) ts) →
    ORel (TRel (ArgRel G')) (resolveArgs env₁ args) (resolveArgs env₂ args)
  | [], () => .nil
  | _ :: _, (a, as) => by
    have ha := resolveArg_rel hE a
    have has := resolveArgs_rel hE as
    simp only [resolveArgs]
    cases e₁ : resolveArg env₁ a <;> cases e₂ : resolveArg env₂ a <;> rw [e₁, e₂] at ha <;>
      simp only [ORel] at ha ⊢ <;>
      cases f₁ : resolveArgs env₁ as <;> cases f₂ : resolveArgs env₂ as <;> rw [f₁, f₂] at has <;>
      simp only [ORel] at has ⊢
    exact .cons ha has

theorem emitHoists_wf {L₁ L₂ : List Ty → Type} {rs : List Ty} {D : Ctx L₁ L₂}
    {G : Ctx (GVal V₁) (GVal V₂)}
    (cont₁ : Nat → VEnv V₁ → GvnTbl V₁ → Expr V₁ L₁ rs)
    (cont₂ : Nat → VEnv V₂ → GvnTbl V₂ → Expr V₂ L₂ rs) :
    ∀ (hoists : List HoistOp) (b : Nat) {G' : Ctx V₁ V₂}
      (env₁ : VEnv V₁) (env₂ : VEnv V₂) (tbl₁ : GvnTbl V₁) (tbl₂ : GvnTbl V₂),
      RelG G' G → EnvRel G' env₁ env₂ → RelT G' tbl₁ tbl₂ →
      (∀ b' {G'' : Ctx V₁ V₂} env₁' env₂' tbl₁' tbl₂',
        RelG G'' G → EnvRel G'' env₁' env₂' → RelT G'' tbl₁' tbl₂' →
        Wf G'' D (cont₁ b' env₁' tbl₁') (cont₂ b' env₂' tbl₂')) →
      Wf G' D (emitHoists hoists b env₁ tbl₁ cont₁) (emitHoists hoists b env₂ tbl₂ cont₂)
  | [], b, _, env₁, env₂, tbl₁, tbl₂, hG, hE, hT, hcont => hcont b env₁ env₂ tbl₁ tbl₂ hG hE hT
  | h :: rest, b, G', env₁, env₂, tbl₁, tbl₂, hG, hE, hT, hcont => by
    simp only [emitHoists]
    cases h.code.isLicmPure with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact emitHoists_wf cont₁ cont₂ rest b env₁ env₂ tbl₁ tbl₂ hG hE hT hcont
    | true =>
      simp only [↓reduceIte]
      have hfind := hT.find_rel h.sig h.ts h.code h.args
      generalize hfl1 : tbl₁.find h.sig h.ts h.code h.args = r₁ at hfind
      generalize hfl2 : tbl₂.find h.sig h.ts h.code h.args = r₂ at hfind
      cases hfind with
      | some _ => exact emitHoists_wf cont₁ cont₂ rest b env₁ env₂ tbl₁ tbl₂ hG hE hT hcont
      | none =>
        have hres := resolveArgs_rel hE h.args
        cases e₁ : resolveArgs env₁ h.args <;> cases e₂ : resolveArgs env₂ h.args <;>
          rw [e₁, e₂] at hres <;> simp only [ORel] at hres ⊢
        · exact emitHoists_wf cont₁ cont₂ rest b env₁ env₂ tbl₁ tbl₂ hG hE hT hcont
        · refine .let_ (.mk h.code hres) fun xs₁ xs₂ => ?_
          have hsub : ∀ p ∈ G', p ∈ Tup.zip xs₁ xs₂ ++ G' := fun _ hq => List.mem_append_right _ hq
          exact emitHoists_wf cont₁ cont₂ rest (b + h.ts.length)
            (envInsertTup env₁ b xs₁) (envInsertTup env₂ b xs₂) _ _
            (hG.weaken hsub) (hE.insertTup xs₁ xs₂ b)
            ((hT.weaken hsub).insert (TRel.freshGVals_rel xs₁ xs₂ b)) hcont

end

/-- Relational well-formedness preservation for `licmSweep` under any untrusted `HoistPlan`. -/
theorem licmSweep_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (GVal V₁) (GVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (GVal V₁) L₁ rs} {e₂ : Expr (GVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, RelG G' G →
      ∀ b env₁ env₂ tbl₁ tbl₂ plan, EnvRel G' env₁ env₂ → RelT G' tbl₁ tbl₂ →
        Wf G' D (licmSweep b env₁ tbl₁ plan e₁) (licmSweep b env₂ tbl₂ plan e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG b env₁ env₂ tbl₁ tbl₂ plan hE hT
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hkey : tupGKey args₁ = tupGKey args₂ := TRel.gkey_eq hG hargs
      have hfind := hT.find_rel sig ts code (tupGKey args₂)
      unfold licmSweep; dsimp only
      rw [hkey]
      generalize hfl1 : tbl₁.find sig ts code (tupGKey args₂) = r₁ at hfind
      generalize hfl2 : tbl₂.find sig ts code (tupGKey args₂) = r₂ at hfind
      cases hfind with
      | some hr => exact ih _ _ (hG.append_tup hr) b env₁ env₂ tbl₁ tbl₂ _ hE hT
      | none =>
        refine .let_ (.mk code (TRel.gout hG hargs)) fun xs₁ xs₂ => ?_
        have hsub : ∀ p ∈ G', p ∈ Tup.zip xs₁ xs₂ ++ G' := fun _ hq => List.mem_append_right _ hq
        exact ih _ _ (hG.freshGVals xs₁ xs₂ b) (b + ts.length)
          (envInsertTup env₁ b xs₁) (envInsertTup env₂ b xs₂) tbl₁ tbl₂ _
          (hE.insertTup xs₁ xs₂ b) (hT.weaken hsub)
  | load t ha _ ih =>
    intro G' hG b env₁ env₂ tbl₁ tbl₂ plan hE hT
    refine .load t (ha.gout hG) fun v₁ v₂ => ?_
    have hsub : ∀ p ∈ G', p ∈ (⟨t, v₁, v₂⟩ :: G') := fun _ hq => List.mem_cons_of_mem _ hq
    exact ih _ _ (hG.freshOne v₁ v₂ b) (b + 1) (env₁.insert b ⟨t, v₁⟩) (env₂.insert b ⟨t, v₂⟩)
      tbl₁ tbl₂ _ ((hE.weaken hsub).insert b List.mem_cons_self) (hT.weaken hsub)
  | store hv ha _ ih =>
    intro G' hG b env₁ env₂ tbl₁ tbl₂ plan hE hT
    exact .store (hv.gout hG) (ha.gout hG) (ih hG b env₁ env₂ tbl₁ tbl₂ _ hE hT)
  | call f hargs _ ih =>
    intro G' hG b env₁ env₂ tbl₁ tbl₂ plan hE hT
    refine .call f (TRel.gout hG hargs) fun xs₁ xs₂ => ?_
    have hsub : ∀ p ∈ G', p ∈ Tup.zip xs₁ xs₂ ++ G' := fun _ hq => List.mem_append_right _ hq
    exact ih _ _ (hG.freshGVals xs₁ xs₂ b) (b + _) (envInsertTup env₁ b xs₁)
      (envInsertTup env₂ b xs₂) tbl₁ tbl₂ _ (hE.insertTup xs₁ xs₂ b) (hT.weaken hsub)
  | jnz hc _ _ iht ihe =>
    intro G' hG b env₁ env₂ tbl₁ tbl₂ plan hE hT
    exact .jnz (hc.gout hG) (iht hG b env₁ env₂ tbl₁ tbl₂ _ hE hT)
      (ihe hG b env₁ env₂ tbl₁ tbl₂ _ hE hT)
  | jump hj hargs =>
    intro G' hG _ _ _ _ _ _ _ _
    exact .jump hj (TRel.gout hG hargs)
  | ret hvs =>
    intro G' hG _ _ _ _ _ _ _ _
    exact .ret (TRel.gout hG hvs)
  | exit f hargs =>
    intro G' hG _ _ _ _ _ _ _ _
    exact .exit f (TRel.gout hG hargs)
  | hlt =>
    intro _ _ _ _ _ _ _ _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hG b env₁ env₂ tbl₁ tbl₂ plan hE hT
    simp only [licmSweep]
    refine emitHoists_wf _ _ _ b env₁ env₂ tbl₁ tbl₂ hG hE hT
      fun b' G'' env₁' env₂' tbl₁' tbl₂' hG' hE' hT' => ?_
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hG' b' env₁' env₂' tbl₁' tbl₂' _ hE' hT')
    rw [licmSweepB_get_eq, licmSweepB_get_eq]
    have hsub : ∀ p ∈ G'', p ∈ Tup.zip xs₁ xs₂ ++ G'' := fun _ hq => List.mem_append_right _ hq
    exact ihb Js₁ Js₂ i _ _ (hG'.freshGVals xs₁ xs₂ b') (b' + _)
      (envInsertTup env₁' b' xs₁) (envInsertTup env₂' b' xs₂) tbl₁' tbl₂' _
      (hE'.insertTup xs₁ xs₂ b') (hT'.weaken hsub)

/-! ## `supportsSource` preservation (`Func.licm_supportsSource`) -/

/-- Check that a hoisted op's `OpCode` is supported by `target`. -/
def HoistOp.supports (target : LegalTarget) (h : HoistOp) : Bool :=
  target.supportsOpCode h.code

mutual
/-- Check that every hoisted op in `HoistPlan` is supported by `target`. -/
def HoistPlan.supports (target : LegalTarget) : HoistPlan → Bool
  | .leaf => true
  | .node1 k => k.supports target
  | .node2 t e => t.supports target && e.supports target
  | .groupNode hs bs k =>
    hs.all (HoistOp.supports target) && bs.supports target && k.supports target

/-- Block-list companion of `HoistPlan.supports`. -/
def HoistBlocks.supports (target : LegalTarget) : HoistBlocks → Bool
  | .nil => true
  | .cons h t => h.supports target && t.supports target
end

private theorem HoistBlocks.supports_get {target : LegalTarget} :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : HoistBlocks) → (i : Member ts sig) →
    bs.supports target = true → (bs.get i).supports target = true
  | _ :: _, _, .nil, _, _ => rfl
  | _ :: _, _, .cons _ _, .here, h => (Bool.and_eq_true _ _ ▸ h).1
  | _ :: _, _, .cons _ pt, .there i, h =>
    HoistBlocks.supports_get pt i (Bool.and_eq_true _ _ ▸ h).2

mutual
private theorem scanTFlat_supports (target : LegalTarget) {rs : List Ty} :
    (tf : TFlat rs) → (senv : List (Option Nat)) → (rt : Licm.ReachTree) → (st : Licm.ScanState) →
    tf.supportsSource target = true →
    st.hoistsRev.all (HoistOp.supports target) = true →
    (Licm.scanTFlat senv rt tf st).hoistsRev.all (HoistOp.supports target) = true
  | .let_ op k, senv, rt, st, hsupp, hacc => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    unfold Licm.scanTFlat
    cases rt <;> dsimp only <;>
    · split
      · split
        · split
          · exact scanTFlat_supports target k _ _ st hsupp.2 hacc
          · split
            · refine scanTFlat_supports target k _ _ _ hsupp.2 ?_
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨hsupp.1, hacc⟩
            · exact scanTFlat_supports target k _ _ st hsupp.2 hacc
        · exact scanTFlat_supports target k _ _ st hsupp.2 hacc
      · exact scanTFlat_supports target k _ _ st hsupp.2 hacc
  | .load _ _ k, senv, rt, st, hsupp, hacc => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact scanTFlat_supports target k _ _ st hsupp.2 hacc
  | .store _ _ k, senv, rt, st, hsupp, hacc => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact scanTFlat_supports target k _ _ st hsupp.2 hacc
  | .call _ _ _ k, senv, rt, st, hsupp, hacc => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact scanTFlat_supports target k _ _ st hsupp.2 hacc
  | .jnz _ t e, senv, rt, st, hsupp, hacc => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.scanTFlat]
    exact scanTFlat_supports target e senv _ _ hsupp.2
      (scanTFlat_supports target t senv _ st hsupp.1 hacc)
  | .jump _ _, _, _, _, _, hacc | .ret _, _, _, _, _, hacc
  | .exit _ _, _, _, _, _, hacc | .hlt, _, _, _, _, hacc => hacc
  | .group bodies k, senv, rt, st, hsupp, hacc => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.scanTFlat]
    exact scanTFlat_supports target k senv _ _ hsupp.2
      (scanTBlocksAll_supports target bodies senv _ st hsupp.1.2 hacc)

private theorem scanTBlocksAll_supports (target : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (senv : List (Option Nat)) →
    (rbs : Licm.ReachBlocks) → (st : Licm.ScanState) →
    tb.supportsSource target = true →
    st.hoistsRev.all (HoistOp.supports target) = true →
    (Licm.scanTBlocksAll senv rbs tb st).hoistsRev.all (HoistOp.supports target) = true
  | _, .nil, _, _, _, _, hacc => hacc
  | _ :: _, .cons b bs, senv, rbs, st, hsupp, hacc => by
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.scanTBlocksAll]
    exact scanTBlocksAll_supports target bs senv _ _ hsupp.2
      (scanTFlat_supports target b _ _ st hsupp.1.2 hacc)
end

private theorem scanLoopBlocks_supports (target : LegalTarget) (loopMask : List Nat)
    {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (senv : List (Option Nat)) →
    (rbs : Licm.ReachBlocks) → (st : Licm.ScanState) →
    tb.supportsSource target = true →
    st.hoistsRev.all (HoistOp.supports target) = true →
    (Licm.scanLoopBlocks loopMask senv rbs tb st).hoistsRev.all (HoistOp.supports target) = true
  | [], .nil, _, _, _, _, hacc => hacc
  | _ :: _, .cons b bs, senv, rbs, st, hsupp, hacc => by
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hsupp
    unfold Licm.scanLoopBlocks; dsimp only
    refine scanLoopBlocks_supports target loopMask bs senv _ _ hsupp.2 ?_
    split
    · exact scanTFlat_supports target b _ _ st hsupp.1.2 hacc
    · exact hacc

mutual
private theorem analyzeTFlat_supports (target : LegalTarget) {rs : List Ty} :
    (tf : TFlat rs) → (next : Nat) → (env : List Nat) → (tbl : Licm.PlanTbl) →
    tf.supportsSource target = true →
    (Licm.analyzeTFlat next env tbl tf).supports target = true
  | .let_ _ k, next, env, tbl, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.analyzeTFlat]
    split <;> exact analyzeTFlat_supports target k _ _ tbl hsupp.2
  | .load _ _ k, next, env, tbl, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact analyzeTFlat_supports target k _ _ tbl hsupp.2
  | .store _ _ k, next, env, tbl, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact analyzeTFlat_supports target k _ _ tbl hsupp.2
  | .call _ _ _ k, next, env, tbl, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    exact analyzeTFlat_supports target k _ _ tbl hsupp.2
  | .jnz _ t e, next, env, tbl, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.analyzeTFlat, HoistPlan.supports, Bool.and_eq_true]
    exact ⟨analyzeTFlat_supports target t next env tbl hsupp.1,
           analyzeTFlat_supports target e next env tbl hsupp.2⟩
  | .jump _ _, _, _, _, _ | .ret _, _, _, _, _ | .exit _ _, _, _, _, _ | .hlt, _, _, _, _ => rfl
  | .group bodies k, next, env, tbl, hsupp => by
    simp only [TFlat.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.analyzeTFlat]
    split
    · simp only [HoistPlan.supports, List.all_nil, Bool.true_and, Bool.and_eq_true]
      exact ⟨analyzeTBlocks_supports target bodies next env tbl hsupp.1.2,
             analyzeTFlat_supports target k next env tbl hsupp.2⟩
    · simp only [HoistPlan.supports, Bool.and_eq_true]
      have hhs := scanLoopBlocks_supports target (Licm.computeLoopMask bodies) bodies
        (env.map some) (Licm.buildReachB (Licm.computeLoopMask bodies) bodies).2
        ⟨next, tbl, []⟩ hsupp.1.2 rfl
      refine ⟨⟨?_, analyzeTBlocks_supports target bodies _ env _ hsupp.1.2⟩,
        analyzeTFlat_supports target k _ env _ hsupp.2⟩
      simpa [List.all_reverse] using hhs

private theorem analyzeTBlocks_supports (target : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) → (next : Nat) → (env : List Nat) →
    (tbl : Licm.PlanTbl) → tb.supportsSource target = true →
    (Licm.analyzeTBlocks next env tbl tb).supports target = true
  | _, .nil, _, _, _, _ => rfl
  | _, .cons b bs, next, env, tbl, hsupp => by
    simp only [TBlocks.supportsSource, Bool.and_eq_true] at hsupp
    simp only [Licm.analyzeTBlocks, HoistBlocks.supports, Bool.and_eq_true]
    exact ⟨analyzeTFlat_supports target b _ _ tbl hsupp.1.2,
           analyzeTBlocks_supports target bs next env tbl hsupp.2⟩
end

private theorem emitHoists_supportsSource (target : LegalTarget) {rs : List Ty}
    (cont : Nat → VEnv K → GvnTbl K → Expr K KL rs) :
    ∀ (hoists : List HoistOp) (b nv nl : Nat) (env : VEnv K) (tbl : GvnTbl K),
      hoists.all (HoistOp.supports target) = true →
      (∀ b' nv' env' tbl', (toTFlat (cont b' env' tbl') nv' nl).supportsSource target = true) →
      (toTFlat (emitHoists hoists b env tbl cont) nv nl).supportsSource target = true
  | [], b, nv, _, env, tbl, _, hcont => hcont b nv env tbl
  | h :: rest, b, nv, nl, env, tbl, hhs, hcont => by
    simp only [List.all_cons, Bool.and_eq_true] at hhs
    simp only [emitHoists]
    cases h.code.isLicmPure with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact emitHoists_supportsSource target cont rest b nv nl env tbl hhs.2 hcont
    | true =>
      simp only [↓reduceIte]
      cases tbl.find h.sig h.ts h.code h.args with
      | some _ =>
        exact emitHoists_supportsSource target cont rest b nv nl env tbl hhs.2 hcont
      | none =>
        cases resolveArgs env h.args with
        | none =>
          exact emitHoists_supportsSource target cont rest b nv nl env tbl hhs.2 hcont
        | some _ =>
          simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
          exact ⟨hhs.1,
            emitHoists_supportsSource target cont rest (b + h.ts.length) (nv + h.ts.length) nl
              _ _ hhs.2 hcont⟩

private theorem toTBlocks_supportsSource_get (target : LegalTarget) {rs : List Ty} (nv nl : Nat) :
    {sig : List (List Ty)} → (bs : Blocks K KL rs sig) →
    (toTBlocks bs nv nl).supportsSource target = true →
    ∀ {ts : List Ty} (i : Member ts sig),
      (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true
  | _ :: _, .cons _ _, h, _, .here => by
    simp only [toTBlocks, TBlocks.supportsSource, Bool.and_eq_true] at h; exact h.1.2
  | _ :: _, .cons _ bs, h, _, .there i => by
    simp only [toTBlocks, TBlocks.supportsSource, Bool.and_eq_true] at h
    exact toTBlocks_supportsSource_get target nv nl bs h.2 i

private theorem toTBlocks_supportsSource_of_get (target : LegalTarget) {rs : List Ty}
    (nv nl : Nat) :
    {sig : List (List Ty)} → (bs : Blocks K KL rs sig) →
    sig.all (·.all target.supportsTy) = true →
    (∀ {ts : List Ty} (i : Member ts sig),
      (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true) →
    (toTBlocks bs nv nl).supportsSource target = true
  | [], .nil, _, _ => rfl
  | _ :: _, .cons _ bs, hsig, hget => by
    simp only [List.all_cons, Bool.and_eq_true] at hsig
    simp only [toTBlocks, TBlocks.supportsSource, Bool.and_eq_true]
    exact ⟨⟨hsig.1, hget .here⟩,
      toTBlocks_supportsSource_of_get target nv nl bs hsig.2 fun i => hget (.there i)⟩

private theorem licmSweep_supportsSource (target : LegalTarget) {rs : List Ty}
    {G : Ctx K (GVal K)} {D : Ctx KL KL}
    {e₁ : Expr K KL rs} {e₂ : Expr (GVal K) KL rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b env tbl plan nv₁ nl₁ nv₂ nl₂,
      (toTFlat e₁ nv₁ nl₁).supportsSource target = true →
      plan.supports target = true →
      (toTFlat (licmSweep b env tbl plan e₂) nv₂ nl₂).supportsSource target = true := by
  induction hwf using Wf.induct with
  | @let_ _ _ ts op₁ op₂ _ _ hop _ ih =>
    intro b env tbl plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    cases hop with
    | mk code _ =>
      simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true] at hsupp
      have hp' : (match plan with | .node1 p => p | _ => .leaf).supports target = true := by
        cases plan <;> simp [HoistPlan.supports] at hplan ⊢; exact hplan
      unfold licmSweep; dsimp only
      cases tbl.find _ ts code (tupGKey _) with
      | some cached =>
        exact ih (Tup.levels ts nv₁) cached b env tbl _ (nv₁ + ts.length) nl₁ nv₂ nl₂ hsupp.2 hp'
      | none =>
        simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
        exact ⟨hsupp.1,
          ih (Tup.levels ts nv₁) (freshGVals ts (Tup.levels ts nv₂) b)
            (b + ts.length) _ tbl _ (nv₁ + ts.length) nl₁ (nv₂ + ts.length) nl₂ hsupp.2 hp'⟩
  | load t _ _ ih =>
    intro b env tbl plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true] at hsupp
    have hp' : (match plan with | .node1 p => p | _ => .leaf).supports target = true := by
      cases plan <;> simp [HoistPlan.supports] at hplan ⊢; exact hplan
    simp only [licmSweep, toTFlat, TFlat.supportsSource, Bool.and_eq_true]
    exact ⟨hsupp.1, ih nv₁ (nv₂, b) (b + 1) _ tbl _ (nv₁ + 1) nl₁ (nv₂ + 1) nl₂ hsupp.2 hp'⟩
  | store _ _ _ ih =>
    intro b env tbl plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true] at hsupp
    have hp' : (match plan with | .node1 p => p | _ => .leaf).supports target = true := by
      cases plan <;> simp [HoistPlan.supports] at hplan ⊢; exact hplan
    simp only [licmSweep, toTFlat, TFlat.supportsSource, Bool.and_eq_true]
    exact ⟨hsupp.1, ih b env tbl _ nv₁ nl₁ nv₂ nl₂ hsupp.2 hp'⟩
  | call f _ _ ih =>
    intro b env tbl plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true] at hsupp
    have hp' : (match plan with | .node1 p => p | _ => .leaf).supports target = true := by
      cases plan <;> simp [HoistPlan.supports] at hplan ⊢; exact hplan
    simp only [licmSweep, toTFlat, TFlat.supportsSource, Bool.and_eq_true]
    exact ⟨hsupp.1,
      ih (Tup.levels _ nv₁) (freshGVals _ (Tup.levels _ nv₂) b) (b + _) _ tbl _
        (nv₁ + _) nl₁ (nv₂ + _) nl₂ hsupp.2 hp'⟩
  | jnz _ _ _ iht ihe =>
    intro b env tbl plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true] at hsupp
    have hp2 :
        let p := match plan with | .node2 pt pe => (pt, pe) | _ => (.leaf, .leaf)
        p.1.supports target = true ∧ p.2.supports target = true := by
      cases plan <;> simp only [HoistPlan.supports, Bool.and_eq_true] at hplan ⊢
      · exact ⟨trivial, trivial⟩
      · exact ⟨trivial, trivial⟩
      · exact hplan
      · exact ⟨trivial, trivial⟩
    dsimp only [licmSweep, toTFlat, TFlat.supportsSource]
    rw [Bool.and_eq_true]
    exact ⟨iht b env tbl _ nv₁ nl₁ nv₂ nl₂ hsupp.1 hp2.1,
           ihe b env tbl _ nv₁ nl₁ nv₂ nl₂ hsupp.2 hp2.2⟩
  | jump _ _ =>
    intro _ _ _ _ _ _ _ _ hsupp _; exact hsupp
  | ret _ =>
    intro _ _ _ _ _ _ _ _ hsupp _; exact hsupp
  | exit _ _ =>
    intro _ _ _ _ _ _ _ _ hsupp _; exact hsupp
  | hlt =>
    intro _ _ _ _ _ _ _ _ _ _; rfl
  | @group _ _ sig b₁ b₂ _ _ _ _ ihb ihk =>
    intro b env tbl plan nv₁ nl₁ nv₂ nl₂ hsupp hplan
    simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true] at hsupp
    have hpg :
        let p := match plan with | .groupNode hs bsP kP => (hs, bsP, kP) | _ => ([], .nil, .leaf)
        p.1.all (HoistOp.supports target) = true ∧ p.2.1.supports target = true ∧
          p.2.2.supports target = true := by
      cases plan <;> simp only [HoistPlan.supports, Bool.and_eq_true] at hplan ⊢
      · exact ⟨rfl, rfl, trivial⟩
      · exact ⟨rfl, rfl, trivial⟩
      · exact ⟨rfl, rfl, trivial⟩
      · exact ⟨hplan.1.1, hplan.1.2, hplan.2⟩
    dsimp only [licmSweep]
    refine emitHoists_supportsSource target _ _ b nv₂ nl₂ env tbl hpg.1 fun b' nv' env' tbl' => ?_
    simp only [toTFlat, TFlat.supportsSource, Bool.and_eq_true]
    refine ⟨⟨hsupp.1.1, toTBlocks_supportsSource_of_get target nv' (nl₂ + sig.length) _ hsupp.1.1
      fun {ts} i => ?_⟩,
      ihk (Tup.levels sig nl₁) (Tup.levels sig nl₂) b' env' tbl' _ nv₁ (nl₁ + sig.length)
        nv' (nl₂ + sig.length) hsupp.2 hpg.2.2⟩
    rw [licmSweepB_get_eq]
    exact ihb (Tup.levels sig nl₁) (Tup.levels sig nl₂) i
      (Tup.levels ts nv₁) (freshGVals ts (Tup.levels ts nv') b')
      (b' + ts.length) (envInsertTup env' b' (Tup.levels ts nv')) tbl' _
      (nv₁ + ts.length) (nl₁ + sig.length) (nv' + ts.length) (nl₂ + sig.length)
      (toTBlocks_supportsSource_get target nv₁ (nl₁ + sig.length) (b₁ (Tup.levels sig nl₁))
        hsupp.1.2 i)
      (HoistBlocks.supports_get _ i hpg.2.1)

/-! ## Closed-function theorems (`Func.licm_*`, `Fn.licm_*`) -/

/-- `Func.licm` preserves relational well-formedness. -/
theorem Func.licm_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.licm f).Wf := by
  unfold Func.licm; dsimp only
  split
  · intro V₁ V₂ L₁ L₂ xs₁ xs₂
    have hwf := hf (GVal V₁) (GVal V₂) L₁ L₂ (freshGVals as xs₁ 0) (freshGVals as xs₂ 0)
    have hrel : RelG (Tup.zip xs₁ xs₂)
        (Tup.zip (freshGVals as xs₁ 0) (freshGVals as xs₂ 0)) := by
      simpa using RelG.freshGVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
    have hE : EnvRel (Tup.zip xs₁ xs₂) (envInsertTup .empty 0 xs₁) (envInsertTup .empty 0 xs₂) := by
      simpa using EnvRel.insertTup (G' := []) EnvRel.empty xs₁ xs₂ 0
    exact licmSweep_wf hwf hrel as.length _ _ .empty .empty _ hE RelT.empty
  · exact hf

/-- `Func.licm` refines function contracts: any source contract holds on `Func.licm f`. -/
theorem Func.licm_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.licm f) xs m Q X := by
  unfold Func.licm; dsimp only
  split
  · have hwf := hf (GVal Val) Val Cont Cont (freshGVals as xs 0) xs
    let ρ0 : FEnv := fun _ _ => default
    have hgood : GoodG (fupdTup ρ0 0 xs) as.length (Tup.zip (freshGVals as xs 0) xs) := by
      simpa using GoodG.freshGVals (ρ := ρ0) (b := 0) (G := []) (fun _ hp => nomatch hp) xs
    have hE : EnvWp (fupdTup ρ0 0 xs) as.length (envInsertTup .empty 0 xs) := by
      simpa using EnvWp.insertTup (EnvWp.empty ρ0 0) xs
    exact licmSweep_wp hwf (fun _ hp => nomatch hp) as.length _ _ .empty _ hgood hE
      (GoodT.empty _ _) m h
  · exact h

/-- `Func.licm` preserves `Func.supportsSource target` for any `LegalTarget` and well-formed `f`. -/
theorem Func.licm_supportsSource (target : LegalTarget) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) (hsupp : f.supportsSource target = true) :
    (Func.licm f).supportsSource target = true := by
  unfold Func.licm; dsimp only
  split
  · simp only [Func.supportsSource, Bool.and_eq_true] at hsupp ⊢
    refine ⟨hsupp.1, ?_⟩
    have hplan : (Licm.buildHoistPlan as.length (reifyFunc f)).supports target = true :=
      analyzeTFlat_supports target (reifyFunc f) as.length (Licm.pushLevels as.length 0 [])
        .empty hsupp.2
    exact licmSweep_supportsSource target
      (hf K (GVal K) KL KL (Tup.levels as 0) (freshGVals as (Tup.levels as 0) 0))
      as.length (envInsertTup .empty 0 (Tup.levels as 0)) .empty _ as.length 0 as.length 0
      hsupp.2 hplan
  · exact hsupp

/-- `Fn.licm` preserves relational well-formedness. -/
theorem Fn.licm_wf {fn : Fn} (hf : fn.Wf) : (Fn.licm fn).Wf :=
  Func.licm_wf hf

/-- `Fn.licm` refines function contracts. -/
theorem Fn.licm_spec {fn : Fn} (hf : fn.Wf) {Γ : Env}
    {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) : Func.spec Γ (Fn.licm fn).body xs m Q X :=
  Func.licm_spec hf h

end LeanQbe.T
