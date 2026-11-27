module

public import LeanQbe.T.OptFlatLoop
import LeanQbe.T.FlatDirectLemmas
import LeanQbe.T.PassFlatKit
import LeanQbe.T.OptFlatSimKit
import LeanQbe.T.LicmLemmas
import LeanQbe.T.LicmRoLemmas

/-!
# LICM Equivalence Proofs for `OptFlatLoop` (`licmFlat_eq`)

Proves exact `=` correspondence (`std3` axioms only) between native `TFlat`
`OptFlatLoop.licmPureFlat` / `OptFlatLoop.licmFlat` and `Func.licmPure` / `Func.licm`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T
namespace OptFlatLoop

open OptFlatPlanKit
open OptFlatSimKit

/-! ## 1. Pure-Total LICM Equivalence (`licmPureFlat_eq`) -/

private theorem emitHoistsFlat_eq {rs : List Ty} :
    (hs : List HoistOp) → (next : Nat) → (env : VEnv K) → (tbl : GvnTbl K) →
    (outD lD : Nat) →
    (cont : Nat → VEnv K → GvnTbl K → Expr K KL rs) →
    (contFlat : Nat → VEnv K → GvnTbl K → Nat → TFlat rs) →
    (let r : HoistEmitRes rs := emitHoistsFlat hs next env tbl outD;
      toTFlat (cont r.next r.env r.tbl) r.outDepth lD =
        contFlat r.next r.env r.tbl r.outDepth) →
    toTFlat (emitHoists hs next env tbl cont) outD lD =
      let r : HoistEmitRes rs := emitHoistsFlat hs next env tbl outD
      r.wrap (contFlat r.next r.env r.tbl r.outDepth)
  | [], _, _, _, _, _, _, _, hcont => hcont
  | h :: rest, next, env, tbl, outD, lD, cont, contFlat, hcont => by
    dsimp only [emitHoists, emitHoistsFlat]
    dsimp only [emitHoistsFlat] at hcont
    cases hp : h.code.isLicmPure
    · simp only [hp] at hcont
      simpa [hp] using emitHoistsFlat_eq rest next env tbl outD lD cont contFlat hcont
    · simp only [hp, ite_true] at hcont; simp only [ite_true]
      cases hf : tbl.find h.sig h.ts h.code h.args with
      | some _ =>
        rw [hf] at hcont; dsimp only at hcont
        exact emitHoistsFlat_eq rest next env tbl outD lD cont contFlat hcont
      | none =>
        rw [hf] at hcont; dsimp only at hcont
        cases hr : resolveArgs env h.args with
        | none =>
          rw [hr] at hcont; dsimp only at hcont
          exact emitHoistsFlat_eq rest next env tbl outD lD cont contFlat hcont
        | some vArgs =>
          rw [hr] at hcont; dsimp only at hcont; dsimp only [toTFlat]
          refine congrArg (TFlat.let_ ⟨h.code, idxArgs outD vArgs⟩) ?_
          exact emitHoistsFlat_eq rest (next + h.ts.length)
            (envInsertTup env next (Tup.levels h.ts outD))
            (tbl.insert h.sig h.ts h.code h.args (freshGVals h.ts (Tup.levels h.ts outD) next))
            (outD + h.ts.length) lD cont contFlat hcont

private theorem insertTupEnv_eq_envInsertTup :
    {ts : List Ty} → (n : Nat) → (env : VEnv K) → (xs : Tup K ts) →
    insertTupEnv n env xs = envInsertTup env n xs
  | [], _, _, () => rfl
  | _ :: _, n, env, (_, xs) => insertTupEnv_eq_envInsertTup (n + 1) (env.insert n ⟨_, _⟩) xs

private abbrev LicmS := HoistPlan × Nat × VEnv K × GvnTbl K × Nat
private abbrev LicmSB := HoistBlocks × Nat × VEnv K × GvnTbl K × Nat

local macro "lr_store" fnF:Lean.Parser.Tactic.simpLemma "," eq:Lean.Parser.Tactic.rwRule : term =>
  `(fun s v a k hΓ _ _ hm hwf ih => by
    rcases s with ⟨_, sr⟩
    obtain ⟨hv, ha, hk⟩ := wf_store hwf
    dsimp only [denote, $fnF]
    rw [denoteArg_eq_some_resolveEnvArg hΓ hm v hv, denoteArg_eq_some_resolveEnvArg hΓ hm a ha]
    dsimp only; rw [$eq]; dsimp only [toTFlat]
    exact congrArg (TFlat.store _ _) (ih (outD' := 0) (_, sr) hΓ hm hk))

local macro "lr_jnz" fnF:Lean.Parser.Tactic.simpLemma "," eq:Lean.Parser.Tactic.rwRule : term =>
  `(fun s c t e hΓ _ _ hm hwf iht ihe => by
    rcases s with ⟨plan, sr⟩
    obtain ⟨hc, ht, he⟩ := wf_jnz hwf
    dsimp only [denote, $fnF]; rw [denoteArg_eq_some_resolveEnvArg hΓ hm c hc]
    dsimp only; rw [$eq]; dsimp only [toTFlat]
    cases plan <;> dsimp only <;>
      exact congr (congrArg (TFlat.jnz _) (iht (_, sr) ht)) (ihe (_, sr) he))

local macro "lr_jump" fnF:Lean.Parser.Tactic.simpLemma "," eq:Lean.Parser.Tactic.rwRule : term =>
  `(fun _ j args hΓ hΔ hll hm hwf => by
    obtain ⟨hj, ha⟩ := wf_jump hwf
    obtain ⟨_, hlk, hidx⟩ := lookupL_jump_eq hΔ hll hj
    dsimp only [denote, $fnF]; rw [hlk, denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha]
    dsimp only; rw [$eq]; dsimp only [toTFlat]; rw [hidx])

local macro "lr_ret" fnF:Lean.Parser.Tactic.simpLemma "," eq:Lean.Parser.Tactic.rwRule : term =>
  `(fun _ vs' hΓ _ _ hm hwf => by
    dsimp only [denote, $fnF]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm vs' hwf]
    dsimp only; rw [$eq]; rfl)

local macro "lr_exit" fnF:Lean.Parser.Tactic.simpLemma "," eq:Lean.Parser.Tactic.rwRule : term =>
  `(fun _ _ args hΓ _ _ hm hwf => by
    dsimp only [denote, $fnF]; rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args hwf]
    dsimp only; rw [$eq]; rfl)

private theorem licmSweepFlat_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD} {_outD_unused : Nat} {inE} (s : LicmS),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (licmSweep s.2.1 s.2.2.1 s.2.2.2.1 s.1 (denote (GVal K) KL tf vs ls))
          s.2.2.2.2 ls.length =
        licmSweepFlat s.2.1 s.2.2.1 s.2.2.2.1 s.1 tf inD inE s.2.2.2.2) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD} {_outD_unused : Nat} {inE} (sb : LicmSB),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (licmSweepB sb.2.1 sb.2.2.1 sb.2.2.2.1 sb.1 (denoteB (GVal K) KL tb vs ls))
          sb.2.2.2.2 ls.length =
        licmSweepBFlat sb.2.1 sb.2.2.1 sb.2.2.2.1 sb.1 tb inD inE sb.2.2.2.2) := by
  refine klSim_mutual ⟨
    @fun _ ts _ _ _ _ inD _ inE ⟨plan, next, env, tbl, outD⟩ op k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      dsimp only [denote, licmSweepFlat]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args ha]; dsimp only
      rw [licmSweep.eq_def]; dsimp only
      cases hfind : tbl.find op.sig ts op.code (tupGKey (resolveEnvArgs inD inE op.args)) with
      | some cached =>
        exact ih (outD' := 0) (_, next, env, tbl, outD) (CtxTypes.push _ hΓ)
          (trieCtxMatch_insertTupEnv hm cached) hk
      | none =>
        dsimp only [toTFlat]
        exact congrArg (TFlat.let_ _)
          (ih (outD' := 0) (_, next + ts.length, envInsertTup env next (Tup.levels ts outD), tbl,
              outD + ts.length) (CtxTypes.push _ hΓ)
            (trieCtxMatch_insertTupEnv hm (freshGVals ts (Tup.levels ts outD) next)) hk),
    fun ⟨plan, next, env, tbl, outD⟩ t a k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      dsimp only [denote, licmSweepFlat]
      rw [denoteArg_eq_some_resolveEnvArg hΓ hm a ha]; dsimp only
      rw [licmSweep.eq_def]; dsimp only [toTFlat]
      exact congrArg (TFlat.load t _)
        (ih (outD' := 0) (_, next + 1, env.insert next ⟨t, outD⟩, tbl, outD + 1) (.cons hΓ)
          (hm.cons t (outD, next)) hk),
    lr_store licmSweepFlat, licmSweep.eq_def,
    fun ⟨plan, next, env, tbl, outD⟩ f bs args k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      dsimp only [denote, licmSweepFlat]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha]; dsimp only
      rw [licmSweep.eq_def]; dsimp only [toTFlat]
      exact congrArg (TFlat.call f bs _)
        (ih (outD' := 0) (_, next + bs.length, envInsertTup env next (Tup.levels bs outD), tbl,
            outD + bs.length) (CtxTypes.push _ hΓ)
          (trieCtxMatch_insertTupEnv hm (freshGVals bs (Tup.levels bs outD) next)) hk),
    lr_jnz licmSweepFlat, licmSweep.eq_def,
    lr_jump licmSweepFlat, licmSweep.eq_def,
    lr_ret licmSweepFlat, licmSweep.eq_def,
    lr_exit licmSweepFlat, licmSweep.eq_def,
    fun _ _ _ _ _ _ => by dsimp only [denote, licmSweepFlat]; rw [licmSweep.eq_def]; rfl,
    @fun rs sig _ _ _ ls _ _ _ ⟨plan, next, env, tbl, outD⟩ bodies k _ hΔ hll _ hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote, licmSweepFlat]; rw [licmSweep.eq_def]; dsimp only
      let p := match plan with | .groupNode hs bsP kP => (hs, bsP, kP) | _ => ([], .nil, .leaf)
      refine emitHoistsFlat_eq p.1 next env tbl outD ls.length _
        (fun n' e' t' od' =>
          .group (licmSweepBFlat n' e' t' p.2.1 bodies _ _ od')
            (licmSweepFlat n' e' t' p.2.2 k _ _ od')) ?_
      dsimp only [toTFlat]
      let r := emitHoistsFlat (rs := rs) p.1 next env tbl outD
      have hb' := ihB (p.2.1, r.next, r.env, r.tbl, r.outDepth)
        (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hb
      have hk' := ihK (p.2.2, r.next, r.env, r.tbl, r.outDepth)
        (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hk
      rw [pushTup_length (Tup.levels sig ls.length) ls] at hb' hk'
      exact congr (congrArg TFlat.group hb') hk',
    fun _ _ _ _ _ _ => rfl,
    @fun _ ts _ _ _ _ _ _ _ _ ⟨bsPlan, next, env, tbl, outD⟩ b bs hΓ _ _ hm hwf ihb ihbs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      dsimp only [denoteB, licmSweepBFlat, licmSweepB, toTBlocks]
      cases bsPlan <;> dsimp only <;>
        exact congr (congrArg TBlocks.cons
          (ihb (outD' := 0) (_, next + ts.length, envInsertTup env next (Tup.levels ts outD), tbl,
              outD + ts.length) (CtxTypes.push _ hΓ)
            (trieCtxMatch_insertTupEnv hm (freshGVals ts (Tup.levels ts outD) next)) hb))
          (ihbs (_, next, env, tbl, outD) hbs)⟩

/-- `licmPureFlat as tf = reifyFunc (Func.licmPure (denoteFunc tf))` under `wfCheck = true`. -/
theorem licmPureFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    licmPureFlat as tf = reifyFunc (Func.licmPure (denoteFunc (as := as) tf)) := by
  dsimp only [licmPureFlat, Func.licmPure]
  have hr : reifyFunc (denoteFunc (as := as) tf) = tf := reifyFunc_denoteFunc_eq tf hwf
  rw [hr]
  split
  · have hm := trieCtxMatch_initEnv (fun {t} (x : K t) next => ((x, next) : GVal K t)) as
    have h := licmSweepFlat_both.1 tf
      (Licm.buildHoistPlan as.length tf, as.length, insertTupEnv 0 .empty (Tup.levels as 0),
        .empty, as.length)
      (CtxTypes.push _ .nil) .nil CtxLevels.nil hm hwf (_outD_unused := 0)
    dsimp only [reifyFunc, denoteFunc]
    rw [← insertTupEnv_eq_envInsertTup]
    exact h.symm
  · exact hr.symm

/-- `licmPureFlat` preserves `wfCheck`. -/
theorem licmPureFlat_wfCheck {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    (licmPureFlat as tf).wfCheck (pushTypes as []) [] = true :=
  wfCheck_of_flat_eq Func.licmPure_wf tf hwf (licmPureFlat_eq tf hwf)

/-! ## 2. Read-Only Load LICM Equivalence (`roSweepFlat_eq`, `licmFlat_eq`) -/

private theorem emitRoHoistsFlat_eq {rs : List Ty} :
    (hs : List HoistLoad) → (next : Nat) → (env : VEnv K) → (outD lD : Nat) →
    (cont : Nat → VEnv K → Expr K KL rs) →
    (contFlat : Nat → VEnv K → Nat → TFlat rs) →
    (let r : RoEmitRes rs := emitRoHoistsFlat hs next env outD;
      toTFlat (cont r.next r.env) r.outDepth lD = contFlat r.next r.env r.outDepth) →
    toTFlat (emitRoHoists hs next env cont) outD lD =
      let r : RoEmitRes rs := emitRoHoistsFlat hs next env outD
      r.wrap (contFlat r.next r.env r.outDepth)
  | [], _, _, _, _, _, _, hcont => hcont
  | h :: rest, next, env, outD, lD, cont, contFlat, hcont => by
    dsimp only [emitRoHoists, emitRoHoistsFlat]
    dsimp only [emitRoHoistsFlat] at hcont
    cases hres : resolveArg env h.addr with
    | none =>
      rw [hres] at hcont; dsimp only at hcont
      exact emitRoHoistsFlat_eq rest next env outD lD cont contFlat hcont
    | some va =>
      rw [hres] at hcont; dsimp only at hcont; dsimp only [toTFlat]
      refine congrArg (TFlat.load h.ty _) ?_
      exact emitRoHoistsFlat_eq rest (next + 1) (env.insert next ⟨h.ty, outD⟩)
        (outD + 1) lD cont contFlat hcont

private abbrev RoS := RoPlan × Nat × VEnv K × Nat
private abbrev RoSB := RoBlocks × Nat × VEnv K × Nat

private theorem roSweepFlat_both :
    (∀ {rs : List Ty} (tf : TFlat rs) {Γ Δ vs ls inD} {_outD_unused : Nat} {inE} (s : RoS),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tf.wfCheck Γ Δ = true →
      toTFlat (roSweep s.2.1 s.2.2.1 s.1 (denote K KL tf vs ls)) s.2.2.2 ls.length =
        roSweepFlat s.2.1 s.2.2.1 s.1 tf inD inE s.2.2.2) ∧
    (∀ {rs : List Ty} {sig : List (List Ty)} (tb : TBlocks rs sig)
      {Γ Δ vs ls inD} {_outD_unused : Nat} {inE} (sb : RoSB),
      CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels ls →
      TrieCtxMatch inD inE vs → tb.wfCheck Γ Δ = true →
      toTBlocks (roSweepB sb.2.1 sb.2.2.1 sb.1 (denoteB K KL tb vs ls)) sb.2.2.2 ls.length =
        roSweepBFlat sb.2.1 sb.2.2.1 sb.1 tb inD inE sb.2.2.2) := by
  refine klSim_mutual ⟨
    @fun _ ts _ _ _ _ _ _ _ ⟨plan, next, env, outD⟩ op k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_let hwf
      dsimp only [denote, roSweepFlat]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm op.args ha]; dsimp only
      rw [roSweep.eq_def]; dsimp only [toTFlat]
      exact congrArg (TFlat.let_ _)
        (ih (outD' := 0) (_, next + ts.length, envInsertTup env next (Tup.levels ts outD),
            outD + ts.length) (CtxTypes.push _ hΓ)
          (trieCtxMatch_insertTupEnv hm (Tup.levels ts outD)) hk),
    fun ⟨plan, next, env, outD⟩ t a k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_load hwf
      dsimp only [denote]; rw [denoteArg_eq_some_resolveEnvArg hΓ hm a ha]; dsimp only
      rw [roSweep.eq_def]
      cases plan with
      | fwdLoad lvl kPlan =>
        dsimp only [roSweepFlat]
        cases hfind : env.find? lvl with
        | none =>
          dsimp only [toTFlat]
          exact congrArg (TFlat.load t _)
            (ih (outD' := 0) (kPlan, next + 1, env.insert next ⟨t, outD⟩, outD + 1)
              (.cons hΓ) (hm.cons t outD) hk)
        | some p =>
          rcases p with ⟨t', v⟩; dsimp only
          split
          · exact ih (outD' := 0) (kPlan, next, env, outD) (.cons hΓ) (hm.cons t _) hk
          · dsimp only [toTFlat]
            exact congrArg (TFlat.load t _)
              (ih (outD' := 0) (kPlan, next + 1, env.insert next ⟨t, outD⟩, outD + 1)
                (.cons hΓ) (hm.cons t outD) hk)
      | node1 _ | leaf | node2 _ _ | groupNode _ _ _ =>
        dsimp only [roSweepFlat, toTFlat]
        exact congrArg (TFlat.load t _)
          (ih (outD' := 0) (_, next + 1, env.insert next ⟨t, outD⟩, outD + 1)
            (.cons hΓ) (hm.cons t outD) hk),
    lr_store roSweepFlat, roSweep.eq_def,
    fun ⟨plan, next, env, outD⟩ f bs args k hΓ _ _ hm hwf ih => by
      obtain ⟨ha, hk⟩ := wf_call hwf
      dsimp only [denote, roSweepFlat]
      rw [denoteArgs_eq_some_resolveEnvArgs hΓ hm args ha]; dsimp only
      rw [roSweep.eq_def]; dsimp only [toTFlat]
      exact congrArg (TFlat.call f bs _)
        (ih (outD' := 0) (_, next + bs.length, envInsertTup env next (Tup.levels bs outD),
            outD + bs.length) (CtxTypes.push _ hΓ)
          (trieCtxMatch_insertTupEnv hm (Tup.levels bs outD)) hk),
    lr_jnz roSweepFlat, roSweep.eq_def,
    lr_jump roSweepFlat, roSweep.eq_def,
    lr_ret roSweepFlat, roSweep.eq_def,
    lr_exit roSweepFlat, roSweep.eq_def,
    fun _ _ _ _ _ _ => by dsimp only [denote, roSweepFlat]; rw [roSweep.eq_def]; rfl,
    @fun rs sig _ _ _ ls _ _ _ ⟨plan, next, env, outD⟩ bodies k _ hΔ hll _ hwf ihB ihK => by
      obtain ⟨hb, hk⟩ := wf_group hwf
      dsimp only [denote, roSweepFlat]; rw [roSweep.eq_def]; dsimp only
      let p := match plan with | .groupNode hs bsP kP => (hs, bsP, kP) | _ => ([], .nil, .leaf)
      refine emitRoHoistsFlat_eq p.1 next env outD ls.length _
        (fun n' e' od' =>
          .group (roSweepBFlat n' e' p.2.1 bodies _ _ od') (roSweepFlat n' e' p.2.2 k _ _ od')) ?_
      dsimp only [toTFlat]
      let r := emitRoHoistsFlat (rs := rs) p.1 next env outD
      have hb' := ihB (p.2.1, r.next, r.env, r.outDepth)
        (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hb
      have hk' := ihK (p.2.2, r.next, r.env, r.outDepth)
        (CtxTypes.push (Tup.levels sig ls.length) hΔ) hll.pushTup hk
      rw [pushTup_length (Tup.levels sig ls.length) ls] at hb' hk'
      exact congr (congrArg TFlat.group hb') hk',
    fun _ _ _ _ _ _ => rfl,
    @fun _ ts _ _ _ _ _ _ _ _ ⟨plan, next, env, outD⟩ b bs hΓ _ _ hm hwf ihb ihbs => by
      obtain ⟨hb, hbs⟩ := wf_cons hwf
      dsimp only [denoteB, roSweepBFlat, roSweepB, toTBlocks]
      cases plan <;> dsimp only <;>
        exact congr (congrArg TBlocks.cons
          (ihb (outD' := 0) (_, next + ts.length, envInsertTup env next (Tup.levels ts outD),
              outD + ts.length)
            (CtxTypes.push _ hΓ) (trieCtxMatch_insertTupEnv hm (Tup.levels ts outD)) hb))
          (ihbs (_, next, env, outD) hbs)⟩

/-- `licmFlat as tf = reifyFunc (Func.licm (denoteFunc tf))` under `wfCheck = true`. -/
theorem licmFlat_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    licmFlat as tf = reifyFunc (Func.licm (denoteFunc (as := as) tf)) := by
  dsimp only [licmFlat, Func.licm]
  have hwf1 : (licmPureFlat as tf).wfCheck (pushTypes as []) [] = true :=
    licmPureFlat_wfCheck tf hwf
  rw [licmPureFlat_eq tf hwf]
  have hf1 : Func.licmPure (denoteFunc (as := as) tf) =
      denoteFunc (as := as) (licmPureFlat as tf) := by
    rw [licmPureFlat_eq tf hwf]
    exact (Func.renorm_eq_self (Func.licmPure_wf (Func.wf_of_denote tf rfl))).symm
  rw [hf1, reifyFunc_denoteFunc_eq (licmPureFlat as tf) hwf1]
  split
  · let p1 := licmPureFlat as tf
    let rp := Licm.buildRoPlan as.length p1
    let initE := insertTupEnv 0 .empty (Tup.levels as 0)
    have hr := roSweepFlat_both.1 p1 (rp, as.length, initE, as.length)
      (CtxTypes.push _ .nil) .nil CtxLevels.nil
      (trieCtxMatch_insertTupEnv .empty (Tup.levels as 0)) hwf1 (_outD_unused := 0)
    let tf2 := roSweepFlat as.length initE rp p1 as.length initE as.length
    have hro : reifyFunc (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs) rp
        (denoteFunc (as := as) p1 V L xs)) = tf2 := by
      dsimp only [reifyFunc, denoteFunc]; rw [← insertTupEnv_eq_envInsertTup]; simpa using hr
    have hwfRo : Func.Wf (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs) rp
        (denoteFunc (as := as) p1 V L xs)) := by
      have hwfF : (denoteFunc (as := as) p1).Wf := Func.wf_of_denote (as := as) p1 rfl
      have h := roSweepFunc_wf hwfF
      rwa [reifyFunc_denoteFunc_eq p1 hwf1] at h
    have hdf2 : (fun V L xs => roSweep as.length (envInsertTup .empty 0 xs) rp
        (denoteFunc (as := as) p1 V L xs)) = denoteFunc (as := as) tf2 := by
      rw [← hro]; exact (Func.renorm_eq_self hwfRo).symm
    change licmPureFlat as tf2 = _
    rw [hdf2]; exact licmPureFlat_eq tf2 (by rw [← hro]; exact PassFlatKit.reifyFunc_wfCheck hwfRo)
  · exact (reifyFunc_denoteFunc_eq (licmPureFlat as tf) hwf1).symm

flat_pass_corollaries licmFlat, Func.licm, Func.licm_wf,
  licmFlat_eq, denoteFunc_licmFlat, licmFlat_wfCheck,
  licmFlatFn, licmFlatFn_toFn, licmFlatFn_wfCheck

end OptFlatLoop
end LeanQbe.T