module

public import LeanQbe.T.CondThreadOptLemmas1
import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.WfLemmas
import LeanQbe.T.FoldLemmas

/-!
# Soundness Proofs for `CondThreadOpt` — Part 2 (`condThreadPass` WP, `callsOk`, & Entrypoints)

Proves `OptValCtx`, `peelThreadHead_wp`, `rewriteCTInline_wp`, `rewriteCTAux_wp`, `*_callsOk`,
and top-level `Func.condThreadWithPlan_*`, `Func.condThreadPass_*`, `Func.condThreadOpt_*`,
`condThread_ok`, `Fn.condThreadOpt_*`, and `Func.condThreadLateOpt_*`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open CondThreadOpt

namespace CondThreadOptImpl

/-! ### Weakest-precondition refinement (`peelThreadHead_wp`, `rewriteCTInline_wp`, `rewriteCTAux_wp`) -/

/-- Value-recovery invariant linking `Arg (CTOptV Val)` bindings to concrete `Val` values,
forbidding `.var none`. -/
def OptValCtx (G : Ctx (Arg (CTOptV Val)) Val) : Prop :=
  ∀ q ∈ G, ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2

theorem OptValCtx.flattenArg {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G)
    {t : Ty} {a : Arg (Arg (CTOptV Val)) t} {v : Arg Val t} (ha : ArgRel G t a v) :
    ∃ ra : Arg Val t, toRealArg? (LeanQbe.T.flattenArg a) = some ra ∧ ra.val = v.val := by
  cases ha with
  | imm c => exact ⟨.imm c, rfl, rfl⟩
  | var hm => exact hG _ hm

theorem trel_toRealArgs?_flattenArgs_wp {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G) :
    {ts : List Ty} → {as : Tup (Arg (Arg (CTOptV Val))) ts} → {vs : Tup (Arg Val) ts} →
    TRel (ArgRel G) as vs →
    ∃ ras : Tup (Arg Val) ts, toRealArgs? (flattenArgs as) = some ras ∧ vals ras = vals vs
  | [], (), (), .nil => ⟨(), rfl, rfl⟩
  | _ :: _, (_, _), (_, _), .cons ha has => by
    obtain ⟨ra, hra, hval⟩ := hG.flattenArg ha
    obtain ⟨ras, hras, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG has
    refine ⟨(ra, ras), ?_, Prod.ext hval hvals⟩
    dsimp only [flattenArgs, tupMapArg, toRealArgs?]
    rw [hra, hras]; rfl

theorem OptValCtx.of_toRealArgs? {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G) :
    {ts : List Ty} → {as : Tup (Arg (CTOptV Val)) ts} → {ras : Tup (Arg Val) ts} →
    toRealArgs? as = some ras → OptValCtx (Tup.zip as (vals ras) ++ G)
  | [], (), (), _, q, hq => by
    dsimp only [vals, Tup.zip] at hq
    exact hG q hq
  | _ :: _, (a, as), (ra, ras), h, q, hq => by
    dsimp only [toRealArgs?] at h
    cases ha : toRealArg? a <;> rw [ha] at h
    · simp at h
    cases has : toRealArgs? as <;> rw [has] at h
    · simp at h
    cases h
    dsimp only [vals, Tup.zip] at hq
    cases hq with
    | head => exact ⟨_, ha, rfl⟩
    | tail _ hq' => exact OptValCtx.of_toRealArgs? hG has q hq'

theorem OptValCtx.of_toOptArgTup {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G) :
    {ts : List Ty} → (xs : Tup Val ts) → OptValCtx (Tup.zip (toOptArgTup xs) xs ++ G)
  | [], (), q, hq => hG q hq
  | _ :: _, (x, xs), q, hq => by
    cases hq with
    | head => exact ⟨.var x, rfl, rfl⟩
    | tail _ hq' => exact OptValCtx.of_toOptArgTup hG xs q hq'

theorem OptValCtx.cons_var {G : Ctx (Arg (CTOptV Val)) Val} (hG : OptValCtx G)
    {t : Ty} (v : Val t) : OptValCtx (⟨t, .var (some v), v⟩ :: G) := fun q hq => by
  cases hq with
  | head => exact ⟨.var v, rfl, rfl⟩
  | tail _ hq' => exact hG q hq'

theorem OptValCtx.toRealArgs?_zip {G : Ctx (Arg (CTOptV Val)) Val} (_hG : OptValCtx G) :
    {ts : List Ty} → {a : Tup (Arg (CTOptV Val)) ts} → {xs : Tup Val ts} →
    (∀ q ∈ Tup.zip a xs, ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2) →
    ∃ ra : Tup (Arg Val) ts, toRealArgs? a = some ra ∧ vals ra = xs
  | [], (), (), _ => ⟨(), rfl, rfl⟩
  | _ :: _, (a, as), (x, xs), ha => by
    obtain ⟨ra₁, hra₁, hv₁⟩ := ha _ List.mem_cons_self
    obtain ⟨ras, hras, hvs⟩ :=
        OptValCtx.toRealArgs?_zip _hG (fun _ hp => ha _ (List.mem_cons_of_mem _ hp))
    refine ⟨(ra₁, ras), ?_, Prod.ext hv₁ hvs⟩
    dsimp only [toRealArgs?]
    rw [hra₁, hras]; rfl

theorem toRealArgs?_immsTup {V : Ty → Type} :
    {ts : List Ty} → (cs : Tup Val ts) →
    toRealArgs? (V := V) (immsTup cs) = some (immsTup cs)
  | [], () => rfl
  | _ :: _, (c, cs) => by
    dsimp only [immsTup, toRealArgs?, toRealArg?]
    rw [toRealArgs?_immsTup cs]; rfl

theorem toRealArgs?_getTupMem {V : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {a : Tup (Arg (CTOptV V)) ts} → {ra : Tup (Arg V) ts} →
    toRealArgs? a = some ra → toRealArg? (getTupMem m a) = some (getTupMem m ra)
  | _ :: _, .here, (x, xs), (_, _), h => by
    dsimp only [toRealArgs?, Option.bind] at h
    cases ha : toRealArg? x <;> rw [ha] at h <;> simp at h
    cases hr : toRealArgs? xs <;> rw [hr] at h <;> simp at h
    rcases h with ⟨rfl, rfl⟩; exact ha
  | _ :: _, .there m, (x, xs), (_, _), h => by
    dsimp only [toRealArgs?, Option.bind] at h
    cases ha : toRealArg? x <;> rw [ha] at h <;> simp at h
    cases hr : toRealArgs? xs <;> rw [hr] at h <;> simp at h
    rcases h with ⟨rfl, rfl⟩; exact toRealArgs?_getTupMem m hr

theorem toRealArgs?_dropTupMem {V : Ty → Type} {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → {a : Tup (Arg (CTOptV V)) ts} → {ra : Tup (Arg V) ts} →
    toRealArgs? a = some ra → toRealArgs? (dropTupMem m a) = some (dropTupMem m ra)
  | _ :: _, .here, (x, xs), (_, _), h => by
    dsimp only [toRealArgs?, Option.bind] at h
    cases ha : toRealArg? x <;> rw [ha] at h <;> simp at h
    cases hr : toRealArgs? xs <;> rw [hr] at h <;> simp at h
    rcases h with ⟨rfl, rfl⟩; exact hr
  | _ :: _, .there m, (x, xs), (_, _), h => by
    dsimp only [toRealArgs?, Option.bind] at h
    cases ha : toRealArg? x <;> rw [ha] at h <;> simp at h
    cases hr : toRealArgs? xs <;> rw [hr] at h <;> simp at h
    rcases h with ⟨rfl, rfl⟩
    simp only [dropTupMem, toRealArgs?, Option.bind, Bind.bind, ha,
      toRealArgs?_dropTupMem m hr]
    rfl

theorem OptValCtx.tup_insertTupMem {u : Ty} :
    {ts : List Ty} → (m : Member u ts) → (b : Val u) → (xs : Tup Val (eraseMem m)) →
    ∀ q ∈ Tup.zip (insertTupMem m (.imm b) (toOptArgTup xs)) (insertTupMem m b xs),
      ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2
  | _ :: _, .here, b, xs, _, hq => by
    have h1 : insertTupMem Member.here (.imm b) (toOptArgTup xs) = (.imm b, toOptArgTup xs) := rfl
    have h2 : insertTupMem Member.here b xs = (b, xs) := rfl
    rw [h1, h2] at hq
    cases hq with
    | head => exact ⟨.imm b, rfl, rfl⟩
    | tail _ hq' =>
      exact OptValCtx.of_toOptArgTup (fun _ h => by cases h) xs _ (List.mem_append_left [] hq')
  | _ :: _, .there m, b, xs, _, hq => by
    rcases xs with ⟨x, xs⟩
    have h1 : insertTupMem m.there (.imm b) (toOptArgTup (x, xs)) =
        (.var (some x), insertTupMem m (.imm b) (toOptArgTup xs)) := rfl
    have h2 : insertTupMem m.there b (x, xs) = (x, insertTupMem m b xs) := rfl
    rw [h1, h2] at hq
    cases hq with
    | head => exact ⟨.var x, rfl, rfl⟩
    | tail _ hq' => exact OptValCtx.tup_insertTupMem m b xs _ hq'

theorem tupImms?_real_eq :
    {ts : List Ty} → {a : Tup (Arg (CTOptV Val)) ts} → {ra : Tup (Arg Val) ts} → {vts : Tup Val
        ts} →
    toRealArgs? a = some ra → tupImms? a = some vts → vals ra = vts
  | [], (), (), (), _, _ => rfl
  | _ :: _, (x, xs), (rx, rxs), (v, vs), hr, hi => by
    dsimp only [toRealArgs?, Bind.bind, Option.bind] at hr
    cases hx : toRealArg? x <;> rw [hx] at hr <;> simp at hr
    cases hxs : toRealArgs? xs <;> rw [hxs] at hr <;> simp at hr
    rcases hr with ⟨rfl, rfl⟩
    dsimp only [tupImms?, Option.bind] at hi
    cases x with
    | var _ => cases hi
    | imm c =>
      dsimp only [Arg.imm?] at hi
      cases hixs : tupImms? xs <;> rw [hixs] at hi <;> simp at hi
      rcases hi with ⟨rfl, rfl⟩
      dsimp only [toRealArg?] at hx; cases hx
      exact Prod.ext rfl (tupImms?_real_eq hxs hixs)

theorem evalThreadLet?_opt_wp {sig dts : List Ty} (code : OpCode sig dts)
    {args₁ : Tup (Arg (CTOptV Val)) sig} {ra₁ : Tup (Arg Val) sig} {vs₂ : Tup Val sig}
    (hreal : toRealArgs? args₁ = some ra₁) (hvs : vals ra₁ = vs₂)
    {out : Tup (Arg (CTOptV Val)) dts} (heval : evalThreadLet? code args₁ = some out)
    {post : Tup Val dts → Prop} (hw : code.wp vs₂ post) :
    ∃ rout : Tup (Arg Val) dts, toRealArgs? out = some rout ∧ post (vals rout) := by
  rw [← hvs] at hw
  cases code with
  | copy _ =>
    rcases args₁ with ⟨a, _⟩; rcases ra₁ with ⟨r, _⟩
    dsimp only [evalThreadLet?] at heval; cases heval
    exact ⟨(r, ()), hreal, hw⟩
  | _ =>
    all_goals
      dsimp only [evalThreadLet?] at heval
      split at heval
      · simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff] at heval
        rcases heval with ⟨cs, hcs, rfl⟩
        rcases hcs with ⟨vts, hv, hev⟩
        have hvv := tupImms?_real_eq hreal hv
        rw [hvv] at hw
        exact ⟨immsTup cs, toRealArgs?_immsTup cs,
          by rw [immsTup_vals]; exact OpCode.eval?_sound _ vts post hev hw⟩
      · cases heval

/-- Target-side `Closed` predicate for `ctSrcCont`. -/
def ctSrcTargetPred {ts : List Ty} (tgt : CTTarget Val Cont ts) (xs : Tup Val ts) (m : Mem 64) :
    Prop :=
  match tgt with
  | .keep j => j xs m
  | .dead => True
  | .split mem lT? lF? lD? =>
    (match lD? with | some jD => jD xs m | none => True) ∧
    (getTupMem mem xs = true →
      match lT? with | some jT => jT (dropTupMem mem xs) m | none => True) ∧
    (getTupMem mem xs = false → match lF? with | some jF => jF (dropTupMem mem xs) m | none => True)

/-- Weakest-precondition label invariant for `(l : CTLabel Val Cont rs ts, J : Cont ts)`. -/
def CTTargetWp (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) {ts : List Ty}
    (tgt : CTTarget Val Cont ts) (J : Cont ts) : Prop :=
  ∀ (a : Tup (Arg (CTOptV Val)) ts) (ra : Tup (Arg Val) ts) (m : Mem 64),
    toRealArgs? a = some ra → tgt.canEmit a = true → J (vals ra) m →
    wp Γ Q X (tgt.emit (rs := rs) a) m

def CTJumpWp (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (l : CTLabel Val Cont rs ts) (J : Cont ts) : Prop :=
  CTTargetWp Γ Q X l.target J ∧
    ∀ (a : Tup (Arg (CTOptV Val)) ts) (ra : Tup (Arg Val) ts) e_out m,
      l.inline? a = some e_out → toRealArgs? a = some ra → J (vals ra) m → wp Γ Q X e_out m

def CTWpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost)
    (D : Ctx (CTLabel Val Cont rs) Cont) : Prop :=
  ∀ p ∈ D, CTJumpWp Γ Q X p.2.1 p.2.2

theorem CTWpD.append {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {H D : Ctx (CTLabel Val Cont rs) Cont}
    (hH : CTWpD Γ Q X H) (hD : CTWpD Γ Q X D) : CTWpD Γ Q X (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

theorem ctSrcTargetPred_to_wp {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost}
    {tgt : CTTarget Val Cont ts} {J : Cont ts}
    (h : ∀ xs m, J xs m → ctSrcTargetPred tgt xs m) :
    CTTargetWp Γ Q X tgt J := by
  intro a ra m hreal hcan hJ
  have hp := h (vals ra) m hJ
  cases tgt with
  | keep j =>
    dsimp only [CTTarget.emit]; rw [hreal]; exact hp
  | dead => simp [CTTarget.canEmit] at hcan
  | split mem lT? lF? lD? =>
    dsimp only [ctSrcTargetPred] at hp
    rcases hp with ⟨hpD, hpT, hpF⟩
    have hget := toRealArgs?_getTupMem mem hreal
    have hdrop := toRealArgs?_dropTupMem mem hreal
    dsimp only [CTTarget.canEmit] at hcan
    dsimp only [CTTarget.emit]
    cases e₁ : getTupMem mem a <;> rw [e₁] at hcan hget
    · rename_i ov
      cases ov with
      | none => dsimp only [toRealArg?] at hget; cases hget
      | some v =>
        dsimp only [toRealArg?] at hget
        have hv : getTupMem mem ra = .var v := Option.some.inj hget.symm
        have hvv : v = getTupMem mem (vals ra) := by
          have := getTupMem_vals mem ra; rw [hv] at this; exact this
        cases lD? with
        | some jD =>
          dsimp only; rw [hreal]; exact hpD
        | none =>
          dsimp only at hcan
          simp only [Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hcan
          rcases hcan with ⟨hTs, hFs⟩
          cases eT : lT? <;> rw [eT] at hTs <;> simp at hTs
          cases eF : lF? <;> rw [eF] at hFs <;> simp at hFs
          dsimp only
          rw [hdrop]; dsimp only [wp]
          refine ⟨fun ht => ?_, fun hf => ?_⟩
          · rw [dropTupMem_vals]; simpa [eT] using hpT (by rw [← hvv]; exact ht)
          · rw [dropTupMem_vals]; simpa [eF] using hpF (by rw [← hvv]; exact hf)
    · rename_i b
      dsimp only [toRealArg?] at hget
      have hb : getTupMem mem ra = .imm b := Option.some.inj hget.symm
      have hbv : b = getTupMem mem (vals ra) := by
        have := getTupMem_vals mem ra; rw [hb] at this; exact this
      cases b
      · rw [hdrop]
        cases eF : lF? <;> rw [eF] at hcan <;> simp at hcan
        dsimp only [wp]; rw [dropTupMem_vals]
        simpa [eF] using hpF (by rw [← hbv])
      · rw [hdrop]
        cases eT : lT? <;> rw [eT] at hcan <;> simp at hcan
        dsimp only [wp]; rw [dropTupMem_vals]
        simpa [eT] using hpT (by rw [← hbv])

/-- Source continuation tuple used for `Closed` in the `.group` case of `rewriteCTAux_wp`. -/
def ctSrcCont (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (l : CTLabel Val Cont rs ts) : Cont ts :=
  fun xs m =>
    ctSrcTargetPred l.target xs m ∧
    ∀ (a : Tup (Arg (CTOptV Val)) ts) (ra : Tup (Arg Val) ts) e_out,
      l.inline? a = some e_out → toRealArgs? a = some ra → vals ra = xs → wp Γ Q X e_out m

def ctSrcConts (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → Tup (CTLabel Val Cont rs) sig → Tup Cont sig
  | [], () => ()
  | _ :: _, (l, ls) => (ctSrcCont Γ Q X l, ctSrcConts Γ Q X ls)

private theorem ctSrcConts_get (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (ls : Tup (CTLabel Val Cont rs) sig) →
    {ts : List Ty} → (i : Member ts sig) →
    (ctSrcConts Γ Q X ls).get i = ctSrcCont Γ Q X (ls.get i)
  | _ :: _, (_, _), _, .here => rfl
  | _ :: _, (_, ls), _, .there i => ctSrcConts_get Γ Q X ls i

theorem ctSrcConts_wpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (ls : Tup (CTLabel Val Cont rs) sig) →
    CTWpD Γ Q X (Tup.zip ls (ctSrcConts Γ Q X ls))
  | [], (), _, hp => nomatch hp
  | _ :: _, (l, ls), p, hp => by
    cases hp with
    | head =>
      refine ⟨ctSrcTargetPred_to_wp (fun _ _ h => h.1), fun a ra e_out m he hreal hJ => ?_⟩
      exact hJ.2 a ra e_out he hreal rfl
    | tail _ hp' => exact ctSrcConts_wpD Γ Q X ls p hp'

/-- Target equality between two label tuples (ignoring `.inline?`). -/
def TargetsEq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → Tup (CTLabel V L rs) sig → Tup (CTLabel V L rs) sig → Prop
  | [], (), () => True
  | _ :: _, (l₁, ls₁), (l₂, ls₂) => l₁.target = l₂.target ∧ TargetsEq ls₁ ls₂

theorem attachInlines_targetsEq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs : Blocks (Arg (CTOptV V)) (CTLabel V L rs) rs sig) →
    (ls : Tup (CTLabel V L rs) sig) →
    TargetsEq ls (attachInlines acts pbs bs ls)
  | _, _, [], .nil, () => trivial
  | a :: acts, .cons pb pbs, _ :: _, .cons b bs, (l, ls) => by
    refine ⟨?_, attachInlines_targetsEq acts pbs bs ls⟩
    cases a with
    | keep _ allow => cases allow <;> rfl
    | splitBool _ _ _ _ inlT inlF =>
      dsimp only [tryMakeInlineLabel]
      split <;> rfl
  | [], _, _ :: _, .cons _ bs, (_, ls) =>
    ⟨rfl, attachInlines_targetsEq [] .nil bs ls⟩
  | _ :: _, .nil, _ :: _, .cons _ bs, (_, ls) =>
    ⟨rfl, attachInlines_targetsEq [] .nil bs ls⟩

theorem ctSrcConts_noInl_wpD (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    {sig : List (List Ty)} → (lsNo lsBody : Tup (CTLabel Val Cont rs) sig) →
    (∀ {ts} (i : Member ts sig) a, (lsNo.get i).inline? a = none) →
    TargetsEq lsNo lsBody →
    CTWpD Γ Q X (Tup.zip lsNo (ctSrcConts Γ Q X lsBody))
  | [], (), (), _, _, _, hp => nomatch hp
  | _ :: _, (l₁, ls₁), (l₂, ls₂), hno, ⟨ht, hts⟩, p, hp => by
    cases hp with
    | head =>
      refine ⟨ctSrcTargetPred_to_wp (fun xs m h => ht ▸ h.1),
        fun a _ _ _ he => by
          have hget : l₁.inline? a = none := hno .here a; rw [hget] at he; cases he⟩
    | tail _ hp' =>
      exact ctSrcConts_noInl_wpD Γ Q X ls₁ ls₂ (fun i => hno (.there i)) hts p hp'

theorem buildTargets_noInl_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → {sig : List (List Ty)} → (Js : Tup L (threadSig acts sig)) →
    ∀ {ts} (i : Member ts sig) a, ((buildTargets (V := V) (rs :=
        rs) acts sig Js).get i).inline? a = none
  | [], _ :: _, (_, _), _, .here, _ => rfl
  | [], _ :: _, (_, js), _, .there i, a => buildTargets_noInl_get [] js i a
  | _ :: _, _ :: _, _, _, .here, _ => rfl
  | _ :: acts, _ :: _, _, _, .there i, a => buildTargets_noInl_get acts _ i a

theorem peelThreadHead_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV Val)) Val} → {D : Ctx (CTLabel Val Cont rs) Cont} →
    {e₂ : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs} → {e₃ : Expr Val Cont rs} →
    Wf G D e₂ e₃ → OptValCtx G → ∀ {m}, wp Γ Q X e₃ m →
    let r := peelThreadHead fuel res p e₂
    ∃ G' e₃', Wf G' D r.2.2 e₃' ∧ OptValCtx G' ∧ wp Γ Q X e₃' m
  | 0, _, _, _, _, _, _, hwf, hG, _, hw => ⟨_, _, hwf, hG, hw⟩
  | fuel + 1, res, p, _, _, _, _, hwf, hG, _, hw => by
    cases p with
    | node1 pk =>
      have hwf0 := hwf
      cases hwf
      case let_ hop hk =>
        clear hwf0
        rcases hop with ⟨code, hargs⟩
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
        dsimp only [peelThreadHead]
        cases he : evalThreadLet? code (flattenArgs _) with
        | none => exact ⟨_, _, .let_ (.mk code hargs) hk, hG, hw⟩
        | some out =>
          obtain ⟨rout, hrout, hkw⟩ := evalThreadLet?_opt_wp code hra hvals he hw
          exact peelThreadHead_wp fuel res pk (hk out (vals rout))
            (OptValCtx.of_toRealArgs? hG hrout) hkw
      all_goals exact ⟨_, _, hwf0, hG, hw⟩
    | node2 pt pe =>
      have hwf0 := hwf
      cases hwf
      case jnz hc ht he =>
        clear hwf0
        obtain ⟨ra, hra, hval⟩ := hG.flattenArg hc
        dsimp only [peelThreadHead]
        cases ef : flattenArg _ with
        | imm b =>
          rw [ef] at hra
          dsimp only [toRealArg?] at hra; cases hra
          cases b with
          | false => exact peelThreadHead_wp fuel true pe he hG (hw.2 hval.symm)
          | true => exact peelThreadHead_wp fuel true pt ht hG (hw.1 hval.symm)
        | var _ => exact ⟨_, _, .jnz hc ht he, hG, hw⟩
      all_goals exact ⟨_, _, hwf0, hG, hw⟩
    | _ => exact ⟨_, _, hwf, hG, hw⟩

theorem rewriteCTInline_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (Arg (CTOptV Val)) Val} {D : Ctx (CTLabel Val Cont rs) Cont}
    {e₂ : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs} {e₃ : Expr Val Cont rs}
    (hwf : Wf G D e₂ e₃) :
    ∀ {G_s : Ctx (Arg (CTOptV Val)) (Arg (CTOptV Val))}
      {D_s : Ctx (CTLabel Val Cont rs) (CTLabel Val Cont rs)}
      {e_chk : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs}
      (_hwf_s : Wf G_s D_s e_chk e₂)
      {budget : Nat} {p : CTPlan} {n : Nat},
      validateInline budget p e_chk = some n →
      (∀ q ∈ G_s, ArgShapeEq q.2.1 q.2.2) → CTDSim D_s →
      OptValCtx G → CTWpD Γ Q X D →
      ∀ m, wp Γ Q X e₃ m → wp Γ Q X (rewriteCTInline p e₂) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m hw3
    rcases hwf_s.rhs_let with ⟨op_chk, k_chk, rfl, hop_s, hk_s⟩
    cases hop with
    | mk code hargs =>
      cases hop_s with
      | mk code_s hargs_s =>
        cases budget with
        | zero => cases p <;> simp [validateInline] at hval
        | succ b =>
          cases p with
          | node1 pk =>
            have hel := evalThreadLet?_shape code (trel_flattenArgs_shape hGs hargs_s)
            dsimp only [validateInline] at hval
            dsimp only [rewriteCTInline]
            rcases hel with ⟨he₁, he₂⟩ | ⟨o₁, o₂, he₁, he₂, ho⟩
            · rw [he₁] at hval; rw [he₂]
              obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
              rw [hra]
              cases hsub : validateInline b pk (k_chk (noneArgTup _)) with
              | none => rw [hsub] at hval; simp at hval
              | some n' =>
                dsimp only [wp, Op.wp] at hw3 ⊢
                rw [← hvals] at hw3
                exact OpCode.wp_mono code _ (fun r hr =>
                  ih (toOptArgTup r) r (hk_s (noneArgTup _) (toOptArgTup r)) hsub
                    (fun p hp =>
                      (List.mem_append.1 hp).elim (none_toOptArgTup_shape_zip r p) (hGs p))
                    hDs (OptValCtx.of_toOptArgTup hG r) hD m hr) hw3
            · rw [he₁] at hval; rw [he₂]
              obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
              obtain ⟨rout, hrout, hkw⟩ := evalThreadLet?_opt_wp code hra hvals he₂ hw3
              exact ih o₂ (vals rout) (hk_s o₁ o₂) hval
                (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip ho p) (hGs p))
                hDs (OptValCtx.of_toRealArgs? hG hrout) hD m hkw
          | _ => simp [validateInline] at hval
  | load t ha _ ih =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m ⟨v, hv, hw3⟩
    rcases hwf_s.rhs_load with ⟨a_chk, k_chk, rfl, ha_s, hk_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ b =>
      cases p with
      | node1 pk =>
        obtain ⟨ra, hra, hval'⟩ := hG.flattenArg ha
        dsimp only [validateInline] at hval
        cases hsub : validateInline b pk (k_chk (.var none)) with
        | none => rw [hsub] at hval; simp at hval
        | some n' =>
          dsimp only [rewriteCTInline, wp]
          rw [hra]; dsimp only [wp]; rw [hval']
          exact ⟨v, hv, ih (.var (some v)) v (hk_s (.var none) (.var (some v))) hsub
            (fun p hp => by cases hp with | head => rfl | tail _ hp' => exact hGs p hp')
            hDs (hG.cons_var v) hD m hw3⟩
      | _ => simp [validateInline] at hval
  | store hv ha _ ih =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m ⟨hok, hw3⟩
    rcases hwf_s.rhs_store with ⟨v_chk, a_chk, k_chk, rfl, hv_s, ha_s, hk_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ b =>
      cases p with
      | node1 pk =>
        obtain ⟨rv, hrv, hvalv⟩ := hG.flattenArg hv
        obtain ⟨ra, hra, hvala⟩ := hG.flattenArg ha
        dsimp only [validateInline] at hval
        cases hsub : validateInline b pk k_chk with
        | none => rw [hsub] at hval; simp at hval
        | some n' =>
          dsimp only [rewriteCTInline, wp]
          rw [hrv, hra]; dsimp only [wp]; rw [hvalv, hvala]
          exact ⟨hok, ih hk_s hsub hGs hDs hG hD _ hw3⟩
      | _ => simp [validateInline] at hval
  | call f hargs _ ih =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m ⟨P, E, hΓ, hP, hE⟩
    rcases hwf_s.rhs_call with ⟨args_chk, k_chk, rfl, hargs_s, hk_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ b =>
      cases p with
      | node1 pk =>
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
        dsimp only [validateInline] at hval
        cases hsub : validateInline b pk (k_chk (noneArgTup _)) with
        | none => rw [hsub] at hval; simp at hval
        | some n' =>
          dsimp only [rewriteCTInline, wp]
          rw [hra]; dsimp only [wp]; rw [hvals]
          exact ⟨P, E, hΓ, fun r m' hr =>
            ih (toOptArgTup r) r (hk_s (noneArgTup _) (toOptArgTup r)) hsub
              (fun p hp => (List.mem_append.1 hp).elim (none_toOptArgTup_shape_zip r p) (hGs p))
              hDs (OptValCtx.of_toOptArgTup hG r) hD m' (hP r m' hr), hE⟩
      | _ => simp [validateInline] at hval
  | jnz hc _ _ iht ihe =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m hw3
    rcases hwf_s.rhs_jnz with ⟨c_chk, t_chk, e_chk', rfl, hc_s, ht_s, he_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ b =>
      cases p with
      | node2 pt pe =>
        have hsh := ArgShapeEq.flattenArg hGs hc_s
        obtain ⟨rc, hrc, hvalc⟩ := hG.flattenArg hc
        dsimp only [validateInline] at hval
        dsimp only [rewriteCTInline]
        cases e₁ : flattenArg c_chk <;> cases e₂ : flattenArg _ <;>
          rw [e₁, e₂] at hsh <;> rw [e₁] at hval <;> rw [e₂] at hrc
        · rename_i ov
          cases ov with
          | none => dsimp only [toRealArg?] at hrc; cases hrc
          | some v =>
            dsimp only [toRealArg?] at hrc
            have hvc := (congrArg Arg.val (Option.some.inj hrc)).trans hvalc
            dsimp only [Bind.bind, Option.bind] at hval
            cases ht : validateInline b pt t_chk <;> rw [ht] at hval <;> simp at hval
            cases he : validateInline (b - _) pe e_chk' <;> rw [he] at hval <;> simp at hval
            dsimp only [wp]
            exact ⟨fun hvt => iht ht_s ht hGs hDs hG hD m (hw3.1 (hvc ▸ hvt)),
                   fun hvf => ihe he_s he hGs hDs hG hD m (hw3.2 (hvc ▸ hvf))⟩
        · dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
        · dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
        · rename_i b₁ b₂
          dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
          dsimp only [toRealArg?] at hrc; cases hrc
          first
          | (cases b₁
             · exact ihe he_s hval hGs hDs hG hD m (hw3.2 hvalc.symm)
             · exact iht ht_s hval hGs hDs hG hD m (hw3.1 hvalc.symm))
          | (cases b₂
             · exact ihe he_s hval hGs hDs hG hD m (hw3.2 hvalc.symm)
             · exact iht ht_s hval hGs hDs hG hD m (hw3.1 hvalc.symm))
      | _ => simp [validateInline] at hval
  | jump hj hargs =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG hD m hw3
    rcases hwf_s.rhs_jump with ⟨j_chk, args_chk, rfl, hj_s, hargs_s⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ _ =>
      cases p with
      | jump _ =>
        obtain ⟨hts, hsinl⟩ := hDs _ hj_s
        have hfa := trel_flattenArgs_shape hGs hargs_s
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
        dsimp only [validateInline] at hval
        rw [hts.canEmit_eq hfa, hsinl _ _ hfa] at hval
        dsimp only [rewriteCTInline]
        split
        · rename_i hcan
          exact (hD _ hj).1 _ ra m hra hcan (by simpa [wp, hvals] using hw3)
        · rename_i hnocan
          rw [Bool.eq_false_iff.2 hnocan, Bool.false_or] at hval
          split at hval
          · rename_i hsome
            rcases Option.isSome_iff_exists.1 hsome with ⟨e_out, heout⟩
            rw [heout]
            exact (hD _ hj).2 _ ra e_out m heout hra (by simpa [wp, hvals] using hw3)
          · cases hval
      | _ => simp [validateInline] at hval
  | ret hvs =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG _ m hw3
    rcases hwf_s.rhs_ret with ⟨_, rfl, _⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ _ =>
      cases p with
      | leaf =>
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hvs
        dsimp only [rewriteCTInline, wp]; rw [hra]; dsimp only [wp]; rw [hvals]; exact hw3
      | _ => simp [validateInline] at hval
  | exit f hargs =>
    intro G_s D_s e_chk hwf_s budget p n hval hGs hDs hG _ m hw3
    rcases hwf_s.rhs_exit with ⟨_, rfl, _⟩
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ _ =>
      cases p with
      | leaf =>
        obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
        dsimp only [rewriteCTInline, wp]; rw [hra]; dsimp only [wp]; rw [hvals]; exact hw3
      | _ => simp [validateInline] at hval
  | hlt =>
    intro G_s D_s e_chk hwf_s budget p n hval _ _ _ _ m hw3
    rcases hwf_s.rhs_hlt with rfl
    cases budget with
    | zero => cases p <;> simp [validateInline] at hval
    | succ _ =>
      cases p with
      | leaf => exact hw3
      | _ => simp [validateInline] at hval
  | group _ _ _ _ =>
    intro _ _ _ hwf_s budget p _ hval
    rcases hwf_s.rhs_group with ⟨_, _, rfl, _, _⟩
    cases budget <;> cases p <;> simp [validateInline] at hval

private theorem attachInlines_get_inline_some {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs : Blocks (Arg (CTOptV V)) (CTLabel V L rs) rs sig) →
    (ls : Tup (CTLabel V L rs) sig) →
    ∀ {ts} (i : Member ts sig) a e_out,
      (ls.get i).inline? a = none →
      ((attachInlines acts pbs bs ls).get i).inline? a = some e_out →
      ∃ pb budget,
        let r := peelThreadHead 4 false pb ((bs.get i) a)
        (validateInline budget r.2.1 r.2.2).isSome = true ∧
        e_out = rewriteCTInline r.2.1 r.2.2
  | a :: acts, .cons pb pbs, _ :: _, .cons b bs, (l, ls), _, .here, arg, e_out, hno, he => by
    simp only [attachInlines, Tup.get] at he hno
    cases a with
    | keep _ allow =>
      cases allow with
      | false =>
        dsimp only [tryMakeInlineLabel] at he
        rw [hno] at he; cases he
      | true =>
        dsimp only [tryMakeInlineLabel] at he
        by_cases hvs : (validateInline (if (peelThreadHead 4 false pb (b arg)).1 then 8 else 3)
            (peelThreadHead 4 false pb (b arg)).2.1
            (peelThreadHead 4 false pb (b arg)).2.2).isSome = true
        · simp only [hvs, ↓reduceIte, Option.some.injEq] at he
          cases he
          exact ⟨pb, _, hvs, rfl⟩
        · simp only [hvs, Bool.false_eq_true, ↓reduceIte] at he
          cases he
    | splitBool _ _ _ _ inlT inlF =>
      dsimp only [tryMakeInlineLabel] at he
      by_cases hinl : (inlT || inlF) = true
      · simp only [hinl, ↓reduceIte] at he
        by_cases hc : ((peelThreadHead 4 false pb (b arg)).1 &&
            (validateInline 8 (peelThreadHead 4 false pb (b arg)).2.1
              (peelThreadHead 4 false pb (b arg)).2.2).isSome) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at he
          simp only [Bool.and_eq_true] at hc
          cases he
          exact ⟨pb, 8, hc.2, rfl⟩
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at he
          cases he
      · simp only [hinl, Bool.false_eq_true, ↓reduceIte] at he
        rw [hno] at he; cases he
  | _ :: acts, .cons pb pbs, _ :: _, .cons _ bs, (_, ls), _, .there i, arg, e_out, hno, he =>
    attachInlines_get_inline_some acts pbs bs ls i arg e_out hno he
  | [], _, _ :: _, .cons _ bs, (l, ls), _, .here, arg, _, hno, he => by
    simp only [attachInlines, Tup.get] at he hno
    rw [hno] at he; cases he
  | [], _, _ :: _, .cons _ bs, (_, ls), _, .there i, arg, e_out, hno, he =>
    attachInlines_get_inline_some [] .nil bs ls i arg e_out hno he
  | _ :: _, .nil, _ :: _, .cons _ bs, (l, ls), _, .here, arg, _, hno, he => by
    simp only [attachInlines, Tup.get] at he hno
    rw [hno] at he; cases he
  | _ :: _, .nil, _ :: _, .cons _ bs, (_, ls), _, .there i, arg, e_out, hno, he =>
    attachInlines_get_inline_some [] .nil bs ls i arg e_out hno he

private theorem closed_blocksAppend_splitLabelTup (Γ : Env) {rs : List Ty} (Q : Post rs)
    (X : XPost) :
    (s₁ s₂ : List (List Ty)) → (bs₁ : Blocks Val Cont rs s₁) → (bs₂ : Blocks Val Cont rs s₂) →
    (Js : Tup Cont (s₁ ++ s₂)) →
    Closed Γ Q X (blocksAppend bs₁ bs₂) Js →
    Closed Γ Q X bs₁ (splitLabelTup s₁ s₂ Js).1 ∧ Closed Γ Q X bs₂ (splitLabelTup s₁ s₂ Js).2
  | [], _, .nil, _, Js, hcl => ⟨trivial, hcl⟩
  | _ :: s₁, s₂, .cons _ bs₁, bs₂, (j, Js), hcl => by
    rcases hcl with ⟨hb, htl⟩
    have hrest := closed_blocksAppend_splitLabelTup Γ Q X s₁ s₂ bs₁ bs₂ Js htl
    exact ⟨⟨hb, hrest.1⟩, hrest.2⟩

private theorem condConsBlock_closed (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (b : Bool) (blk : Unit → Tup Val ts → Expr Val Cont rs) {rest : List (List Ty)}
    (tl : Blocks Val Cont rs rest) (js : Tup Cont ((if b then [ts] else []) ++ rest))
    (hcl : Closed Γ Q X (condConsBlock b blk tl) js) :
    (∀ j' (_h : (splitOptLabel b js).1 = some j') xs m, wp Γ Q X (blk () xs) m → j' xs m) ∧
      Closed Γ Q X tl (splitOptLabel b js).2 := by
  cases b
  · exact ⟨(fun _ h => by cases h), hcl⟩
  · exact ⟨fun _ h xs m hw => by cases h; exact hcl.1 xs m hw, hcl.2⟩

private theorem ArgShapeEq.refl_mem_zip {V : Ty → Type} :
    {ts : List Ty} → (a : Tup (Arg (CTOptV V)) ts) →
    ∀ p ∈ Tup.zip a a, ArgShapeEq p.2.1 p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, as), _, hp => by
    cases hp with
    | head => rfl
    | tail _ hp' => exact ArgShapeEq.refl_mem_zip as _ hp'

private theorem splitOptLabel_true_of_some {L : List Ty → Type} {ts : List Ty} {b : Bool}
    {rest : List (List Ty)} {js : Tup L ((if b then [ts] else []) ++ rest)} {j : L ts}
    (h : (splitOptLabel b js).1 = some j) : b = true := by
  cases b <;> simp [splitOptLabel] at h ⊢

private theorem splitBool_head_target (Γ : Env) {rs ts : List Ty} (Q : Post rs) (X : XPost)
    (keepT keepF keepDisp : Bool) (sp : Option (Member .bool ts))
    (headJs : Tup Cont (splitMemberSig ts keepT keepF keepDisp sp))
    (rwId : Tup Val ts → Expr Val Cont rs)
    (rwSplit : (mem : Member .bool ts) → Bool → Tup Val (eraseMem mem) → Expr Val Cont rs)
    (hact : ∀ mem, sp = some mem → (!keepDisp || (keepT && keepF)) = true)
    (hcl : Closed Γ Q X (mkSplitCurBlocks keepT keepF keepDisp
      (CTLabel.noInline (mkSplitTarget ts keepT keepF keepDisp sp headJs)) rwId rwSplit sp) headJs)
    (xs : Tup Val ts) (m : Mem 64)
    (hId : sp = none → wp Γ Q X (rwId xs) m)
    (hSp : ∀ (mem : Member .bool ts), sp = some mem →
      (keepT = true → getTupMem mem xs = true → wp Γ Q X (rwSplit mem true (dropTupMem mem xs)) m) ∧
      (keepF = true → getTupMem mem xs = false → wp Γ Q X (rwSplit mem false (dropTupMem mem xs))
          m)) :
    ctSrcTargetPred (mkSplitTarget (V := Val) ts keepT keepF keepDisp sp headJs) xs m := by
  cases sp with
  | none =>
    dsimp only [mkSplitTarget, mkSplitCurBlocks, ctSrcTargetPred] at hcl ⊢
    exact hcl.1 xs m (hId rfl)
  | some mem =>
    revert headJs hact hcl hSp
    cases keepDisp with
    | false =>
      intro headJs _ hcl hSp
      dsimp only [mkSplitTarget, mkSplitCurBlocks, mkSplitBlocks,
        ctSrcTargetPred, splitOptLabel] at hcl ⊢
      have hD_cl := condConsBlock_closed Γ Q X false _ _ _ hcl
      have hT_cl := condConsBlock_closed Γ Q X keepT _ _ _ hD_cl.2
      have hF_cl := condConsBlock_closed Γ Q X keepF _ _ _ hT_cl.2
      have hT_ok : getTupMem mem xs = true →
          match (splitOptLabel keepT headJs).1 with
          | some jT => jT (dropTupMem mem xs) m
          | none => True := by
        intro hget
        cases hkj : (splitOptLabel keepT headJs).1 with
        | none => trivial
        | some jT =>
          have hkt := splitOptLabel_true_of_some hkj
          exact hT_cl.1 jT hkj (dropTupMem mem xs) m ((hSp mem rfl).1 hkt hget)
      have hF_ok : getTupMem mem xs = false →
          match (splitOptLabel keepF (splitOptLabel keepT headJs).2).1 with
          | some jF => jF (dropTupMem mem xs) m
          | none => True := by
        intro hget
        cases hkj : (splitOptLabel keepF (splitOptLabel keepT headJs).2).1 with
        | none => trivial
        | some jF =>
          have hkf := splitOptLabel_true_of_some hkj
          exact hF_cl.1 jF hkj (dropTupMem mem xs) m ((hSp mem rfl).2 hkf hget)
      exact ⟨trivial, hT_ok, hF_ok⟩
    | true =>
      intro headJs hact hcl hSp
      have hact' := hact mem rfl
      simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hact'
      rcases hact' with ⟨rfl, rfl⟩
      dsimp only [mkSplitTarget, mkSplitCurBlocks, mkSplitBlocks, condConsBlock,
        ctSrcTargetPred, splitOptLabel] at hcl ⊢
      rcases headJs with ⟨jD, jT, jF, _⟩
      rcases hcl with ⟨hD, hT, hF, _⟩
      have hT_ok : getTupMem mem xs = true → jT (dropTupMem mem xs) m :=
        fun hget => hT _ _ ((hSp mem rfl).1 rfl hget)
      have hF_ok : getTupMem mem xs = false → jF (dropTupMem mem xs) m :=
        fun hget => hF _ _ ((hSp mem rfl).2 rfl hget)
      have hdisp_wp : wp Γ Q X (.jnz (.var (getTupMem mem xs))
          (.jump jT (dropTupMem mem (toArgTup xs)))
          (.jump jF (dropTupMem mem (toArgTup xs)))) m := by
        dsimp only [wp]
        refine ⟨fun ht => ?_, fun hf => ?_⟩
        · have := hT_ok ht; rwa [dropTupMem_toArgTup, toArgTup_vals]
        · have := hF_ok hf; rwa [dropTupMem_toArgTup, toArgTup_vals]
      exact ⟨hD _ _ hdisp_wp, hT_ok, hF_ok⟩

private theorem validateAct_splitBool_goal {ts : List Ty} {p : Nat} {keepT keepF keepDisp inlT inlF
    : Bool}
    (h : validateAct ts (.splitBool p keepT keepF keepDisp inlT inlF) = true) :
    ∀ m, splitMember? p ts = some m → (!keepDisp || (keepT && keepF)) = true := by
  intro m hm; dsimp only [validateAct] at h; rwa [hm] at h

private theorem ctSrcConts_closed_targets (Γ : Env) {rs : List Ty} (Q : Post rs) (X : XPost) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bk : Blocks (Arg (CTOptV UnitV)) (ValidL rs) rs sig) →
    (b₂ : Blocks (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs sig) →
    (b₃ : Blocks Val Cont rs sig) →
    (Js_out : Tup Cont (threadSig acts sig)) →
    (lsNo lsBody : Tup (CTLabel Val Cont rs) sig) →
    TargetsEq lsNo lsBody →
    lsNo = buildTargets acts sig Js_out →
    validateCTBlocks acts pbs bk = true →
    Closed Γ Q X (rewriteCTBlocks acts pbs b₂ lsNo) Js_out →
    (∀ {ts} (i : Member ts sig) pb (ak : Tup (Arg (CTOptV UnitV)) ts)
        (a₂ : Tup (Arg (CTOptV Val)) ts) (xs : Tup Val ts),
      TRel (fun _ => ArgShapeEq) ak a₂ →
      (∀ q ∈ Tup.zip a₂ xs, ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2) →
      validateCTPlan pb (bk.get i ak) = true →
      ∀ m, wp Γ Q X (b₃.get i xs) m → wp Γ Q X (rewriteCTAux pb (b₂.get i a₂)) m) →
    ∀ {ts} (i : Member ts sig) xs m,
      wp Γ Q X (b₃.get i xs) m → ctSrcTargetPred (lsBody.get i).target xs m
  | [], .nil, [], .nil, .nil, .nil, (), (), (), _, _, _, _, _, _, i => nomatch i
  | [], .cons _ _, [], .nil, .nil, .nil, _, _, _, _, _, _, _, _, _, i => nomatch i
  | _ :: _, pbs, [], .nil, .nil, .nil, _, _, _, _, _, hval, _, _, _, _ => by
    cases pbs <;> simp [validateCTBlocks] at hval
  | [], pbs, _ :: _, .cons _ _, .cons _ _, .cons _ _, _, _, _, _, _, hval, _, _, _, _ => by
    cases pbs <;> simp [validateCTBlocks] at hval
  | _ :: _, .nil, _ :: _, .cons _ _, .cons _ _, .cons _ _, _, _, _, _, _, hval, _, _, _, _ => by
    simp [validateCTBlocks] at hval
  | a :: acts, .cons pb pbs, ts :: _, .cons bkh bkt, .cons b₂h b₂t, .cons _ b₃t, Js_out,
      (lno, lsNo), (lb, lsBody), ⟨hteq, hteqs⟩, hbt, hval, hcl, hblk, _, i => by
    intro xs m hw3
    unfold validateCTBlocks at hval
    simp only [Bool.and_eq_true] at hval
    rcases hval with ⟨⟨hact, hbody⟩, hvaltl⟩
    dsimp only [buildTargets] at hbt
    simp only [Prod.mk.injEq] at hbt
    rcases hbt with ⟨rfl, hls⟩
    unfold rewriteCTBlocks at hcl
    have hsp := closed_blocksAppend_splitLabelTup Γ Q X _ _ _ _ _ hcl
    cases i with
    | here =>
      change ctSrcTargetPred lb.target xs m
      rw [← hteq]
      cases a with
      | keep kb _ =>
        cases kb with
        | false => trivial
        | true =>
          dsimp only [CTLabel.noInline, mkActTarget, ctSrcTargetPred]
          have hw2 := hblk .here pb _ _ xs
            (TRel.mono (fun _ _ _ h => h.shape) (toOptArgTup_trel (Tup.units ts) xs))
            (fun q hq => OptValCtx.of_toOptArgTup (G := []) (fun _ h => by cases h) xs q
              (List.mem_append_left [] hq))
            hbody m hw3
          exact hsp.1.1 xs m hw2
      | splitBool p keepT keepF keepDisp _ _ =>
        dsimp only [CTLabel.noInline, mkActTarget]
        refine splitBool_head_target Γ Q X keepT keepF keepDisp (splitMember? p ts)
          (splitLabelTup _ _ Js_out).1
          (fun xs' => rewriteCTAux pb (b₂h (toOptArgTup xs')))
          (fun mem bVal xs' =>
            rewriteCTAux pb (b₂h (insertTupMem mem (.imm bVal) (toOptArgTup xs'))))
          (validateAct_splitBool_goal hact) hsp.1 xs m ?_ ?_
        · intro hmem
          dsimp only at hbody
          simp only [hmem] at hbody
          exact hblk .here pb _ _ xs
            (TRel.mono (fun _ _ _ h => h.shape) (toOptArgTup_trel (Tup.units ts) xs))
            (fun q hq => OptValCtx.of_toOptArgTup (G := []) (fun _ h => by cases h) xs q
              (List.mem_append_left [] hq))
            hbody m hw3
        · intro mem hmem
          dsimp only at hbody
          simp only [hmem, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hbody
          refine ⟨fun hkeepT hget => ?_, fun hkeepF hget => ?_⟩
          · have hbt' : validateCTPlan pb (bkh (insertTupMem mem (.imm true)
                (toOptArgTup (Tup.units (eraseMem mem))))) = true := by
              rcases hbody.1 with hc | hc
              · rw [hkeepT] at hc; cases hc
              · exact hc
            have hsh : TRel (fun _ => ArgShapeEq)
                (insertTupMem mem (.imm true) (toOptArgTup (Tup.units (eraseMem mem))))
                (insertTupMem mem (.imm true) (toOptArgTup (dropTupMem mem xs))) :=
              trel_insertTupMem mem rfl (TRel.mono (fun _ _ _ h => h.shape)
                (toOptArgTup_trel _ _))
            have hopt :
                ∀ q ∈ Tup.zip (insertTupMem mem (.imm true) (toOptArgTup (dropTupMem mem xs))) xs,
                ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2 := by
              have heqxs : insertTupMem mem true (dropTupMem mem xs) = xs := by
                rw [← hget, insertTupMem_get_drop]
              have hopt0 := OptValCtx.tup_insertTupMem mem true (dropTupMem mem xs)
              rwa [heqxs] at hopt0
            exact hblk .here pb _ _ xs hsh hopt hbt' m hw3
          · have hbf' : validateCTPlan pb (bkh (insertTupMem mem (.imm false)
                (toOptArgTup (Tup.units (eraseMem mem))))) = true := by
              rcases hbody.2 with hc | hc
              · rw [hkeepF] at hc; cases hc
              · exact hc
            have hsh : TRel (fun _ => ArgShapeEq)
                (insertTupMem mem (.imm false) (toOptArgTup (Tup.units (eraseMem mem))))
                (insertTupMem mem (.imm false) (toOptArgTup (dropTupMem mem xs))) :=
              trel_insertTupMem mem rfl (TRel.mono (fun _ _ _ h => h.shape)
                (toOptArgTup_trel _ _))
            have hopt :
                ∀ q ∈ Tup.zip (insertTupMem mem (.imm false) (toOptArgTup (dropTupMem mem xs))) xs,
                ∃ ra : Arg Val q.1, toRealArg? q.2.1 = some ra ∧ ra.val = q.2.2 := by
              have heqxs : insertTupMem mem false (dropTupMem mem xs) = xs := by
                rw [← hget, insertTupMem_get_drop]
              have hopt0 := OptValCtx.tup_insertTupMem mem false (dropTupMem mem xs)
              rwa [heqxs] at hopt0
            exact hblk .here pb _ _ xs hsh hopt hbf' m hw3
    | there i =>
      exact ctSrcConts_closed_targets Γ Q X acts pbs bkt b₂t b₃t (splitLabelTup _ _ Js_out).2
        lsNo lsBody hteqs hls hvaltl hsp.2 (fun j => hblk (.there j)) i xs m hw3

theorem rewriteCTAux_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (Arg (CTOptV Val)) Val} {D : Ctx (CTLabel Val Cont rs) Cont}
    {e₂ : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs} {e₃ : Expr Val Cont rs}
    (hwf : Wf G D e₂ e₃) :
    ∀ {Gk : Ctx (Arg (CTOptV UnitV)) (Arg (CTOptV Val))}
      {Dk : Ctx (ValidL rs) (CTLabel Val Cont rs)}
      {ek : Expr (Arg (CTOptV UnitV)) (ValidL rs) rs} (_hwk : Wf Gk Dk ek e₂)
      {G_s : Ctx (Arg (CTOptV Val)) (Arg (CTOptV Val))}
      {D_s : Ctx (CTLabel Val Cont rs) (CTLabel Val Cont rs)}
      {e_s : Expr (Arg (CTOptV Val)) (CTLabel Val Cont rs) rs} (_hwf_s : Wf G_s D_s e_s e₂)
      (plan : CTPlan) (_hval : validateCTPlan plan ek = true),
      (∀ q ∈ Gk, ArgShapeEq q.2.1 q.2.2) → CTDSim Dk →
      (∀ q ∈ G_s, ArgShapeEq q.2.1 q.2.2) → CTDSim D_s →
      OptValCtx G → CTWpD Γ Q X D →
      ∀ m, wp Γ Q X e₃ m → wp Γ Q X (rewriteCTAux plan e₂) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m hw3
    rcases hwk.rhs_let with ⟨op_k, k_k, rfl, hop_k, hk_k⟩
    rcases hwf_s.rhs_let with ⟨op_s, k_s, rfl, hop_s, hk_s⟩
    cases hop with
    | mk code hargs =>
      cases hop_k with
      | mk _ hargs_k =>
        cases hop_s with
        | mk _ hargs_s =>
          cases plan with
          | node1 pk =>
            have helk := evalThreadLet?_shape code (trel_flattenArgs_shape hGk hargs_k)
            have hels := evalThreadLet?_shape code (trel_flattenArgs_shape hGs hargs_s)
            dsimp only [validateCTPlan] at hval
            dsimp only [rewriteCTAux]
            rcases helk with ⟨hek, he₂⟩ | ⟨ok, o₂, hek, he₂, hok⟩
            · rw [hek] at hval; rw [he₂]
              rcases hels with ⟨_, he₂'⟩ | ⟨os, o₂', _, he₂', _⟩
              · obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
                rw [hra]
                dsimp only [wp, Op.wp] at hw3 ⊢
                rw [← hvals] at hw3
                exact OpCode.wp_mono code _ (fun r hr =>
                  ih (toOptArgTup r) r (hk_k (toOptArgTup (Tup.units _)) (toOptArgTup r))
                    (hk_s (toOptArgTup r) (toOptArgTup r)) pk hval
                    (fun p hp => (List.mem_append.1 hp).elim (toOptArgTup_shape_zip _ _ p) (hGk p))
                    hDk
                    (fun p hp => (List.mem_append.1 hp).elim (toOptArgTup_shape_zip _ _ p) (hGs p))
                    hDs (OptValCtx.of_toOptArgTup hG r) hD m hr) hw3
              · rw [he₂] at he₂'; cases he₂'
            · rw [hek] at hval; rw [he₂]
              rcases hels with ⟨_, he₂'⟩ | ⟨os, o₂', _, he₂', hos⟩
              · rw [he₂] at he₂'; cases he₂'
              · rw [he₂] at he₂'; cases he₂'
                obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
                obtain ⟨rout, hrout, hkw⟩ := evalThreadLet?_opt_wp code hra hvals he₂ hw3
                exact ih o₂ (vals rout) (hk_k ok o₂) (hk_s os o₂) pk hval
                  (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip hok p) (hGk p))
                  hDk
                  (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip hos p) (hGs p))
                  hDs (OptValCtx.of_toRealArgs? hG hrout) hD m hkw
          | _ => dsimp only [validateCTPlan] at hval; cases hval
  | load t ha _ ih =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m ⟨v, hv, hw3⟩
    rcases hwk.rhs_load with ⟨_, k_k, rfl, _, hk_k⟩
    rcases hwf_s.rhs_load with ⟨_, k_s, rfl, _, hk_s⟩
    cases plan with
    | node1 pk =>
      obtain ⟨ra, hra, hval'⟩ := hG.flattenArg ha
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux]
      rw [hra]; dsimp only [wp]; rw [hval']
      exact ⟨v, hv, ih (.var (some v)) v (hk_k (.var (some ())) (.var (some v)))
        (hk_s (.var (some v)) (.var (some v))) pk hval
        (fun p hp => by cases hp with | head => rfl | tail _ hp' => exact hGk p hp') hDk
        (fun p hp => by cases hp with | head => rfl | tail _ hp' => exact hGs p hp') hDs
        (hG.cons_var v) hD m hw3⟩
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | store hv ha _ ih =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m ⟨hok, hw3⟩
    rcases hwk.rhs_store with ⟨_, _, k_k, rfl, _, _, hk_k⟩
    rcases hwf_s.rhs_store with ⟨_, _, k_s, rfl, _, _, hk_s⟩
    cases plan with
    | node1 pk =>
      obtain ⟨rv, hrv, hvalv⟩ := hG.flattenArg hv
      obtain ⟨ra, hra, hvala⟩ := hG.flattenArg ha
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux]
      rw [hrv, hra]; dsimp only [wp]; rw [hvalv, hvala]
      exact ⟨hok, ih hk_k hk_s pk hval hGk hDk hGs hDs hG hD _ hw3⟩
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | call f hargs _ ih =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m ⟨P, E, hΓ, hP, hE⟩
    rcases hwk.rhs_call with ⟨_, k_k, rfl, _, hk_k⟩
    rcases hwf_s.rhs_call with ⟨_, k_s, rfl, _, hk_s⟩
    cases plan with
    | node1 pk =>
      obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux]
      rw [hra]; dsimp only [wp]; rw [hvals]
      exact ⟨P, E, hΓ, fun r m' hr =>
        ih (toOptArgTup r) r (hk_k (toOptArgTup (Tup.units _)) (toOptArgTup r))
          (hk_s (toOptArgTup r) (toOptArgTup r)) pk hval
          (fun p hp => (List.mem_append.1 hp).elim (toOptArgTup_shape_zip _ _ p) (hGk p)) hDk
          (fun p hp => (List.mem_append.1 hp).elim (toOptArgTup_shape_zip _ _ p) (hGs p)) hDs
          (OptValCtx.of_toOptArgTup hG r) hD m' (hP r m' hr), hE⟩
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | jnz hc _ _ iht ihe =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m hw3
    rcases hwk.rhs_jnz with ⟨c_k, t_k, e_k, rfl, hc_k, ht_k, he_k⟩
    rcases hwf_s.rhs_jnz with ⟨c_s, t_s, e_s', rfl, hc_s, ht_s, he_s⟩
    cases plan with
    | node2 pt pe =>
      have hsh := ArgShapeEq.flattenArg hGk hc_k
      obtain ⟨rc, hrc, hvalc⟩ := hG.flattenArg hc
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux]
      cases e₁ : flattenArg c_k <;> cases e₂ : flattenArg _ <;>
        rw [e₁, e₂] at hsh <;> rw [e₁] at hval <;> rw [e₂] at hrc
      · rename_i ov
        cases ov with
        | none => dsimp only [toRealArg?] at hrc; cases hrc
        | some v =>
          dsimp only [toRealArg?] at hrc
          have hvc := (congrArg Arg.val (Option.some.inj hrc)).trans hvalc
          simp only [Bool.and_eq_true] at hval
          dsimp only [wp]
          exact ⟨fun hvt => iht ht_k ht_s pt hval.1 hGk hDk hGs hDs hG hD m (hw3.1 (hvc ▸ hvt)),
                 fun hvf => ihe he_k he_s pe hval.2 hGk hDk hGs hDs hG hD m (hw3.2 (hvc ▸ hvf))⟩
      · dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
      · dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
      · rename_i b₁ b₂
        dsimp only [ArgShapeEq, Arg.imm?] at hsh; cases hsh
        dsimp only [toRealArg?] at hrc; cases hrc
        cases b₁
        · exact ihe he_k he_s pe hval hGk hDk hGs hDs hG hD m (hw3.2 hvalc.symm)
        · exact iht ht_k ht_s pt hval hGk hDk hGs hDs hG hD m (hw3.1 hvalc.symm)
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | jump hj hargs =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk _ _ hG hD m hw3
    rcases hwk.rhs_jump with ⟨j_k, args_k, rfl, hj_k, hargs_k⟩
    cases plan with
    | jump tryInl =>
      obtain ⟨hts, hsinl⟩ := hDk _ hj_k
      have hfa := trel_flattenArgs_shape hGk hargs_k
      obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
      have hcan := hts.canEmit_eq hfa
      have his := hsinl _ _ hfa
      dsimp only [validateCTPlan] at hval
      dsimp only [rewriteCTAux, CTLabel.emitJump]
      cases tryInl
      · simp only [Bool.false_eq_true, ↓reduceIte] at hval ⊢
        rw [hcan] at hval
        exact (hD _ hj).1 _ ra m hra hval (by simpa [wp, hvals] using hw3)
      · simp only [↓reduceIte] at hval ⊢
        cases he_k : j_k.inline? (flattenArgs args_k) <;>
          cases he_2 : CTLabel.inline? _ (flattenArgs _) <;>
          rw [he_k] at hval his <;> rw [he_2] at his
        · rw [hcan] at hval
          exact (hD _ hj).1 _ ra m hra hval (by simpa [wp, hvals] using hw3)
        · simp at his
        · simp at his
        · exact (hD _ hj).2 _ ra _ m he_2 hra (by simpa [wp, hvals] using hw3)
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | ret hvs =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval _ _ _ _ hG _ m hw3
    rcases hwk.rhs_ret with ⟨_, rfl, _⟩
    cases plan with
    | leaf =>
      obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hvs
      dsimp only [rewriteCTAux]; rw [hra]; dsimp only [wp]; rw [hvals]; exact hw3
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | exit f hargs =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval _ _ _ _ hG _ m hw3
    rcases hwk.rhs_exit with ⟨_, rfl, _⟩
    cases plan with
    | leaf =>
      obtain ⟨ra, hra, hvals⟩ := trel_toRealArgs?_flattenArgs_wp hG hargs
      dsimp only [rewriteCTAux]; rw [hra]; dsimp only [wp]; rw [hvals]; exact hw3
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | hlt =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval _ _ _ _ _ _ m hw3
    rcases hwk.rhs_hlt with rfl
    cases plan with
    | leaf => exact hw3
    | _ => dsimp only [validateCTPlan] at hval; cases hval
  | @group G D sig b₂ b₃ k₂ k₃ hb _ ihb ihk =>
    intro Gk Dk ek hwk G_s D_s e_s hwf_s plan hval hGk hDk hGs hDs hG hD m hw3
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    rcases hwf_s.rhs_group with ⟨bs, ks, rfl, hbs, hks⟩
    cases plan with
    | group acts pbs pk =>
      dsimp only [validateCTPlan] at hval
      simp only [Bool.and_eq_true] at hval
      rcases hval with ⟨hvalb, hvalk⟩
      dsimp only [rewriteCTAux, wp]
      intro Js_out hcl_out
      let lsNok := validTargets (rs := rs) acts sig
      let lsNo₂ := buildTargets (V := Val) (rs := rs) acts sig Js_out
      have hNoSim : CTDSim (Tup.zip lsNok lsNo₂) := validTargets_buildTargets_sim acts sig Js_out
      have hNoSelf : CTDSim (Tup.zip lsNo₂ lsNo₂) := buildTargets_self_sim acts sig Js_out
      let lsBodyk := attachInlines acts pbs (bk lsNok) lsNok
      let lsBody₂ := attachInlines acts pbs (b₂ lsNo₂) lsNo₂
      let lsBody_s := attachInlines acts pbs (bs lsNo₂) lsNo₂
      have hBodySim : CTDSim (Tup.zip lsBodyk lsBody₂) :=
        attachInlines_sim hGk (hNoSim.append hDk) acts pbs (bk lsNok) (b₂ lsNo₂)
          (hbk lsNok lsNo₂) lsNok lsNo₂ hNoSim
      have hBodySelf : CTDSim (Tup.zip lsBody_s lsBody₂) :=
        attachInlines_sim hGs (hNoSelf.append hDs) acts pbs (bs lsNo₂) (b₂ lsNo₂)
          (hbs lsNo₂ lsNo₂) lsNo₂ lsNo₂ hNoSelf
      let Js_src := ctSrcConts Γ Q X lsBody₂
      have hD_body : CTWpD Γ Q X (Tup.zip lsBody₂ Js_src ++ D) :=
        (ctSrcConts_wpD Γ Q X lsBody₂).append hD
      have hD_no : CTWpD Γ Q X (Tup.zip lsNo₂ Js_src ++ D) :=
        (ctSrcConts_noInl_wpD Γ Q X lsNo₂ lsBody₂ (buildTargets_noInl_get acts Js_out)
          (attachInlines_targetsEq acts pbs (b₂ lsNo₂) lsNo₂)).append hD
      have hcl_src : Closed Γ Q X (b₃ Js_src) Js_src := by
        rw [closed_iff]
        intro ts i xs m' hw_src
        rw [ctSrcConts_get]
        dsimp only [ctSrcCont]
        refine ⟨?_, fun a ra e_out heout hreal hvals => ?_⟩
        · exact ctSrcConts_closed_targets Γ Q X acts pbs (bk lsBodyk) (b₂ lsBody₂) (b₃ Js_src)
            Js_out lsNo₂ lsBody₂
                (attachInlines_targetsEq acts pbs (b₂ lsNo₂) lsNo₂) rfl hvalb hcl_out
            (fun i' pb ak a₂ xs' hsh hopt hvb m'' hw'' => by
              obtain ⟨r_xs, hrx, hvsx⟩ := hG.toRealArgs?_zip hopt
              exact ihb lsBody₂ Js_src i' a₂ xs' ((hbk lsBodyk lsBody₂).get i' ak a₂)
                ((hbs lsBody_s lsBody₂).get i' a₂ a₂) pb hvb
                (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.mem_zip hsh p) (hGk p))
                (hBodySim.append hDk)
                (fun p hp => (List.mem_append.1 hp).elim (ArgShapeEq.refl_mem_zip a₂ p) (hGs p))
                (hBodySelf.append hDs)
                (by simpa [hvsx] using OptValCtx.of_toRealArgs? hG hrx) hD_body m'' hw'')
            i xs m' hw_src
        · obtain ⟨pb, budget, hvi, rfl⟩ := attachInlines_get_inline_some acts pbs (b₂ lsNo₂) lsNo₂
            i a e_out (buildTargets_noInl_get acts Js_out i a) heout
          have hwf_s_blk := (hbs lsNo₂ lsNo₂).get i a a
          have hsh_a : ∀ p ∈ Tup.zip a a ++ G_s, ArgShapeEq p.2.1 p.2.2 := fun p hp =>
            (List.mem_append.1 hp).elim (ArgShapeEq.refl_mem_zip a p) (hGs p)
          obtain ⟨_, hp'_s, G_s', hG_s', hpeel_wf_s⟩ :=
              peelThreadHead_sim 4 false pb hwf_s_blk hsh_a
          have hwf_wp_blk := (hb lsNo₂ Js_src).get i a (vals ra)
          have hG_a : OptValCtx (Tup.zip a (vals ra) ++ G) :=
            OptValCtx.of_toRealArgs? hG hreal
          obtain ⟨G_peel, e₃', hwf_peel, hG_peel, hw_peel⟩ :=
            peelThreadHead_wp 4 false pb hwf_wp_blk hG_a (by simpa [hvals] using hw_src)
          have hvi_s : validateInline budget (peelThreadHead 4 false pb ((bs lsNo₂).get i a)).2.1
              (peelThreadHead 4 false pb ((bs lsNo₂).get i a)).2.2 =
              validateInline budget (peelThreadHead 4 false pb ((b₂ lsNo₂).get i a)).2.1
              (peelThreadHead 4 false pb ((b₂ lsNo₂).get i a)).2.2 := by
            rw [hp'_s]
            exact validateInline_sim budget _ hpeel_wf_s hG_s' (hNoSelf.append hDs)
          obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hvi
          rw [← hp'_s]
          exact rewriteCTInline_wp hwf_peel hpeel_wf_s (hvi_s.trans hn)
            hG_s' (hNoSelf.append hDs) hG_peel hD_no m' hw_peel
      exact ihk lsBody₂ Js_src (hkk lsBodyk lsBody₂) (hks lsBody_s lsBody₂) pk hvalk
        hGk (hBodySim.append hDk) hGs (hBodySelf.append hDs) hG hD_body m (hw3 Js_src hcl_src)
    | _ => dsimp only [validateCTPlan] at hval; cases hval

/-! ### Call-set well-scopedness (`*_callsOk`) -/

private def CTCallsOkD (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)) : Prop :=
  ∀ p ∈ D, ∀ a e, p.2.1.inline? a = some e → e.callsOk allowed exits

private theorem CTCallsOkD.append {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {H D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    (hH : CTCallsOkD allowed exits H) (hD : CTCallsOkD allowed exits D) :
    CTCallsOkD allowed exits (H ++ D) := fun p hp =>
  (List.mem_append.1 hp).elim (hH p) (hD p)

private theorem ctTarget_emit_callsOk {allowed : List SigEntry} {exits : List Sym} {rs ts : List Ty}
    (t : CTTarget UnitV (fun _ => Unit) ts) (a : Tup (Arg (CTOptV UnitV)) ts) :
    (t.emit (rs := rs) a).callsOk allowed exits := by
  cases t with
  | keep _ => dsimp only [CTTarget.emit]; split <;> trivial
  | dead => trivial
  | split m lT? lF? lD? =>
    dsimp only [CTTarget.emit]
    cases getTupMem m a with
    | imm b => cases b <;> dsimp only <;> split <;> trivial
    | var ov =>
      cases ov with
      | none => trivial
      | some _ =>
        dsimp only
        cases lD? with
        | some _ => dsimp only; split <;> trivial
        | none => dsimp only; split <;> trivial

private theorem peelThreadHead_keep_wf {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (fuel : Nat) → (res : Bool) → (p : CTPlan) →
    {G : Ctx (Arg (CTOptV UnitV)) (fun _ => Unit)} →
    {D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)} →
    {e₁ : Expr (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs} →
    {e₂ : Expr UnitV (fun _ => Unit) rs} →
    Wf G D e₁ e₂ → e₂.callsOk allowed exits →
    let r := peelThreadHead fuel res p e₁
    ∃ G' e₂', Wf G' D r.2.2 e₂' ∧ e₂'.callsOk allowed exits
  | 0, _, _, G, _, _, e₂, hwf, hc => ⟨G, e₂, hwf, hc⟩
  | fuel + 1, res, p, G, D, _, _, hwf, hc => by
    cases p with
    | node1 pk =>
      have hwf0 := hwf
      cases hwf
      case let_ hop hk =>
        clear hwf0
        rcases hop with ⟨code, hargs⟩
        dsimp only [peelThreadHead]
        cases evalThreadLet? code (flattenArgs _) with
        | none => exact ⟨G, _, .let_ (.mk code hargs) hk, hc⟩
        | some out =>
          exact peelThreadHead_keep_wf fuel res pk (hk out (Tup.units _)) hc
      all_goals exact ⟨G, _, hwf0, hc⟩
    | node2 pt pe =>
      have hwf0 := hwf
      cases hwf
      case jnz hc_arg ht he =>
        clear hwf0
        dsimp only [peelThreadHead]
        cases flattenArg _ with
        | imm b =>
          cases b with
          | false => exact peelThreadHead_keep_wf fuel true pe he hc.2
          | true => exact peelThreadHead_keep_wf fuel true pt ht hc.1
        | var _ => exact ⟨G, _, .jnz hc_arg ht he, hc⟩
      all_goals exact ⟨G, _, hwf0, hc⟩
    | _ => exact ⟨G, _, hwf, hc⟩

private theorem rewriteCTInline_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg (CTOptV UnitV)) (fun _ => Unit)}
    {D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    {e₁ : Expr (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs}
    {e₂ : Expr UnitV (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : CTPlan), CTCallsOkD allowed exits D → e₂.callsOk allowed exits →
      (rewriteCTInline p e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      cases hop with
      | mk code _ =>
        dsimp only [rewriteCTInline]
        cases evalThreadLet? code _ with
        | some out => exact ih out (Tup.units _) pk hD hc
        | none =>
          cases toRealArgs? _ with
          | none => trivial
          | some _ => exact ih (toOptArgTup (Tup.units _)) (Tup.units _) pk hD hc
    | _ => trivial
  | load _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTInline]
      cases toRealArg? _ with
      | none => trivial
      | some _ => exact ih (.var (some ())) () pk hD hc
    | _ => trivial
  | store _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTInline]
      cases toRealArg? _ <;> cases toRealArg? _ <;> first | trivial | exact ih pk hD hc
    | _ => trivial
  | call _ _ _ ih =>
    intro p hD ⟨hf, hc⟩
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTInline]
      cases toRealArgs? _ with
      | none => trivial
      | some _ => exact ⟨hf, ih (toOptArgTup (Tup.units _)) (Tup.units _) pk hD hc⟩
    | _ => trivial
  | jnz _ _ _ iht ihe =>
    intro p hD ⟨hct, hce⟩
    cases p with
    | node2 pt pe =>
      dsimp only [rewriteCTInline]
      cases flattenArg _ with
      | imm b => cases b with | false => exact ihe pe hD hce | true => exact iht pt hD hct
      | var ov =>
        cases ov with
        | none => trivial
        | some _ => exact ⟨iht pt hD hct, ihe pe hD hce⟩
    | _ => trivial
  | jump hj _ =>
    intro p hD _
    cases p with
    | jump _ =>
      dsimp only [rewriteCTInline]
      split
      · exact ctTarget_emit_callsOk _ _
      · cases he : CTLabel.inline? _ (flattenArgs _) with
        | none => trivial
        | some e_out => exact hD _ hj _ e_out he
    | _ => trivial
  | ret _ =>
    intro p _ _
    cases p with
    | leaf => dsimp only [rewriteCTInline]; cases toRealArgs? _ <;> trivial
    | _ => trivial
  | exit _ _ =>
    intro p _ hc
    cases p with
    | leaf =>
      dsimp only [rewriteCTInline]
      cases toRealArgs? _ with | none => trivial | some _ => exact hc
    | _ => trivial
  | hlt => intro p _ _; cases p <;> trivial
  | group _ _ _ _ => intro p _ _; cases p <;> trivial

private theorem attachInlines_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg (CTOptV UnitV)) (fun _ => Unit)}
    {D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    (hD : CTCallsOkD allowed exits D) :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs sig) →
    (bs₂ : Blocks UnitV (fun _ => Unit) rs sig) →
    WfB G D bs₁ bs₂ → bs₂.callsOk allowed exits →
    (ls : Tup (CTLabel UnitV (fun _ => Unit) rs) sig) →
    (∀ p ∈ Tup.zip ls (Tup.units sig), ∀ a e, p.2.1.inline? a = some e → e.callsOk allowed exits) →
    ∀ p ∈ Tup.zip (attachInlines acts pbs bs₁ ls) (Tup.units sig),
      ∀ a e, p.2.1.inline? a = some e → e.callsOk allowed exits
  | _, _, [], .nil, .nil, _, _, (), _, _, hp => nomatch hp
  | a :: acts, .cons pb pbs, _ :: _, .cons b tl₁, .cons _ tl₂, .cons hb hbs, hc,
      (l, ls), hls, p, hp => by
    rcases hc with ⟨hcb, hcs⟩
    dsimp only [attachInlines, Tup.units, Tup.zip] at hp
    cases hp with
    | head =>
      intro arg e_out he
      simp only [attachInlines] at he
      have hl0 : ∀ a e, l.inline? a = some e → e.callsOk allowed exits :=
        hls _ List.mem_cons_self
      cases a with
      | keep _ allow =>
        cases allow with
        | false => exact hl0 arg e_out he
        | true =>
          dsimp only [tryMakeInlineLabel] at he
          by_cases hvs : (validateInline (if (peelThreadHead 4 false pb (b arg)).1 then 8 else 3)
              (peelThreadHead 4 false pb (b arg)).2.1
              (peelThreadHead 4 false pb (b arg)).2.2).isSome = true
          · simp only [hvs, ↓reduceIte, Option.some.injEq] at he
            cases he
            obtain ⟨_, _, hwf_p, hc_p⟩ :=
                peelThreadHead_keep_wf 4 false pb (hb arg (Tup.units _)) hcb
            exact rewriteCTInline_callsOk hwf_p _ hD hc_p
          · simp only [hvs, Bool.false_eq_true, ↓reduceIte] at he
            cases he
      | splitBool _ _ _ _ inlT inlF =>
        dsimp only [tryMakeInlineLabel] at he
        by_cases hinl : (inlT || inlF) = true
        · simp only [hinl, ↓reduceIte] at he
          by_cases hc : ((peelThreadHead 4 false pb (b arg)).1 &&
              (validateInline 8 (peelThreadHead 4 false pb (b arg)).2.1
                (peelThreadHead 4 false pb (b arg)).2.2).isSome) = true
          · simp only [hc, ↓reduceIte, Option.some.injEq] at he
            cases he
            obtain ⟨_, _, hwf_p, hc_p⟩ :=
                peelThreadHead_keep_wf 4 false pb (hb arg (Tup.units _)) hcb
            exact rewriteCTInline_callsOk hwf_p _ hD hc_p
          · simp only [hc, Bool.false_eq_true, ↓reduceIte] at he
            cases he
        · simp only [hinl, Bool.false_eq_true, ↓reduceIte] at he
          exact hl0 arg e_out he
    | tail _ hp' =>
      exact attachInlines_callsOk hD acts pbs tl₁ tl₂ hbs hcs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | [], _, _ :: _, .cons _ tl₁, .cons _ tl₂, .cons _ hbs, hc, (_, ls), hls, p, hp => by
    rcases hc with ⟨_, hcs⟩
    dsimp only [attachInlines, Tup.units, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_callsOk hD [] .nil tl₁ tl₂ hbs hcs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'
  | _ :: _, .nil, _ :: _, .cons _ tl₁, .cons _ tl₂, .cons _ hbs, hc, (_, ls), hls, p, hp => by
    rcases hc with ⟨_, hcs⟩
    dsimp only [attachInlines, Tup.units, Tup.zip] at hp
    cases hp with
    | head => exact hls _ List.mem_cons_self
    | tail _ hp' =>
      exact attachInlines_callsOk hD [] .nil tl₁ tl₂ hbs hcs ls
        (fun _ hq => hls _ (List.mem_cons_of_mem _ hq)) p hp'

private theorem buildTargets_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (acts : List BlockAct) → (sig : List (List Ty)) →
    (Js : Tup (fun _ => Unit) (threadSig acts sig)) →
    CTCallsOkD allowed exits (Tup.zip (buildTargets (V := UnitV) (rs :=
        rs) acts sig Js) (Tup.units sig))
  | _, [], (), _, hp => nomatch hp
  | [], _ :: sig, (_, js), p, hp => by
    dsimp only [buildTargets, Tup.units, Tup.zip] at hp
    cases hp with
    | head => intro _ _ he; cases he
    | tail _ hp' => exact buildTargets_callsOk [] sig js p hp'
  | a :: acts, ts :: sig, js, p, hp => by
    dsimp only [buildTargets, Tup.units, Tup.zip] at hp
    cases hp with
    | head => intro _ _ he; cases he
    | tail _ hp' => exact buildTargets_callsOk acts sig (splitLabelTup _ _ js).2 p hp'

private theorem blocksAppend_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {s₁ s₂ : List (List Ty)} → {bs₁ : Blocks (fun _ => Unit) (fun _ => Unit) rs s₁} →
    {bs₂ : Blocks (fun _ => Unit) (fun _ => Unit) rs s₂} →
    bs₁.callsOk allowed exits → bs₂.callsOk allowed exits →
    (blocksAppend bs₁ bs₂).callsOk allowed exits
  | [], _, .nil, _, _, h₂ => h₂
  | _ :: _, _, .cons _ _, _, h₁, h₂ => ⟨h₁.1, blocksAppend_callsOk h₁.2 h₂⟩

private theorem condConsBlock_callsOk {allowed : List SigEntry} {exits : List Sym} {rs ts : List Ty}
    (b : Bool) (blk : Unit → Tup (fun _ => Unit) ts → Expr (fun _ => Unit) (fun _ => Unit) rs)
    {rest : List (List Ty)} (tl : Blocks (fun _ => Unit) (fun _ => Unit) rs rest)
    (hblk : b = true → (blk () (Tup.units ts)).callsOk allowed exits)
    (htl : tl.callsOk allowed exits) :
    (condConsBlock b blk tl).callsOk allowed exits := by
  cases b with
  | false => exact htl
  | true => exact ⟨hblk rfl, htl⟩

private theorem mkHltBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    (sig : List (List Ty)) → (mkHltBlocks (V := fun _ => Unit) (L := fun _ => Unit) (rs :=
        rs) sig).callsOk allowed exits
  | [] => trivial
  | _ :: sig => ⟨trivial, mkHltBlocks_callsOk sig⟩

private theorem mkSplitBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs ts : List Ty}
    (m : Member .bool ts) (keepDisp keepT keepF : Bool) (lbl : CTLabel UnitV (fun _ => Unit) rs ts)
    {rwT rwF : Tup UnitV (eraseMem m) → Expr UnitV (fun _ => Unit) rs}
    (hT : (rwT (Tup.units _)).callsOk allowed exits)
    (hF : (rwF (Tup.units _)).callsOk allowed exits) :
    (mkSplitBlocks m keepDisp keepT keepF lbl rwT rwF).callsOk allowed exits := by
  refine condConsBlock_callsOk keepDisp _ _ (fun _ => ?_)
    (condConsBlock_callsOk keepT _ _ (fun _ => hT) (condConsBlock_callsOk keepF _ _ (fun _ =>
      hF) trivial))
  dsimp only
  cases lbl.target with
  | keep _ | dead => trivial
  | split m' lT? lF? _ => cases lT? <;> cases lF? <;> simp [Expr.callsOk]

private theorem rewriteCTBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List
    Ty} :
    (acts : List BlockAct) → (pbs : CTPlanB) → {sig : List (List Ty)} →
    (bs₁ : Blocks (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs sig) →
    (ls : Tup (CTLabel UnitV (fun _ => Unit) rs) sig) →
    (∀ {ts} (i : Member ts sig) pb (a₁ : Tup (Arg (CTOptV UnitV)) ts),
      (rewriteCTAux pb (bs₁.get i a₁)).callsOk allowed exits) →
    (rewriteCTBlocks acts pbs bs₁ ls).callsOk allowed exits
  | acts, _, [], .nil, (), _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_callsOk _
  | [], _, _ :: _, .cons _ _, _, _ => by simp only [rewriteCTBlocks]; exact mkHltBlocks_callsOk _
  | _ :: _, .nil, _ :: _, .cons _ _, _, _ => by
    simp only [rewriteCTBlocks]; exact mkHltBlocks_callsOk _
  | a :: acts, .cons pb pbs, ts :: _, .cons _ tl₁, (_, tls), h => by
    unfold rewriteCTBlocks
    refine blocksAppend_callsOk ?_ (rewriteCTBlocks_callsOk acts pbs tl₁ tls (fun i =>
      h (.there i)))
    cases a with
    | keep kb _ =>
      cases kb with
      | false => trivial
      | true => exact ⟨h .here pb _, trivial⟩
    | splitBool p keepT keepF keepDisp _ _ =>
      dsimp only [actSig]
      generalize splitMember? p ts = sp
      cases sp with
      | none => exact ⟨h .here pb _, trivial⟩
      | some m => exact mkSplitBlocks_callsOk m keepDisp keepT keepF _ (h .here pb _) (h .here pb _)

private theorem rewriteCTAux_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg (CTOptV UnitV)) UnitV} {D : Ctx (CTLabel UnitV (fun _ => Unit) rs) (fun _ =>
      Unit)}
    {e₁ : Expr (Arg (CTOptV UnitV)) (CTLabel UnitV (fun _ => Unit) rs) rs}
    {e₂ : Expr UnitV (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (p : CTPlan), CTCallsOkD allowed exits D → e₂.callsOk allowed exits →
      (rewriteCTAux p e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      cases hop with
      | mk code _ =>
        dsimp only [rewriteCTAux]
        cases evalThreadLet? code _ with
        | some out => exact ih out (Tup.units _) pk hD hc
        | none =>
          cases toRealArgs? _ with
          | none => trivial
          | some _ => exact ih (toOptArgTup (Tup.units _)) (Tup.units _) pk hD hc
    | _ => trivial
  | load _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTAux]
      cases toRealArg? _ with
      | none => trivial
      | some _ => exact ih (.var (some ())) () pk hD hc
    | _ => trivial
  | store _ _ _ ih =>
    intro p hD hc
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTAux]
      cases toRealArg? _ <;> cases toRealArg? _ <;> first | trivial | exact ih pk hD hc
    | _ => trivial
  | call _ _ _ ih =>
    intro p hD ⟨hf, hc⟩
    cases p with
    | node1 pk =>
      dsimp only [rewriteCTAux]
      cases toRealArgs? _ with
      | none => trivial
      | some _ => exact ⟨hf, ih (toOptArgTup (Tup.units _)) (Tup.units _) pk hD hc⟩
    | _ => trivial
  | jnz _ _ _ iht ihe =>
    intro p hD ⟨hct, hce⟩
    cases p with
    | node2 pt pe =>
      dsimp only [rewriteCTAux]
      cases flattenArg _ with
      | imm b => cases b with | false => exact ihe pe hD hce | true => exact iht pt hD hct
      | var ov =>
        cases ov with
        | none => trivial
        | some _ => exact ⟨iht pt hD hct, ihe pe hD hce⟩
    | _ => trivial
  | jump hj _ =>
    intro p hD _
    cases p with
    | jump tryInl =>
      dsimp only [rewriteCTAux, CTLabel.emitJump]
      cases tryInl
      · exact ctTarget_emit_callsOk _ _
      · cases he : CTLabel.inline? _ (flattenArgs _) with
        | none => exact ctTarget_emit_callsOk _ _
        | some e_out => exact hD _ hj _ e_out he
    | _ => trivial
  | ret _ =>
    intro p _ _
    cases p with | leaf => dsimp only [rewriteCTAux]; cases toRealArgs? _ <;> trivial | _ => trivial
  | exit _ _ =>
    intro p _ hc
    cases p with
    | leaf =>
      dsimp only [rewriteCTAux]
      cases toRealArgs? _ with | none => trivial | some _ => exact hc
    | _ => trivial
  | hlt => intro p _ _; cases p <;> trivial
  | @group _ D sig b₁ b₂ k₁ k₂ hb _ ihb ihk =>
    intro p hD ⟨hcb, hck⟩
    cases p with
    | group acts pbs pk =>
      dsimp only [rewriteCTAux, Expr.callsOk]
      let lsNo := buildTargets (V := UnitV) (rs := rs) acts sig (Tup.units _)
      have hNo : CTCallsOkD allowed exits (Tup.zip lsNo (Tup.units sig)) :=
        buildTargets_callsOk acts sig (Tup.units _)
      have hD_no : CTCallsOkD allowed exits (Tup.zip lsNo (Tup.units sig) ++ D) := hNo.append hD
      let lsBody := attachInlines acts pbs (b₁ lsNo) lsNo
      have hBody : CTCallsOkD allowed exits (Tup.zip lsBody (Tup.units sig)) :=
        attachInlines_callsOk hD_no acts pbs (b₁ lsNo) (b₂ (Tup.units sig))
            (hb lsNo (Tup.units sig))
          hcb lsNo hNo
      have hD_body : CTCallsOkD allowed exits (Tup.zip lsBody (Tup.units sig) ++ D) :=
          hBody.append hD
      refine ⟨rewriteCTBlocks_callsOk acts pbs (b₁ lsBody) lsNo (fun i pb a₁ =>
        ihb lsBody (Tup.units sig) i a₁ (Tup.units _) pb hD_body (Blocks.callsOk_get hcb i)),
        ihk lsBody (Tup.units sig) pk hD_body hck⟩
    | _ => trivial

private theorem denoteB_toTBlocks_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List
    Ty} :
    {sig : List (List Ty)} → {bs₁ : Blocks K KL rs sig} → {bs₂ : Blocks UnitV (fun _ =>
      Unit) rs sig} →
    (nv nl : Nat) → (vs : List ((_t : Ty) × Unit)) → (ls : List ((_ts : List Ty) × Unit)) →
    (∀ {ts} (i : Member ts sig), (bs₂.get i (Tup.units ts)).callsOk allowed exits →
      (denote UnitV (fun _ => Unit)
        (toTFlat (bs₁.get i (Tup.levels ts nv)) (nv + ts.length) nl)
        (pushTup (Tup.units ts) vs) ls).callsOk allowed exits) →
    bs₂.callsOk allowed exits →
    (denoteB UnitV (fun _ => Unit) (toTBlocks bs₁ nv nl) vs ls).callsOk allowed exits
  | [], .nil, .nil, _, _, _, _, _, _ => trivial
  | _ :: _, .cons _ _, .cons _ _, nv, nl, vs, ls, h, hc =>
    ⟨h .here hc.1, denoteB_toTBlocks_callsOk nv nl vs ls (fun i => h (.there i)) hc.2⟩

private theorem denote_toTFlat_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx K UnitV} {D : Ctx KL (fun _ => Unit)}
    {e₁ : Expr K KL rs} {e₂ : Expr UnitV (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (nv nl : Nat) (vs : List ((_t : Ty) × Unit)) (ls : List ((_ts : List Ty) × Unit)),
      e₂.callsOk allowed exits →
      (denote UnitV (fun _ => Unit) (toTFlat e₁ nv nl) vs ls).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArgs vs (idxArgs nv op₁.args) with
    | none => trivial
    | some _ => exact ih (Tup.levels ts nv) (Tup.units ts) (nv + ts.length) nl _ ls hc
  | load _ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArg vs (idxArg nv _) with
    | none => trivial
    | some _ => exact ih nv () (nv + 1) nl _ ls hc
  | store _ _ _ ih =>
    intro nv nl vs ls hc
    dsimp only [toTFlat, denote]
    cases denoteArg vs _ <;> cases denoteArg vs _ <;> first | trivial | exact ih nv nl vs ls hc
  | call _ _ _ ih =>
    intro nv nl vs ls ⟨hf, hc⟩
    dsimp only [toTFlat, denote]
    cases denoteArgs vs _ with
    | none => trivial
    | some _ => exact ⟨hf, ih (Tup.levels _ nv) (Tup.units _) (nv + _) nl _ ls hc⟩
  | jnz _ _ _ iht ihe =>
    intro nv nl vs ls ⟨ht, he⟩
    dsimp only [toTFlat, denote]
    cases denoteArg vs _ with
    | none => trivial
    | some _ => exact ⟨iht nv nl vs ls ht, ihe nv nl vs ls he⟩
  | jump _ _ =>
    intro nv nl vs ls _
    dsimp only [toTFlat, denote]
    cases lookupL ls _ _ <;> cases denoteArgs vs _ <;> trivial
  | ret _ =>
    intro nv nl vs _ _
    dsimp only [toTFlat, denote]; cases denoteArgs vs _ <;> trivial
  | exit _ _ =>
    intro nv nl vs _ _
    dsimp only [toTFlat, denote]; cases denoteArgs vs _ <;> trivial
  | hlt => intro _ _ _ _ _; trivial
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro nv nl vs ls ⟨hb, hk⟩
    dsimp only [toTFlat, denote, Expr.callsOk]
    exact ⟨denoteB_toTBlocks_callsOk nv (nl + sig.length) vs _
        (fun i hci => ihb (Tup.levels sig nl) (Tup.units sig) i (Tup.levels _ nv) (Tup.units _)
          (nv + _) (nl + sig.length) _ _ hci) hb,
      ihk (Tup.levels sig nl) (Tup.units sig) nv (nl + sig.length) vs _ hk⟩

end CondThreadOptImpl

/-! ## Top-level soundness theorems (`condThread_ok` and entrypoints) -/

open CondThreadOpt CondThreadOptImpl

/-- `Func.condThreadWithPlan` preserves relational well-formedness `Func.Wf`. -/
theorem Func.condThreadWithPlan_wf {as rs : List Ty} (plan : CTPlan) {f : Func as rs} (hf : f.Wf) :
    (Func.condThreadWithPlan plan f).Wf := by
  dsimp only [Func.condThreadWithPlan]
  split
  · intro V₁ V₂ L₁ L₂ xs₁ xs₂
    exact rewriteCTAux_wf
      (hf (Arg (CTOptV V₁)) (Arg (CTOptV V₂)) (CTLabel V₁ L₁ rs) (CTLabel V₂ L₂ rs)
        (toOptArgTup xs₁) (toOptArgTup xs₂))
      plan (mem_zip_toOptArgTup xs₁ xs₂) (fun _ hp => nomatch hp)
  · exact hf

/-- `Func.condThreadWithPlan` refines `Func.wp` / `Func.spec` when `f` is well-formed. -/
theorem Func.condThreadWithPlan_spec {as rs : List Ty} (plan : CTPlan) {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) :
    Func.spec Γ (Func.condThreadWithPlan plan f) xs m Q X := by
  dsimp only [Func.condThreadWithPlan]
  split
  · rename_i hval
    have hwf := hf (Arg (CTOptV Val)) Val (CTLabel Val Cont rs) Cont (toOptArgTup xs) xs
    have hwk := hf (Arg (CTOptV UnitV)) (Arg (CTOptV Val)) (ValidL rs) (CTLabel Val Cont rs)
      (toOptArgTup (Tup.units as)) (toOptArgTup xs)
    have hwfs :=
        hf (Arg (CTOptV Val)) (Arg (CTOptV Val)) (CTLabel Val Cont rs) (CTLabel Val Cont rs)
      (toOptArgTup xs) (toOptArgTup xs)
    exact rewriteCTAux_wp hwf hwk hwfs plan hval
      (toOptArgTup_shape_zip _ _) (fun _ hp => nomatch hp)
      (toOptArgTup_shape_zip _ _) (fun _ hp => nomatch hp)
      (by simpa [List.append_nil] using
        OptValCtx.of_toOptArgTup (G := []) (fun _ hp => nomatch hp) xs)
      (fun _ hp => nomatch hp) m h
  · exact h

/-- `Func.condThreadWithPlan` preserves `Expr.callsOk`. -/
theorem Func.condThreadWithPlan_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} (plan : CTPlan) {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.condThreadWithPlan plan f) UnitV (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  dsimp only [Func.condThreadWithPlan]
  split
  · exact rewriteCTAux_callsOk
      (hf (Arg (CTOptV UnitV)) UnitV (CTLabel UnitV (fun _ => Unit) rs) (fun _ => Unit)
        (toOptArgTup (Tup.units as)) (Tup.units as))
      plan (fun _ hp => nomatch hp) hc
  · exact hc

/-- `Func.condThreadPass` preserves relational well-formedness `Func.Wf`. -/
theorem Func.condThreadPass_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.condThreadPass f).Wf := by
  dsimp only [Func.condThreadPass]
  split
  · exact Func.condThreadWithPlan_wf _ hf
  · exact Func.wf_of_denote (reifyFunc f) rfl

/-- `Func.condThreadPass` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.condThreadPass_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.condThreadPass f) xs m Q X := by
  dsimp only [Func.condThreadPass]
  split
  · exact Func.condThreadWithPlan_spec _ hf h
  · exact Func.renorm_spec hf h

/-- `Func.condThreadPass` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.condThreadPass_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.condThreadPass f) UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  dsimp only [Func.condThreadPass]
  split
  · exact Func.condThreadWithPlan_callsOk _ hf hc
  · simpa [denoteFunc, reifyFunc] using
      denote_toTFlat_callsOk
        (hf K UnitV KL (fun _ => Unit) (Tup.levels as 0) (Tup.units as))
        as.length 0 (pushTup (Tup.units as) []) [] hc

/-- `Func.condThreadOpt` preserves relational well-formedness `Func.Wf`. -/
theorem Func.condThreadOpt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.condThreadOpt f).Wf :=
  Func.condThreadPass_wf (Func.pathCondOpt_wf hf)

/-- `Func.condThreadOpt` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.condThreadOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.condThreadOpt f) xs m Q X :=
  Func.condThreadPass_spec (Func.pathCondOpt_wf hf) (Func.pathCondOpt_spec hf h)

/-- Full semantic preservation of `Func.condThreadOpt` under `Func.wp` / `Func.spec`. -/
theorem condThread_ok {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.wp Γ f xs m Q X) : Func.wp Γ (Func.condThreadOpt f) xs m Q X :=
  Func.condThreadOpt_spec hf h

/-- `Func.condThreadOpt` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.condThreadOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.condThreadOpt f) UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  Func.condThreadPass_callsOk (Func.pathCondOpt_wf hf) (Func.pathCondOpt_callsOk hf hc)

/-- `Fn.condThreadOpt` preserves `Fn.Wf`. -/
theorem Fn.condThreadOpt_wf {fn : Fn} (hf : fn.Wf) : (fn.condThreadOpt).Wf :=
  Func.condThreadOpt_wf hf

/-- `Fn.condThreadOpt` refines `Func.spec`. -/
theorem Fn.condThreadOpt_spec {fn : Fn} (hf : fn.Wf)
    {Γ : Env} {xs : Tup Val fn.as} {m : Mem 64} {Q : Post fn.rs} {X : XPost}
    (h : Func.spec Γ fn.body xs m Q X) : Func.spec Γ (fn.condThreadOpt).body xs m Q X :=
  Func.condThreadOpt_spec hf h

/-- `Fn.condThreadOpt` preserves `Fn.callsOk`. -/
theorem Fn.condThreadOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {fn : Fn} (hf : fn.Wf) (hc : fn.callsOk allowed exits) :
    (fn.condThreadOpt).callsOk allowed exits :=
  Func.condThreadOpt_callsOk hf hc

/-- `Func.condThreadLateOpt` preserves relational well-formedness `Func.Wf`. -/
theorem Func.condThreadLateOpt_wf {as rs : List Ty} (f : Func as rs) :
    (Func.condThreadLateOpt f).Wf :=
  Func.renorm_wf _

/-- `Func.condThreadLateOpt` refines `Func.wp` / `Func.spec` for any well-formed `f`. -/
theorem Func.condThreadLateOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.condThreadLateOpt f) xs m Q X :=
  Func.renorm_spec (Func.condThreadOpt_wf hf) (Func.condThreadOpt_spec hf h)

/-- `Func.condThreadLateOpt` preserves `Expr.callsOk` for any well-formed `f`. -/
theorem Func.condThreadLateOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.condThreadLateOpt f) UnitV (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  simpa [Func.condThreadLateOpt, Func.renorm, denoteFunc, reifyFunc] using
    denote_toTFlat_callsOk
      ((Func.condThreadOpt_wf hf) K UnitV KL (fun _ => Unit) (Tup.levels as 0) (Tup.units as))
      as.length 0 (pushTup (Tup.units as) []) [] (Func.condThreadOpt_callsOk hf hc)

end LeanQbe.T
