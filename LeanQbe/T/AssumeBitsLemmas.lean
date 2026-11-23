module

public import LeanQbe.T.AssumeBits
public import LeanQbe.T.Wf
public import LeanQbe.T.WP
public import LeanQbe.T.Module
import LeanQbe.T.OpsLemmas
import LeanQbe.T.WPLemmas
import LeanQbe.T.WfLemmas

/-!
# Correctness of `assumeBits`

* Semantic invariant: every `ABVal` agrees with its value (`ABGood`): its known-zero mask is
  sound (`KZOk`), its identity is bound in the identity environment `ρ`, and its zero / nonzero
  facts hold (`FactsOk`) whenever the value is zero / nonzero.
* `abElim?_sound`, `abRes_ok`, `OpRel.abLet_wp`: every elimination and every emitted result's
  metadata is sound for the opcode semantics.
* `assumeBits_wp`: source `wp` implies the simplified `wp` (via `Wf.induct`), with branch facts
  justified by the `.jnz` condition on each arm.
* `assumeBits_wf`, `assumeBits_callsOk`: relational well-formedness and call/exit well-scopedness.
* `Func.assumeBits_spec`, `Func.assumeBits_wf`, `Func.assumeBits_callsOk`: closed functions.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Identity environment -/

/-- Environment mapping lexical identities to their bound values. -/
abbrev ABEnv : Type := Nat → Option ((t : Ty) × Val t)

/-- Bind identity `b` to `v`. -/
def ABEnv.upd (ρ : ABEnv) {t : Ty} (b : Nat) (v : Val t) : ABEnv :=
  fun k => if k = b then some ⟨t, v⟩ else ρ k

/-- Bind consecutive identities `b, b + 1, …` to `xs`. -/
def ABEnv.updTup (ρ : ABEnv) (b : Nat) : {ts : List Ty} → Tup Val ts → ABEnv
  | [], () => ρ
  | _ :: _, (x, xs) => ABEnv.updTup (ABEnv.upd ρ b x) (b + 1) xs

theorem ABEnv.upd_eq (ρ : ABEnv) {t : Ty} (b : Nat) (v : Val t) :
    ABEnv.upd ρ b v b = some ⟨t, v⟩ := by
  simp [ABEnv.upd]

theorem ABEnv.upd_ne (ρ : ABEnv) {t : Ty} {b k : Nat} (v : Val t) (h : k ≠ b) :
    ABEnv.upd ρ b v k = ρ k := by
  simp [ABEnv.upd, h]

theorem ABEnv.updTup_lt (ρ : ABEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → {b k : Nat} → k < b → ABEnv.updTup ρ b xs k = ρ k
  | [], (), _, _, _ => rfl
  | _ :: _, (x, xs), b, k, hk => by
    dsimp only [ABEnv.updTup]
    rw [ABEnv.updTup_lt (ABEnv.upd ρ b x) xs (by omega)]
    exact ABEnv.upd_ne ρ x (by omega)

/-! ## Semantic invariants -/

/-- Every bit set in `kz` is `0` in the value (vacuous on non-`.bits` types). -/
def KZOk : (t : Ty) → Val t → Nat → Prop
  | .bits _, v, kz => ∀ i, kz.testBit i = true → BitVec.getLsbD v i = false
  | _, _, _ => True

/-- A fact holds when its identity is in scope and its mask is known zero in the bound value. -/
def FactOk (ρ : ABEnv) (b : Nat) (f : BitFact) : Prop :=
  f.1 < b ∧ ∀ (n : Nat) (v : BitVec n), ρ f.1 = some ⟨.bits n, v⟩ → KZOk (.bits n) v f.2

/-- Every fact of `F` holds. -/
def FactsOk (ρ : ABEnv) (b : Nat) (F : List BitFact) : Prop :=
  ∀ f ∈ F, FactOk ρ b f

/-- The value is zero (`false` / `0#n`). -/
def ZeroV : (t : Ty) → Val t → Prop
  | .bool, v => v = false
  | .bits n, v => v = 0#n
  | _, _ => False

/-- The value is nonzero (`true` / `≠ 0#n`). -/
def NzV : (t : Ty) → Val t → Prop
  | .bool, v => v = true
  | .bits n, v => v ≠ 0#n
  | _, _ => False

/-- Metadata `a` is sound for value `v` under identity environment `ρ` below bound `b`. -/
def InfoOk (ρ : ABEnv) (b : Nat) {t : Ty} (a : ABInfo) (v : Val t) : Prop :=
  (∀ k, a.id = some k → k < b ∧ ρ k = some ⟨t, v⟩) ∧ KZOk t v a.kz ∧
    (ZeroV t v → FactsOk ρ b a.zf) ∧ (NzV t v → FactsOk ρ b a.nf)

/-- An `ABVal` agrees with value `v`. -/
def ABGood (ρ : ABEnv) (b : Nat) {t : Ty} (a : ABVal Val t) (v : Val t) : Prop :=
  a.out.val = v ∧ InfoOk ρ b a.info v

/-- An input operand agrees with value `v`. -/
def ABGoodArg (ρ : ABEnv) (b : Nat) {t : Ty} (a : Arg (ABVal Val) t) (v : Val t) : Prop :=
  a.abOut.val = v ∧ InfoOk ρ b a.abInfo v

/-- Context invariant: every entry of `G` agrees with its value. -/
def ABGoodCtx (ρ : ABEnv) (b : Nat) (G : Ctx (ABVal Val) Val) : Prop :=
  ∀ p ∈ G, ABGood ρ b p.2.1 p.2.2

/-! ## Monotonicity under environment extension -/

section Mono
variable {ρ ρ' : ABEnv} {b b' : Nat}

theorem FactsOk.mono (hb : b ≤ b') (hρ : ∀ k, k < b → ρ' k = ρ k) {F : List BitFact}
    (h : FactsOk ρ b F) : FactsOk ρ' b' F := fun f hf =>
  ⟨by have := (h f hf).1; omega, fun n v hv => (h f hf).2 n v ((hρ _ (h f hf).1).symm.trans hv)⟩

theorem InfoOk.mono (hb : b ≤ b') (hρ : ∀ k, k < b → ρ' k = ρ k) {t : Ty} {a : ABInfo}
    {v : Val t} (h : InfoOk ρ b a v) : InfoOk ρ' b' a v :=
  ⟨fun k hk => ⟨by have := (h.1 k hk).1; omega, (hρ k (h.1 k hk).1).trans (h.1 k hk).2⟩, h.2.1,
    fun hz => (h.2.2.1 hz).mono hb hρ, fun hn => (h.2.2.2 hn).mono hb hρ⟩

theorem ABGoodCtx.mono (hb : b ≤ b') (hρ : ∀ k, k < b → ρ' k = ρ k) {G : Ctx (ABVal Val) Val}
    (h : ABGoodCtx ρ b G) : ABGoodCtx ρ' b' G := fun p hp =>
  ⟨(h p hp).1, (h p hp).2.mono hb hρ⟩

end Mono

theorem FactsOk.updTup {ρ : ABEnv} {b : Nat} {F : List BitFact} (h : FactsOk ρ b F)
    {ts : List Ty} (xs : Tup Val ts) : FactsOk (ABEnv.updTup ρ b xs) (b + ts.length) F :=
  h.mono (Nat.le_add_right _ _) fun _ hk => ABEnv.updTup_lt ρ xs hk

theorem ABGoodCtx.updTup {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val} (h : ABGoodCtx ρ b G)
    {ts : List Ty} (xs : Tup Val ts) : ABGoodCtx (ABEnv.updTup ρ b xs) (b + ts.length) G :=
  h.mono (Nat.le_add_right _ _) fun _ hk => ABEnv.updTup_lt ρ xs hk

theorem FactsOk.append {ρ : ABEnv} {b : Nat} {F₁ F₂ : List BitFact} (h₁ : FactsOk ρ b F₁)
    (h₂ : FactsOk ρ b F₂) : FactsOk ρ b (F₁ ++ F₂) := fun f hf =>
  (List.mem_append.1 hf).elim (h₁ f) (h₂ f)

theorem FactsOk.nil {ρ : ABEnv} {b : Nat} : FactsOk ρ b [] := fun _ hf => nomatch hf

/-! ## Context helpers -/

theorem ABGoodCtx.cons {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val} (hG : ABGoodCtx ρ b G)
    {t : Ty} {a : ABVal Val t} {v : Val t} (ha : ABGood ρ b a v) :
    ABGoodCtx ρ b (⟨t, a, v⟩ :: G)
  | _, .head _ => ha
  | _, .tail _ hp => hG _ hp

theorem ABGoodCtx.append_tup {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val}
    (hG : ABGoodCtx ρ b G) :
    {ts : List Ty} → {cs : Tup (ABVal Val) ts} → {xs : Tup Val ts} →
    TRel (fun _ a v => ABGood ρ b a v) cs xs → ABGoodCtx ρ b (Tup.zip cs xs ++ G)
  | [], (), (), .nil => hG
  | _ :: _, (_, _), (_, _), .cons hc hs => (ABGoodCtx.append_tup hG hs).cons hc

theorem KZOk.zero : (t : Ty) → (v : Val t) → KZOk t v 0
  | .bits _, _ => fun i hi => by simp at hi
  | .bool, _ => trivial
  | .float _, _ => trivial
  | .pair _ _, _ => trivial

private theorem InfoOk.fresh {ρ : ABEnv} {b k : Nat} {t : Ty} {v : Val t} (hk : k < b)
    (hρ : ρ k = some ⟨t, v⟩) : InfoOk ρ b ({ id := some k } : ABInfo) v :=
  ⟨fun _ h => by cases h; exact ⟨hk, hρ⟩, KZOk.zero t v, fun _ => FactsOk.nil,
    fun _ => FactsOk.nil⟩

private theorem ABGoodCtx.freshABVals_only (ρ : ABEnv) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    ABGoodCtx (ABEnv.updTup ρ b xs) (b + ts.length) (Tup.zip (freshABVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | t :: ts, (x, xs), b => by
    dsimp only [freshABVals, tupFreshWith, Tup.zip, ABEnv.updTup]
    intro p hp
    cases hp with
    | head =>
      refine ⟨rfl, InfoOk.fresh (by simp) ?_⟩
      rw [ABEnv.updTup_lt (ABEnv.upd ρ b x) xs (by omega), ABEnv.upd_eq]
    | tail _ hp =>
      have ih := ABGoodCtx.freshABVals_only (ABEnv.upd ρ b x) xs (b + 1) p hp
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem ABGoodCtx.freshABVals {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val}
    (hG : ABGoodCtx ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    ABGoodCtx (ABEnv.updTup ρ b xs) (b + ts.length) (Tup.zip (freshABVals ts xs b) xs ++ G) :=
  fun p hp => (List.mem_append.1 hp).elim (ABGoodCtx.freshABVals_only ρ xs b p)
    ((hG.updTup xs) p)

theorem ABGoodCtx.freshOne {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val}
    (hG : ABGoodCtx ρ b G) {t : Ty} (v : Val t) :
    ABGoodCtx (ABEnv.upd ρ b v) (b + 1) (⟨t, ABVal.fresh v b, v⟩ :: G) :=
  (hG.updTup (ts := [t]) (v, ())).cons ⟨rfl, InfoOk.fresh (by simp) (ABEnv.upd_eq ρ b v)⟩

/-! ## Bit-level lemmas -/

theorem KZOk.or {n : Nat} {v : BitVec n} {k₁ k₂ : Nat} (h₁ : KZOk (.bits n) v k₁)
    (h₂ : KZOk (.bits n) v k₂) : KZOk (.bits n) v (k₁ ||| k₂) := fun i hi => by
  rw [Nat.testBit_or, Bool.or_eq_true] at hi
  exact hi.elim (h₁ i) (h₂ i)

theorem immKz_ok : (t : Ty) → (c : Val t) → KZOk t c (immKz t c)
  | .bits n, c => fun i hi => by
    dsimp only [immKz] at hi
    rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, BitVec.testBit_toNat] at hi
    by_cases h : i < n
    · simpa [h] using hi
    · exact BitVec.getLsbD_of_ge c i (by omega)
  | .bool, _ => trivial
  | .float _, _ => trivial
  | .pair _ _, _ => trivial

theorem highFrom_testBit {n k i : Nat} (h : (highFrom n k).testBit i = true) : k ≤ i ∧ i < n := by
  unfold highFrom at h
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem andKeeps_eq {n kz : Nat} {c x : BitVec n} (h : andKeeps n kz c = true)
    (hx : KZOk (.bits n) x kz) : x &&& c = x := by
  unfold andKeeps at h
  have h' := beq_iff_eq.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb := congrArg (fun m => Nat.testBit m i) h'
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    BitVec.testBit_toNat, hi, decide_true] at hb
  rw [BitVec.getLsbD_and]
  cases hc : c.getLsbD i
  · simp only [hc, Bool.true_xor, Bool.not_false, Bool.true_and] at hb
    simp [hx i hb]
  · simp

theorem andKills_eq {n kz : Nat} {c x : BitVec n} (h : andKills kz c = true)
    (hx : KZOk (.bits n) x kz) : x &&& c = 0#n := by
  unfold andKills at h
  have h' := beq_iff_eq.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have hb := congrArg (fun m => Nat.testBit m i) h'
  simp only [Nat.testBit_and, BitVec.testBit_toNat] at hb
  rw [BitVec.getLsbD_and, BitVec.getLsbD_zero]
  cases hc : c.getLsbD i
  · simp
  · simp only [hc] at hb
    simp [hx i hb]

theorem kzOk_of_and_zero {n : Nat} {x c : BitVec n} (h : x &&& c = 0#n) :
    KZOk (.bits n) x c.toNat := fun i hi => by
  have hb := congrArg (fun v => BitVec.getLsbD v i) h
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at hb
  rw [BitVec.testBit_toNat] at hi
  simpa [hi] using hb

theorem kzOk_of_and_zero' {n : Nat} {x c : BitVec n} (h : c &&& x = 0#n) :
    KZOk (.bits n) x c.toNat :=
  kzOk_of_and_zero (by rw [BitVec.and_comm]; exact h)

/-! ## Facts and identities -/

theorem kzOk_of_env {ρ : ABEnv} {i n n' : Nat} {v : BitVec n} {v' : BitVec n'} {m : Nat}
    (h : ρ i = some ⟨.bits n, v⟩) (h' : ρ i = some ⟨.bits n', v'⟩)
    (hm : KZOk (.bits n) v m) : KZOk (.bits n') v' m := by
  rw [h] at h'
  injection h' with h'
  injection h' with h1 h2
  injection h1 with hn
  subst hn
  cases h2
  exact hm

theorem factMask_ok {ρ : ABEnv} {b : Nat} {i n : Nat} {v : BitVec n}
    (hρ : ρ i = some ⟨.bits n, v⟩) : {F : List BitFact} → FactsOk ρ b F →
    KZOk (.bits n) v (factMask i F)
  | [], _ => KZOk.zero _ _
  | f :: F, hF => by
    have ih := factMask_ok hρ (F := F) fun g hg => hF g (List.mem_cons_of_mem _ hg)
    dsimp only [factMask]
    split
    · next hfi =>
      have hf := hF f List.mem_cons_self
      have hfi' : f.1 = i := beq_iff_eq.mp hfi
      exact KZOk.or (hf.2 n v (hfi' ▸ hρ)) ih
    · exact ih

theorem kzIn_ok {ρ : ABEnv} {b : Nat} {F : List BitFact} (hF : FactsOk ρ b F) {n : Nat}
    {a : ABInfo} {v : BitVec n} (ha : InfoOk ρ b (t := .bits n) a v) :
    KZOk (.bits n) v (a.kzIn F) := by
  unfold ABInfo.kzIn
  split
  · next i hid => exact KZOk.or ha.2.1 (factMask_ok (ha.1 i hid).2 hF)
  · exact ha.2.1

theorem ABShape.fact_ok {ρ : ABEnv} {b : Nat} {n : Nat} {a : ABInfo} {v : BitVec n}
    (o : Option (Val (.bits n))) (ha : InfoOk ρ b (t := .bits n) a v) {m : Nat}
    (hm : KZOk (.bits n) v m) : FactsOk ρ b (ABShape.fact (a, o) m) := by
  dsimp only [ABShape.fact]
  split
  · next i hid =>
    intro f hf
    rw [List.mem_singleton] at hf
    subst hf
    exact ⟨(ha.1 i hid).1, fun _ _ h' => kzOk_of_env (ha.1 i hid).2 h' hm⟩
  · exact FactsOk.nil

/-! ## Operand-level lemmas -/

theorem InfoOk.ofImm {ρ : ABEnv} {b : Nat} {t : Ty} (c : Val t) :
    InfoOk ρ b (ABInfo.ofImm t c) c :=
  ⟨(fun _ h => nomatch h), immKz_ok t c, fun _ => FactsOk.nil, fun _ => FactsOk.nil⟩

theorem ArgRel.abGood {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val} (hG : ABGoodCtx ρ b G)
    {t : Ty} : {a₁ : Arg (ABVal Val) t} → {a₂ : Arg Val t} → ArgRel G t a₁ a₂ →
    ABGoodArg ρ b a₁ a₂.val
  | .var _, _, .var h => hG _ h
  | .imm _, _, .imm c => ⟨rfl, InfoOk.ofImm c⟩

theorem ABGoodArg.toAB {ρ : ABEnv} {b : Nat} {t : Ty} {a : Arg (ABVal Val) t} {v : Val t}
    (h : ABGoodArg ρ b a v) : ABGood ρ b a.toAB v := by
  cases a <;> exact h

theorem ABGoodArg.imm_eq {ρ : ABEnv} {b : Nat} {t : Ty} {a : Arg (ABVal Val) t} {v c : Val t}
    (ha : ABGoodArg ρ b a v) (hc : a.abOut.imm? = some c) : v = c := by
  have h1 : a.abOut.val = v := ha.1
  cases ho : a.abOut with
  | var _ => rw [ho] at hc; cases hc
  | imm c' => rw [ho] at hc h1; cases hc; exact h1.symm

theorem TRel.abOut_vals {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val} (hG : ABGoodCtx ρ b G)
    {ts : List Ty} {as₁ : Tup (Arg (ABVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupAOut as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => Arg.abOut) (fun ha => (ha.abGood hG).1) h

theorem TRel.abGoodArgs {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val} (hG : ABGoodCtx ρ b G) :
    {ts : List Ty} → {as₁ : Tup (Arg (ABVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → TRel (fun _ a v => ABGoodArg ρ b a v) as₁ (vals as₂)
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons ha hs => .cons (ha.abGood hG) (TRel.abGoodArgs hG hs)

/-! ## Soundness of eliminations -/

/-- Values of the replacements selected by an elimination tuple. -/
def ABElim.eval {sig : List Ty} (vs : Tup Val sig) :
    {ts : List Ty} → Tup (fun u => ABElim sig u) ts → Tup Val ts
  | [], () => ()
  | _ :: _, (.arg i, act) => (vs.get i, ABElim.eval vs act)
  | _ :: _, (.imm c, act) => (c, ABElim.eval vs act)

theorem ABElim.apply_good {ρ : ABEnv} {b : Nat} {sig : List Ty}
    {args : Tup (Arg (ABVal Val)) sig} {vs : Tup Val sig}
    (hargs : TRel (fun _ a v => ABGoodArg ρ b a v) args vs) :
    {ts : List Ty} → (act : Tup (fun u => ABElim sig u) ts) →
    TRel (fun _ a v => ABGood ρ b a v) (ABElim.apply args act) (ABElim.eval vs act)
  | [], () => .nil
  | _ :: _, (.arg i, act) => .cons (TRel.get i hargs).toAB (ABElim.apply_good hargs act)
  | _ :: _, (.imm c, act) => .cons ⟨rfl, InfoOk.ofImm c⟩ (ABElim.apply_good hargs act)

private theorem andElim?_cases {n kz : Nat} {c : BitVec n}
    {i : Member (Ty.bits n) [Ty.bits n, Ty.bits n]}
    {act : Tup (fun u => ABElim [Ty.bits n, Ty.bits n] u) [Ty.bits n]}
    (h : andElim? n kz c i = some act) {x : BitVec n} (hx : KZOk (.bits n) x kz) :
    (act = (.arg i, ()) ∧ x &&& c = x) ∨ (act = (.imm 0#n, ()) ∧ x &&& c = 0#n) := by
  unfold andElim? at h
  split at h
  · next hk => cases h; exact .inl ⟨rfl, andKeeps_eq hk hx⟩
  · split at h
    · next hk => cases h; exact .inr ⟨rfl, andKills_eq hk hx⟩
    · cases h

theorem abElim?_sound {ρ : ABEnv} {b : Nat} {F : List BitFact} (hF : FactsOk ρ b F)
    {sig ts : List Ty} {code : OpCode sig ts} {args : Tup (Arg (ABVal Val)) sig}
    {vs : Tup Val sig} (hargs : TRel (fun _ a v => ABGoodArg ρ b a v) args vs)
    {act : Tup (fun u => ABElim sig u) ts} (hact : abElim? code (tupABShape args) F = some act)
    {P : Tup Val ts → Prop} (hw : code.wp vs P) : P (ABElim.eval vs act) := by
  cases code with
  | copy t =>
    obtain ⟨a, ⟨⟩⟩ := args
    obtain ⟨va, ⟨⟩⟩ := vs
    cases hact
    exact hw
  | and t =>
    obtain ⟨a, c, ⟨⟩⟩ := args
    obtain ⟨va, vc, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _ | ⟨hc, _⟩⟩
    cases t with
    | bits n =>
      have hw' : P (va &&& vc, ()) := hw
      dsimp only [abElim?, tupABShape, Tup.map, Arg.abShape] at hact
      cases hci : c.abOut.imm? with
      | some k =>
        rw [hci] at hact
        have hk := hc.imm_eq hci
        subst hk
        rcases andElim?_cases hact (kzIn_ok hF ha.2) with ⟨rfl, he⟩ | ⟨rfl, he⟩
        · exact he ▸ hw'
        · exact he ▸ hw'
      | none =>
        rw [hci] at hact
        cases hai : a.abOut.imm? with
        | some k =>
          rw [hai] at hact
          have hk := ha.imm_eq hai
          subst hk
          rcases andElim?_cases hact (kzIn_ok hF hc.2) with ⟨rfl, he⟩ | ⟨rfl, he⟩
          · rw [BitVec.and_comm] at he; exact he ▸ hw'
          · rw [BitVec.and_comm] at he; exact he ▸ hw'
        | none => rw [hai] at hact; cases hact
    | bool => cases hact
    | float _ => cases hact
    | pair _ _ => cases hact
  | _ => cases hact

/-! ## Soundness of result metadata -/

/-- The metadata `r` is sound for the first result of `ys`. -/
def ResOk (ρ : ABEnv) (b : Nat) (r : ABRes) : {ts : List Ty} → Tup Val ts → Prop
  | [], () => True
  | t :: _, (y, _) =>
    KZOk t y r.kz ∧ (ZeroV t y → FactsOk ρ b r.zf) ∧ (NzV t y → FactsOk ρ b r.nf)

theorem ResOk.empty {ρ : ABEnv} {b : Nat} : {ts : List Ty} → (ys : Tup Val ts) →
    ResOk ρ b {} ys
  | [], () => trivial
  | t :: _, (y, _) => ⟨KZOk.zero t y, fun _ => FactsOk.nil, fun _ => FactsOk.nil⟩

section ResLemmas
variable {ρ : ABEnv} {b : Nat} {F : List BitFact}

private theorem andRes_ok (hF : FactsOk ρ b F) {n : Nat} {a c : Arg (ABVal Val) (.bits n)}
    {va vc : BitVec n} (ha : ABGoodArg ρ b a va) (hc : ABGoodArg ρ b c vc) :
    ResOk ρ b (andRes (.bits n) a.abShape c.abShape F) (ts := [.bits n]) (va &&& vc, ()) := by
  refine ⟨KZOk.or (fun i hi => ?_) (fun i hi => ?_), fun hz => ?_, fun _ => FactsOk.nil⟩
  · rw [BitVec.getLsbD_and, kzIn_ok hF ha.2 i hi, Bool.false_and]
  · rw [BitVec.getLsbD_and, kzIn_ok hF hc.2 i hi, Bool.and_false]
  · have hz' : va &&& vc = 0#n := hz
    dsimp only [andRes, Arg.abShape]
    cases hci : c.abOut.imm? with
    | some k =>
      have hk := hc.imm_eq hci
      subst hk
      exact ABShape.fact_ok _ ha.2 (kzOk_of_and_zero hz')
    | none =>
      cases hai : a.abOut.imm? with
      | some k =>
        have hk := ha.imm_eq hai
        subst hk
        exact ABShape.fact_ok _ hc.2 (kzOk_of_and_zero' hz')
      | none => exact FactsOk.nil

private theorem orRes_kz (hF : FactsOk ρ b F) {n : Nat} {a c : Arg (ABVal Val) (.bits n)}
    {va vc r : BitVec n} (ha : ABGoodArg ρ b a va) (hc : ABGoodArg ρ b c vc)
    (hr : ∀ i, va.getLsbD i = false → vc.getLsbD i = false → r.getLsbD i = false) :
    ResOk ρ b (orRes (.bits n) a.abShape c.abShape F) (ts := [.bits n]) (r, ()) := by
  refine ⟨fun i hi => ?_, fun _ => FactsOk.nil, fun _ => FactsOk.nil⟩
  dsimp only [orRes, Arg.abShape] at hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi
  exact hr i (kzIn_ok hF ha.2 i hi.1) (kzIn_ok hF hc.2 i hi.2)

private theorem lshrRes_ok (hF : FactsOk ρ b F) {n : Nat} {a c : Arg (ABVal Val) (.bits n)}
    {va vc : BitVec n} (ha : ABGoodArg ρ b a va) (hc : ABGoodArg ρ b c vc) :
    ResOk ρ b (lshrRes (.bits n) a.abShape c.abShape F) (ts := [.bits n])
      (va >>> (vc.toNat % n), ()) := by
  dsimp only [lshrRes, Arg.abShape]
  cases hci : c.abOut.imm? with
  | none => exact ResOk.empty _
  | some k =>
    have hk := hc.imm_eq hci
    subst hk
    refine ⟨KZOk.or (fun i hi => ?_) (fun i hi => ?_), fun _ => FactsOk.nil, fun _ => FactsOk.nil⟩
    · rw [Nat.testBit_shiftRight] at hi
      rw [BitVec.getLsbD_ushiftRight]
      exact kzIn_ok hF ha.2 _ hi
    · have h := highFrom_testBit hi
      rw [BitVec.getLsbD_ushiftRight]
      exact BitVec.getLsbD_of_ge va _ (by omega)

private theorem shlRes_ok (hF : FactsOk ρ b F) {n : Nat} {a c : Arg (ABVal Val) (.bits n)}
    {va vc : BitVec n} (ha : ABGoodArg ρ b a va) (hc : ABGoodArg ρ b c vc) :
    ResOk ρ b (shlRes (.bits n) a.abShape c.abShape F) (ts := [.bits n])
      (va <<< (vc.toNat % n), ()) := by
  dsimp only [shlRes, Arg.abShape]
  cases hci : c.abOut.imm? with
  | none => exact ResOk.empty _
  | some k =>
    have hk := hc.imm_eq hci
    subst hk
    refine ⟨KZOk.or (fun i hi => ?_) (fun i hi => ?_), fun _ => FactsOk.nil, fun _ => FactsOk.nil⟩
    · rw [Nat.testBit_shiftLeft] at hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
      rw [BitVec.getLsbD_shiftLeft, kzIn_ok hF ha.2 _ hi.2, Bool.and_false]
    · rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at hi
      simp [BitVec.getLsbD_shiftLeft, hi]

private theorem notRes_ok {a : Arg (ABVal Val) .bool} {va : Bool} (ha : ABGoodArg ρ b a va) :
    ResOk ρ b (notRes .bool a.abShape) (ts := [.bool]) (!va, ()) := by
  refine ⟨trivial, fun hz => ?_, fun hn => ?_⟩
  · have hz' : (!va) = false := hz
    exact ha.2.2.2.2 (show va = true by simpa using hz')
  · have hn' : (!va) = true := hn
    exact ha.2.2.2.1 (show va = false by simpa using hn')

private theorem signBit_kz {n : Nat} {v : BitVec n} (h : v.msb = false) :
    KZOk (.bits n) v (signBit n) := fun i hi => by
  unfold signBit at hi
  rw [Nat.testBit_two_pow, decide_eq_true_eq] at hi
  subst hi
  rw [← BitVec.msb_eq_getLsbD_last]
  exact h

private theorem ltBits_kz {n : Nat} {v c : BitVec n} (h : v.toNat < c.toNat) :
    KZOk (.bits n) v (highFrom n (ltBits c.toNat)) := fun i hi => by
  have h1 := highFrom_testBit hi
  have h2 : v.toNat < 2 ^ ltBits c.toNat := by
    have := Nat.lt_log2_self (n := c.toNat - 1)
    unfold ltBits
    omega
  have h3 : v.toNat < 2 ^ i :=
    Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) h1.1)
  rw [← BitVec.testBit_toNat]
  exact Nat.testBit_lt_two_pow h3

private theorem cmpRes_ok {o : CmpOp} {n : Nat} {a c : Arg (ABVal Val) (.bits n)}
    {va vc : BitVec n} (ha : ABGoodArg ρ b a va) (hc : ABGoodArg ρ b c vc) :
    ResOk ρ b (cmpRes o n a.abShape c.abShape) (ts := [.bool]) (o.evalBits va vc, ()) := by
  dsimp only [cmpRes, Arg.abShape]
  cases hci : c.abOut.imm? with
  | none => cases o <;> exact ResOk.empty _
  | some k =>
    have hk := hc.imm_eq hci
    subst hk
    cases o with
    | ne =>
      dsimp only
      split
      · next h0 =>
        rw [beq_iff_eq] at h0
        subst h0
        refine ⟨trivial, fun hz => ha.2.2.2.1 ?_, fun hn => ha.2.2.2.2 ?_⟩
        · have hz' : decide (va ≠ 0#n) = false := hz
          show va = 0#n
          simpa using hz'
        · have hn' : decide (va ≠ 0#n) = true := hn
          show va ≠ 0#n
          simpa using hn'
      · exact ResOk.empty _
    | eq =>
      dsimp only
      split
      · next h0 =>
        rw [beq_iff_eq] at h0
        subst h0
        refine ⟨trivial, fun hz => ha.2.2.2.2 ?_, fun hn => ha.2.2.2.1 ?_⟩
        · have hz' : decide (va = 0#n) = false := hz
          show va ≠ 0#n
          simpa using hz'
        · have hn' : decide (va = 0#n) = true := hn
          show va = 0#n
          simpa using hn'
      · exact ResOk.empty _
    | slt =>
      dsimp only
      split
      · next h0 =>
        rw [beq_iff_eq] at h0
        subst h0
        refine ⟨trivial, fun hz => ABShape.fact_ok _ ha.2 (signBit_kz ?_), fun _ => FactsOk.nil⟩
        have hz' : va.slt 0#n = false := hz
        rwa [BitVec.slt_zero_eq_msb] at hz'
      · exact ResOk.empty _
    | sge =>
      dsimp only
      split
      · next h0 =>
        rw [beq_iff_eq] at h0
        subst h0
        refine ⟨trivial, fun _ => FactsOk.nil, fun hn => ABShape.fact_ok _ ha.2 (signBit_kz ?_)⟩
        have hn' : (0#n).sle va = true := hn
        rw [BitVec.sle_eq_not_slt, BitVec.slt_zero_eq_msb, Bool.not_eq_true'] at hn'
        exact hn'
      · exact ResOk.empty _
    | ult =>
      refine ⟨trivial, fun _ => FactsOk.nil, fun hn => ABShape.fact_ok _ ha.2 (ltBits_kz ?_)⟩
      have hn' : va.ult vc = true := hn
      simpa [BitVec.ult] using hn'
    | uge =>
      refine ⟨trivial, fun hz => ABShape.fact_ok _ ha.2 (ltBits_kz ?_), fun _ => FactsOk.nil⟩
      have hz' : vc.ule va = false := hz
      simp only [BitVec.ule, decide_eq_false_iff_not, Nat.not_le] at hz'
      exact hz'
    | ule | ugt | sle | sgt => exact ResOk.empty _

end ResLemmas

theorem abRes_ok {ρ : ABEnv} {b : Nat} {F : List BitFact} (hF : FactsOk ρ b F)
    {sig ts : List Ty} (code : OpCode sig ts) {args : Tup (Arg (ABVal Val)) sig}
    {vs : Tup Val sig} (hargs : TRel (fun _ a v => ABGoodArg ρ b a v) args vs)
    {P : Tup Val ts → Prop} (hw : code.wp vs P) :
    code.wp vs (fun ys => P ys ∧ ResOk ρ b (abRes code (tupABShape args) F) ys) := by
  cases code with
  | and t =>
    obtain ⟨a, c, ⟨⟩⟩ := args
    obtain ⟨va, vc, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _ | ⟨hc, _⟩⟩
    cases t with
    | bits n => exact ⟨hw, andRes_ok hF ha hc⟩
    | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw
  | or t =>
    obtain ⟨a, c, ⟨⟩⟩ := args
    obtain ⟨va, vc, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _ | ⟨hc, _⟩⟩
    cases t with
    | bits n =>
      refine ⟨hw, orRes_kz hF ha hc fun i h1 h2 => ?_⟩
      show BitVec.getLsbD (va ||| vc) i = false
      rw [BitVec.getLsbD_or, h1, h2, Bool.or_false]
    | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw
  | xor t =>
    obtain ⟨a, c, ⟨⟩⟩ := args
    obtain ⟨va, vc, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _ | ⟨hc, _⟩⟩
    cases t with
    | bits n =>
      refine ⟨hw, orRes_kz hF ha hc fun i h1 h2 => ?_⟩
      show BitVec.getLsbD (va ^^^ vc) i = false
      rw [BitVec.getLsbD_xor, h1, h2, Bool.xor_false]
    | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw
  | not t =>
    obtain ⟨a, ⟨⟩⟩ := args
    obtain ⟨va, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _⟩
    cases t with
    | bool => exact ⟨hw, notRes_ok ha⟩
    | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw
  | lshr t =>
    obtain ⟨a, c, ⟨⟩⟩ := args
    obtain ⟨va, vc, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _ | ⟨hc, _⟩⟩
    cases t with
    | bits n => exact ⟨hw, lshrRes_ok hF ha hc⟩
    | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw
  | shl t =>
    obtain ⟨a, c, ⟨⟩⟩ := args
    obtain ⟨va, vc, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _ | ⟨hc, _⟩⟩
    cases t with
    | bits n => exact ⟨hw, shlRes_ok hF ha hc⟩
    | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw
  | select t =>
    obtain ⟨cc, a, c, ⟨⟩⟩ := args
    obtain ⟨vcc, va, vc, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨_, _ | ⟨ha, _ | ⟨hc, _⟩⟩⟩
    cases t with
    | bits n =>
      refine ⟨hw, orRes_kz hF ha hc fun i h1 h2 => ?_⟩
      cases vcc <;> assumption
    | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw
  | zext m n =>
    obtain ⟨a, ⟨⟩⟩ := args
    obtain ⟨va, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _⟩
    refine ⟨hw.1, hw.2, KZOk.or (fun i hi => ?_) (fun i hi => ?_), fun _ => FactsOk.nil,
      fun _ => FactsOk.nil⟩
    · rw [BitVec.getLsbD_setWidth, kzIn_ok hF ha.2 i hi, Bool.and_false]
    · rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_of_ge va i (highFrom_testBit hi).1,
        Bool.and_false]
  | trunc m n =>
    obtain ⟨a, ⟨⟩⟩ := args
    obtain ⟨va, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _⟩
    refine ⟨hw.1, hw.2, fun i hi => ?_, fun _ => FactsOk.nil, fun _ => FactsOk.nil⟩
    rw [BitVec.getLsbD_setWidth, kzIn_ok hF ha.2 i hi, Bool.and_false]
  | ofBool n =>
    obtain ⟨a, ⟨⟩⟩ := args
    obtain ⟨va, ⟨⟩⟩ := vs
    refine ⟨hw, fun i hi => ?_, fun _ => FactsOk.nil, fun _ => FactsOk.nil⟩
    have h1 := (highFrom_testBit hi).1
    have hlt : va.toNat < 2 ^ i :=
      Nat.lt_of_lt_of_le (Bool.toNat_lt va) (by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) h1)
    rw [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow hlt, Bool.and_false]
  | cmp o t m h =>
    obtain ⟨a, c, ⟨⟩⟩ := args
    obtain ⟨va, vc, ⟨⟩⟩ := vs
    rcases hargs with _ | ⟨ha, _ | ⟨hc, _⟩⟩
    subst h
    cases t with
    | bits n => exact ⟨hw, cmpRes_ok ha hc⟩
    | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw
  | _ => exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy, ResOk.empty ys⟩) hw

/-! ## Emission and `Op.abLet` soundness -/

theorem abWrap_good {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val} (hG : ABGoodCtx ρ b G)
    (r : ABRes) : {ts : List Ty} → (ys : Tup Val ts) → ResOk ρ b r ys →
    ABGoodCtx (ABEnv.updTup ρ b ys) (b + ts.length) (Tup.zip (abWrap r ts ys b) ys ++ G)
  | [], (), _ => hG
  | t :: ts, (y, ys), ⟨hk, hz, hn⟩ => by
    dsimp only [abWrap, Tup.zip, ABEnv.updTup]
    have hρ : ∀ k, k < b → ABEnv.upd ρ b y k = ρ k := fun k hk => ABEnv.upd_ne ρ y (by omega)
    have hG1 : ABGoodCtx (ABEnv.upd ρ b y) (b + 1) G := hG.mono (by omega) hρ
    have hfresh := ABGoodCtx.freshABVals hG1 ys
    rw [List.length_cons, show b + (ts.length + 1) = b + 1 + ts.length by omega]
    have hρ' : ∀ k, k < b →
        ABEnv.updTup (ABEnv.upd ρ b y) (b + 1) ys k = ρ k := fun k hk => by
      rw [ABEnv.updTup_lt _ ys (by omega)]; exact hρ k hk
    refine hfresh.cons ⟨rfl, fun k hk' => ?_, hk, fun h => (hz h).mono (by omega) hρ',
      fun h => (hn h).mono (by omega) hρ'⟩
    cases hk'
    exact ⟨by omega, by rw [ABEnv.updTup_lt _ ys (by omega), ABEnv.upd_eq]⟩

theorem OpRel.abLet_wp {ρ : ABEnv} {b : Nat} {G : Ctx (ABVal Val) Val} {F : List BitFact}
    (hG : ABGoodCtx ρ b G) (hF : FactsOk ρ b F) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (ABVal Val)) sig} {args₂ : Tup (Arg Val) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) {P : Tup Val ts → Prop} (hw : code.wp (vals args₂) P) :
    match ({ code := code, args := args₁ } : Op (ABVal Val) ts).abLet F b with
    | .elim res => ∃ ys, P ys ∧ ABGoodCtx ρ b (Tup.zip res ys ++ G)
    | .emit op' wrap =>
      op'.wp fun ys =>
        P ys ∧ ABGoodCtx (ABEnv.updTup ρ b ys) (b + ts.length) (Tup.zip (wrap ys) ys ++ G) := by
  have hga := TRel.abGoodArgs hG hargs
  dsimp only [Op.abLet]
  cases hact : abElim? code (tupABShape args₁) F with
  | some act =>
    exact ⟨_, abElim?_sound hF hga hact hw, hG.append_tup (ABElim.apply_good hga act)⟩
  | none =>
    dsimp only [Op.wp]
    rw [TRel.abOut_vals hG hargs]
    exact OpCode.wp_mono _ _ (fun ys hy => ⟨hy.1, abWrap_good hG _ ys hy.2⟩)
      (abRes_ok hF code hga hw)

/-! ## `assumeBits_wp` via `Wf.induct` -/

theorem assumeBitsB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (b : Nat)
    (F : List BitFact) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (ABVal V) L rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (assumeBitsB b F bs).get i xs = assumeBits (b + ts.length) F (bs.get i (freshABVals ts xs b))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => assumeBitsB_get b F bs i xs

private theorem assumeBits_let {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (next : Nat) (F : List BitFact) (op : Op (ABVal V) ts)
    (k : Tup (ABVal V) ts → Expr (ABVal V) L rs) :
    assumeBits next F (.let_ op k) =
      match op.abLet F next with
      | .elim res => assumeBits next F (k res)
      | .emit op' wrap => .let_ op' fun xs => assumeBits (next + ts.length) F (k (wrap xs)) := by
  delta assumeBits; dsimp only [Expr.brecOn, Expr.rec, assumeBits._f]
  cases op.abLet F next <;> rfl

/-- Weakest-precondition preservation for `assumeBits`: every in-scope fact holds, so every
elimination and every branch-implied fact is sound. -/
theorem assumeBits_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (ABVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (ABVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ b ρ F, ABGoodCtx ρ b G → FactsOk ρ b F →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (assumeBits b F e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD b ρ F hG hF m hw
    dsimp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hstep := OpRel.abLet_wp hG hF hargs hw
      rw [assumeBits_let]
      cases hcl : ({ code := code, args := args₁ } : Op (ABVal Val) ts).abLet F b with
      | elim res =>
        rw [hcl] at hstep
        rcases hstep with ⟨ys, hk2, hG'⟩
        exact ih res ys hD b ρ F hG' hF m hk2
      | emit op' wrap =>
        rw [hcl] at hstep
        dsimp only [wp]
        exact Op.wp_mono (fun ys hy =>
          ih (wrap ys) ys hD (b + ts.length) _ F hy.2 (hF.updTup ys) m hy.1) hstep
  | load t ha _ ih =>
    intro hD b ρ F hG hF m hw
    dsimp only [wp, assumeBits] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, (ha.abGood hG).1 ▸ hv,
      ih (ABVal.fresh v b) v hD (b + 1) (ABEnv.upd ρ b v) F (hG.freshOne v)
        (hF.updTup (ts := [t]) (v, ())) m hk⟩
  | store hv ha _ ih =>
    intro hD b ρ F hG hF m hw
    dsimp only [wp, assumeBits] at hw ⊢
    rw [(ha.abGood hG).1, (hv.abGood hG).1]
    exact ⟨hw.1, ih hD b ρ F hG hF _ hw.2⟩
  | call f hargs _ ih =>
    intro hD b ρ F hG hF m hw
    dsimp only [wp, assumeBits] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    rw [hargs.abOut_vals hG]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshABVals _ r b) r hD (b + _) (ABEnv.updTup ρ b r) F (hG.freshABVals r)
        (hF.updTup r) m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hD b ρ F hG hF m hw
    dsimp only [wp, assumeBits] at hw ⊢
    have hcg := hc.abGood hG
    rw [hcg.1]
    exact ⟨fun h => iht hD b ρ _ hG ((hcg.2.2.2.2 h).append hF) m (hw.1 h),
      fun h => ihe hD b ρ _ hG ((hcg.2.2.2.1 h).append hF) m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD b ρ F hG _ m hw
    have hj' := hD _ hj
    dsimp only at hj'
    dsimp only [wp, assumeBits] at hw ⊢
    rw [hj', hargs.abOut_vals hG]
    exact hw
  | ret hvs =>
    intro _ b ρ F hG _ m hw
    dsimp only [wp, assumeBits] at hw ⊢
    rw [hvs.abOut_vals hG]
    exact hw
  | exit f hargs =>
    intro _ b ρ F hG _ m hw
    dsimp only [wp, assumeBits] at hw ⊢
    rw [hargs.abOut_vals hG]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ hw
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD b ρ F hG hF m hw
    dsimp only [wp, assumeBits] at hw ⊢
    intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) b ρ F hG hF m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb
    have h := ihb Js Js i (freshABVals ts xs b) xs (tup_zip_self_eq hD Js) (b + ts.length)
      (ABEnv.updTup ρ b xs) F (hG.freshABVals xs) (hF.updTup xs) m' hb
    rw [← assumeBitsB_get b F (b₁ Js) i xs] at h
    exact hclosed i xs m' h

/-! ## Relational well-formedness (`ABRelG` and `assumeBits_wf`) -/

section
variable {V₁ V₂ : Ty → Type}

/-- Two `ABVal`s are related when their operands are related and their metadata agree. -/
def ABRelVal (G' : Ctx V₁ V₂) {t : Ty} (a₁ : ABVal V₁ t) (a₂ : ABVal V₂ t) : Prop :=
  ArgRel G' t a₁.out a₂.out ∧ a₁.info = a₂.info

/-- Every entry of `G` is related under `G'`. -/
def ABRelG (G' : Ctx V₁ V₂) (G : Ctx (ABVal V₁) (ABVal V₂)) : Prop :=
  ∀ p ∈ G, ABRelVal G' p.2.1 p.2.2

theorem ABRelVal.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) {t : Ty}
    {a₁ : ABVal V₁ t} {a₂ : ABVal V₂ t} (h : ABRelVal G₁ a₁ a₂) : ABRelVal G₂ a₁ a₂ :=
  ⟨h.1.weaken hsub, h.2⟩

theorem ABRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    {t : Ty} {a₁ : ABVal V₁ t} {a₂ : ABVal V₂ t} (ha : ABRelVal G' a₁ a₂) :
    ABRelG G' (⟨t, a₁, a₂⟩ :: G)
  | _, .head _ => ha
  | _, .tail _ hp => hG _ hp

theorem ABRelG.weaken {G' G'' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    (hsub : ∀ p ∈ G', p ∈ G'') : ABRelG G'' G :=
  fun p hp => (hG p hp).weaken hsub

theorem ABRelG.append_tup {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G) :
    {ts : List Ty} → {r₁ : Tup (ABVal V₁) ts} → {r₂ : Tup (ABVal V₂) ts} →
    TRel (fun _ => ABRelVal G') r₁ r₂ → ABRelG G' (Tup.zip r₁ r₂ ++ G)
  | [], (), (), .nil => hG
  | _ :: _, (_, _), (_, _), .cons hr hs => (ABRelG.append_tup hG hs).cons hr

theorem ABRelVal.fresh {G' : Ctx V₁ V₂} {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t} (b : Nat)
    (hm : ⟨t, v₁, v₂⟩ ∈ G') : ABRelVal G' (ABVal.fresh v₁ b) (ABVal.fresh v₂ b) :=
  ⟨.var hm, rfl⟩

private theorem ABRelG.freshABVals_only {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts)
    (b : Nat) :
    ABRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshABVals ts xs₁ b) (freshABVals ts xs₂ b)) :=
  mem_tup_zip_tupFreshWith (fun x n => ABVal.fresh x n) (fun x n => ABVal.fresh x n)
    (P := fun G' _ c₁ c₂ => ABRelVal G' c₁ c₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ idx => ABRelVal.fresh idx List.mem_cons_self)
    xs₁ xs₂ b

theorem ABRelG.freshABVals {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    ABRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshABVals ts xs₁ b) (freshABVals ts xs₂ b) ++ G) := fun p hp =>
  (List.mem_append.1 hp).elim
    (fun hp => (ABRelG.freshABVals_only xs₁ xs₂ b p hp).weaken
      fun _ hq => List.mem_append_left G' hq)
    (fun hp => (hG p hp).weaken fun _ hq => List.mem_append_right _ hq)

theorem ABRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    ABRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, ABVal.fresh v₁ b, ABVal.fresh v₂ b⟩ :: G) :=
  (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq).cons (ABRelVal.fresh b List.mem_cons_self)

theorem TRel.freshABVals_rel {G' : Ctx V₁ V₂} {ts : List Ty} (xs₁ : Tup V₁ ts)
    (xs₂ : Tup V₂ ts) (b : Nat) :
    TRel (fun _ => ABRelVal (Tup.zip xs₁ xs₂ ++ G')) (freshABVals ts xs₁ b)
      (freshABVals ts xs₂ b) :=
  TRel_tupFreshWith (fun x n => ABVal.fresh x n) (fun x n => ABVal.fresh x n)
    (P := fun G' _ c₁ c₂ => ABRelVal G' c₁ c₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ idx => ABRelVal.fresh idx List.mem_cons_self)
    xs₁ xs₂ b

theorem ArgRel.abRel {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    {t : Ty} : {a₁ : Arg (ABVal V₁) t} → {a₂ : Arg (ABVal V₂) t} → ArgRel G t a₁ a₂ →
    ArgRel G' t a₁.abOut a₂.abOut ∧ a₁.abInfo = a₂.abInfo
  | .var _, .var _, .var h => hG _ h
  | .imm c, _, .imm _ => ⟨.imm c, rfl⟩

theorem ArgRel.toAB_rel {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    {t : Ty} : {a₁ : Arg (ABVal V₁) t} → {a₂ : Arg (ABVal V₂) t} → ArgRel G t a₁ a₂ →
    ABRelVal G' a₁.toAB a₂.toAB
  | .var _, .var _, .var h => hG _ h
  | .imm c, _, .imm _ => ⟨.imm c, rfl⟩

theorem ArgRel.abShape_eq {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    {t : Ty} {a₁ : Arg (ABVal V₁) t} {a₂ : Arg (ABVal V₂) t} (h : ArgRel G t a₁ a₂) :
    a₁.abShape = a₂.abShape := by
  obtain ⟨ho, hi⟩ := h.abRel hG
  dsimp only [Arg.abShape]
  rw [hi]
  generalize a₁.abOut = o₁ at ho ⊢
  generalize a₂.abOut = o₂ at ho ⊢
  cases ho <;> rfl

theorem TRel.tupABShape_eq {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G) :
    {ts : List Ty} → {as₁ : Tup (Arg (ABVal V₁)) ts} → {as₂ : Tup (Arg (ABVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ → tupABShape as₁ = tupABShape as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => by
    dsimp only [tupABShape, Tup.map]
    rw [h.abShape_eq hG]
    exact congrArg _ (TRel.tupABShape_eq hG hs)

theorem TRel.abOut_rel {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    {ts : List Ty} {as₁ : Tup (Arg (ABVal V₁)) ts} {as₂ : Tup (Arg (ABVal V₂)) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') (tupAOut as₁) (tupAOut as₂) :=
  TRel.tupMapArg_rel (fun _ => Arg.abOut) (fun _ => Arg.abOut) (fun ha => (ha.abRel hG).1) h

theorem ABElim.apply_rel {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    {sig : List Ty} {args₁ : Tup (Arg (ABVal V₁)) sig} {args₂ : Tup (Arg (ABVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    {ts : List Ty} → (act : Tup (fun u => ABElim sig u) ts) →
    TRel (fun _ => ABRelVal G') (ABElim.apply args₁ act) (ABElim.apply args₂ act)
  | [], () => .nil
  | _ :: _, (.arg i, act) => .cons ((TRel.get i hargs).toAB_rel hG) (ABElim.apply_rel hG hargs act)
  | _ :: _, (.imm c, act) => .cons ⟨.imm c, rfl⟩ (ABElim.apply_rel hG hargs act)

theorem abWrap_rel {G' : Ctx V₁ V₂} (r : ABRes) (b : Nat) :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    TRel (fun _ => ABRelVal (Tup.zip xs₁ xs₂ ++ G')) (abWrap r ts xs₁ b) (abWrap r ts xs₂ b)
  | [], (), () => .nil
  | _ :: _, (_, xs₁), (_, xs₂) =>
    .cons ⟨.var List.mem_cons_self, rfl⟩
      (TRel.mono (fun _ _ _ h => h.weaken fun _ hq => List.mem_cons_of_mem _ hq)
        (TRel.freshABVals_rel (G' := G') xs₁ xs₂ (b + 1)))

/-- Relation between the `let_` lowering steps of two related instantiations. -/
inductive ABStepRel (G' : Ctx V₁ V₂) :
    {ts : List Ty} → ABLetStep V₁ ts → ABLetStep V₂ ts → Prop
  | elim {ts : List Ty} {r₁ : Tup (ABVal V₁) ts} {r₂ : Tup (ABVal V₂) ts} :
      TRel (fun _ => ABRelVal G') r₁ r₂ → ABStepRel G' (.elim r₁) (.elim r₂)
  | emit {ts : List Ty} {o₁ : Op V₁ ts} {o₂ : Op V₂ ts}
      {w₁ : Tup V₁ ts → Tup (ABVal V₁) ts} {w₂ : Tup V₂ ts → Tup (ABVal V₂) ts} :
      OpRel G' o₁ o₂ →
      (∀ xs₁ xs₂, TRel (fun _ => ABRelVal (Tup.zip xs₁ xs₂ ++ G')) (w₁ xs₁) (w₂ xs₂)) →
      ABStepRel G' (.emit o₁ w₁) (.emit o₂ w₂)

theorem OpRel.abLet_rel {G' : Ctx V₁ V₂} {G : Ctx (ABVal V₁) (ABVal V₂)} (hG : ABRelG G' G)
    (F : List BitFact) (b : Nat) {sig ts : List Ty} {code : OpCode sig ts}
    {args₁ : Tup (Arg (ABVal V₁)) sig} {args₂ : Tup (Arg (ABVal V₂)) sig}
    (hargs : TRel (ArgRel G) args₁ args₂) :
    ABStepRel G' (({ code := code, args := args₁ } : Op (ABVal V₁) ts).abLet F b)
      (({ code := code, args := args₂ } : Op (ABVal V₂) ts).abLet F b) := by
  dsimp only [Op.abLet]
  rw [TRel.tupABShape_eq hG hargs]
  cases abElim? code (tupABShape args₂) F with
  | some act => exact .elim (ABElim.apply_rel hG hargs act)
  | none =>
    exact .emit (.mk code (TRel.abOut_rel hG hargs)) fun xs₁ xs₂ => abWrap_rel _ b xs₁ xs₂

end

/-- Well-formedness preservation for `assumeBits`, proved via `Wf.induct`. -/
theorem assumeBits_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (ABVal V₁) (ABVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (ABVal V₁) L₁ rs} {e₂ : Expr (ABVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, ABRelG G' G → ∀ b F, Wf G' D (assumeBits b F e₁) (assumeBits b F e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG b F
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hrel := OpRel.abLet_rel hG F b hargs (code := code)
      rw [assumeBits_let, assumeBits_let]
      generalize ({ code := code, args := args₁ } : Op (ABVal V₁) ts).abLet F b = st₁ at hrel ⊢
      generalize ({ code := code, args := args₂ } : Op (ABVal V₂) ts).abLet F b = st₂ at hrel ⊢
      cases hrel with
      | elim hr => exact ih _ _ (hG.append_tup hr) b F
      | emit hop' hw =>
        refine .let_ hop' fun xs₁ xs₂ => ?_
        have hG' : ABRelG (Tup.zip xs₁ xs₂ ++ G') G :=
          hG.weaken fun _ hq => List.mem_append_right _ hq
        exact ih _ _ (hG'.append_tup (hw xs₁ xs₂)) (b + ts.length) F
  | load t ha _ ih =>
    intro G' hG b F
    exact .load t (ha.abRel hG).1 fun v₁ v₂ => ih _ _ (hG.freshOne v₁ v₂ b) (b + 1) F
  | store hv ha _ ih =>
    intro G' hG b F
    exact .store (hv.abRel hG).1 (ha.abRel hG).1 (ih hG b F)
  | call f hargs _ ih =>
    intro G' hG b F
    exact .call f (TRel.abOut_rel hG hargs) fun xs₁ xs₂ =>
      ih _ _ (hG.freshABVals xs₁ xs₂ b) (b + _) F
  | jnz hc _ _ iht ihe =>
    intro G' hG b F
    obtain ⟨ho, hi⟩ := hc.abRel hG
    dsimp only [assumeBits]
    rw [hi]
    exact .jnz ho (iht hG b _) (ihe hG b _)
  | jump hj hargs =>
    intro G' hG _ _
    exact .jump hj (TRel.abOut_rel hG hargs)
  | ret hvs =>
    intro G' hG _ _
    exact .ret (TRel.abOut_rel hG hvs)
  | exit f hargs =>
    intro G' hG _ _
    exact .exit f (TRel.abOut_rel hG hargs)
  | hlt =>
    intro _ _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hG b F
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hG b F)
    rw [assumeBitsB_get, assumeBitsB_get]
    exact ihb Js₁ Js₂ i _ _ (hG.freshABVals xs₁ xs₂ b) (b + _) F

/-! ## Call/exit well-scopedness (`assumeBits_callsOk`) -/

private theorem assumeBitsB_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (b : Nat) (F : List BitFact) :
    {sig : List (List Ty)} → (bs₁ : Blocks (ABVal (fun _ => Unit)) (fun _ => Unit) rs sig) →
    (bs₂ : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    (∀ {ts} (i : Member ts sig), (bs₂.get i (Tup.units ts)).callsOk allowed exits →
      (assumeBits (b + ts.length) F (bs₁.get i (freshABVals ts (Tup.units ts) b))).callsOk
        allowed exits) →
    bs₂.callsOk allowed exits → (assumeBitsB b F bs₁).callsOk allowed exits
  | _, .nil, .nil, _, _ => trivial
  | _, .cons _ _, .cons _ _, h, hc =>
    ⟨h .here hc.1, assumeBitsB_callsOk b F _ _ (fun i => h (.there i)) hc.2⟩

/-- `assumeBits` keeps every call (same symbol and signature) and every exit. -/
theorem assumeBits_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (ABVal (fun _ => Unit)) (fun _ => Unit)} {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (ABVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b F, e₂.callsOk allowed exits → (assumeBits b F e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ _ _ ih =>
    intro b F hc
    rw [assumeBits_let]
    cases op₁.abLet F b with
    | elim res => exact ih res (Tup.units ts) b F hc
    | emit op' wrap => exact ih (wrap (Tup.units ts)) (Tup.units ts) (b + ts.length) F hc
  | load _ _ _ ih =>
    intro b F hc
    exact ih _ () (b + 1) F hc
  | store _ _ _ ih =>
    intro b F hc
    exact ih b F hc
  | call _ _ _ ih =>
    intro b F hc
    exact ⟨hc.1, ih _ (Tup.units _) (b + _) F hc.2⟩
  | jnz _ _ _ iht ihe =>
    intro b F hc
    exact ⟨iht _ _ hc.1, ihe _ _ hc.2⟩
  | jump _ _ =>
    intro _ _ _
    trivial
  | ret _ =>
    intro _ _ _
    trivial
  | exit _ _ =>
    intro _ _ hc
    exact hc
  | hlt =>
    intro _ _ _
    trivial
  | @group _ _ sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro b F hc
    exact ⟨assumeBitsB_callsOk b F _ _
      (fun i hci => ihb (Tup.units sig) (Tup.units sig) i _ (Tup.units _) _ F hci) hc.1,
      ihk (Tup.units sig) (Tup.units sig) b F hc.2⟩

/-! ## Closed functions -/

/-- `Func.assumeBits` preserves well-formedness. -/
theorem Func.assumeBits_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.assumeBits f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (ABVal V₁) (ABVal V₂) L₁ L₂ (freshABVals as xs₁ 0) (freshABVals as xs₂ 0)
  have hrel : ABRelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshABVals as xs₁ 0) (freshABVals as xs₂ 0)) := by
    simpa using ABRelG.freshABVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact LeanQbe.T.assumeBits_wf hwf hrel as.length []

/-- Known-bits simplification refines contracts: any source contract holds on
`Func.assumeBits f`. -/
theorem Func.assumeBits_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.assumeBits f) xs m Q X := by
  have hwf := hf (ABVal Val) Val Cont Cont (freshABVals as xs 0) xs
  have hgood : ABGoodCtx (ABEnv.updTup (fun _ => none) 0 xs) as.length
      (Tup.zip (freshABVals as xs 0) xs) := by
    simpa using ABGoodCtx.freshABVals (ρ := fun _ => none) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact LeanQbe.T.assumeBits_wp hwf (fun _ hp => nomatch hp) as.length _ [] hgood FactsOk.nil m h

/-- `Func.assumeBits` refines `Func.wp` semantics for any well-formed function. -/
theorem Func.assumeBits_correct {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.wp Γ f xs m Q X) : Func.wp Γ (Func.assumeBits f) xs m Q X :=
  Func.assumeBits_spec hf h

/-- `Func.assumeBits` preserves `Expr.callsOk` for any well-formed function. -/
theorem Func.assumeBits_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.assumeBits f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits :=
  LeanQbe.T.assumeBits_callsOk
    (hf (ABVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
      (freshABVals as (Tup.units as) 0) (Tup.units as)) as.length [] hc

end LeanQbe.T
