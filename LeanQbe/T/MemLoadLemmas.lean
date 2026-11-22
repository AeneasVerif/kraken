module

public import LeanQbe.T.MemLoad
public import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas

/-!
# Correctness of `MemLoad` and `AssumeElim` (`O-M2`)

* `spanDisjoint_sound`: `BitVec 64` offset-interval disjointness cancels common `base` even
  across `base + off` wraparound, connecting to `OpsLemmas.loadVal_storeMem_disjoint`.
* `stepBaseOff_good`: symbolic `(baseKey, off)` tracking preserves `BaseOffGood` across
  `add i64`, `sub i64`, `copy i64`, and all other opcodes.
* `memLoad_wp`, `memLoad_wf`, `Func.memLoad_wf`, `Func.memLoad_spec`: soundness and
  well-formedness of lexical load CSE, store-to-load forwarding, and group kill-set preservation.
* `assumeElim_wp`, `assumeElim_wf`, `Func.assumeElim_wf`, `Func.assumeElim_spec`: soundness and
  well-formedness of `.jnz c t .hlt → t` and `.jnz c .hlt e → e`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Key equality, disjointness, `BaseOffGood`, and `stepBaseOff_good` -/

theorem fkey64Beq_iff_eq : {a b : FKey i64} → fkey64Beq a b = true ↔ a = b
  | .var i, .var j => by dsimp only [fkey64Beq]; simp
  | .imm a, .imm b => by dsimp only [fkey64Beq]; simp
  | .var _, .imm _ | .imm _, .var _ => by dsimp only [fkey64Beq]; simp

theorem spanDisjoint_sound {off₁ : BitVec 64} {bytes₁ : Nat} {off₂ : BitVec 64} {bytes₂ : Nat}
    (h : spanDisjoint off₁ bytes₁ off₂ bytes₂ = true) (base : BitVec 64) :
    ∀ i j, i < bytes₁ → j < bytes₂ →
      (base + off₂) + BitVec.ofNat 64 j ≠ (base + off₁) + BitVec.ofNat 64 i := by
  intro i j hi hj heq
  rw [BitVec.add_assoc, BitVec.add_assoc] at heq
  have heq' : off₂ + BitVec.ofNat 64 j = off₁ + BitVec.ofNat 64 i := by
    have h1 := congrArg (-base + ·) heq
    simpa [BitVec.add_assoc] using h1
  have hnat := congrArg BitVec.toNat heq'
  have ho1 := off₁.isLt
  have ho2 := off₂.isLt
  simp only [spanDisjoint, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    · have hi64 : i < 2 ^ 64 := by omega
      have hj64 : j < 2 ^ 64 := by omega
      have h1' : (off₁ + BitVec.ofNat 64 i).toNat = off₁.toNat + i := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
          Nat.mod_eq_of_lt (by omega)]
      have h2' : (off₂ + BitVec.ofNat 64 j).toNat = off₂.toNat + j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64,
          Nat.mod_eq_of_lt (by omega)]
      omega

theorem Trie.getD_insert_ne {α : Type} (t : Trie α) {i j : Nat} (v d : α) (h : j ≠ i) :
    (t.insert i v).getD j d = t.getD j d := by
  simp only [Trie.getD, Trie.find?_insert_ne t v h]

/-- Symbolic `(baseKey, off)` map agrees with valuation `ρ` below `next` and is empty above. -/
def BaseOffGood (ρ : (t : Ty) → Nat → Val t) (next : Nat) (m : BaseOffMap) : Prop :=
  (∀ i < next,
    (m.getD i (.var i, 0#64)).1.FLt next ∧
    (m.getD i (.var i, 0#64)).1.fev ρ + (m.getD i (.var i, 0#64)).2 = ρ i64 i) ∧
  (∀ i ≥ next, m.find? i = none)

theorem BaseOffGood.empty (ρ : (t : Ty) → Nat → Val t) (next : Nat) :
    BaseOffGood ρ next .empty := by
  refine ⟨fun i hi => ?_, fun _ _ => rfl⟩
  simp only [Trie.getD_empty]
  exact ⟨hi, BitVec.add_zero _⟩

theorem BaseOffGood.upd_fupd {ρ : (t : Ty) → Nat → Val t} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) {u : Ty} (v : Val u) :
    BaseOffGood (fupd ρ next v) (next + 1) m := by
  refine ⟨fun i hi => ?_, fun i hi => hm.2 i (by omega)⟩
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hlt | rfl
  · obtain ⟨hflt, hev⟩ := hm.1 i hlt
    refine ⟨hflt.mono, ?_⟩
    rw [FKey.fev_fupd v hflt, fupd_ne ρ v (Nat.ne_of_lt hlt)]
    exact hev
  · have hnone := hm.2 i (Nat.le_refl i)
    simp only [Trie.getD, hnone, Option.getD_none]
    exact ⟨hi, BitVec.add_zero _⟩

theorem BaseOffGood.upd_fupdTup {ρ : (t : Ty) → Nat → Val t} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) :
    {ts : List Ty} → (xs : Tup Val ts) → BaseOffGood (fupdTup ρ next xs) (next + ts.length) m
  | [], () => hm
  | _ :: ts, (x, xs) => by
    simp only [fupdTup, List.length_cons]
    have h1 := (hm.upd_fupd x).upd_fupdTup xs
    rwa [show next + 1 + ts.length = next + (ts.length + 1) by omega] at h1

theorem BaseOffGood.insert_next {ρ : (t : Ty) → Nat → Val t} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) (v : Val i64) {b : FKey i64} {off : BitVec 64}
    (hb : b.FLt next) (heq : b.fev ρ + off = v) :
    BaseOffGood (fupd ρ next v) (next + 1) (m.insert next (b, off)) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hlt | rfl
    · rw [Trie.getD_insert_ne m (b, off) (.var i, 0#64) (Nat.ne_of_lt hlt)]
      obtain ⟨hflt, hev⟩ := hm.1 i hlt
      refine ⟨hflt.mono, ?_⟩
      rw [FKey.fev_fupd v hflt, fupd_ne ρ v (Nat.ne_of_lt hlt)]
      exact hev
    · simp only [Trie.getD_insert_self]
      refine ⟨hb.mono, ?_⟩
      rw [FKey.fev_fupd v hb, fupd_eq]
      exact heq
  · rw [Trie.find?_insert_ne m (b, off) (by omega)]
    exact hm.2 i (by omega)

theorem resolveKey_good {ρ : (t : Ty) → Nat → Val t} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) {k : FKey i64} (hk : k.FLt next) :
    (resolveKey m k).1.FLt next ∧ (resolveKey m k).1.fev ρ + (resolveKey m k).2 = k.fev ρ := by
  cases k with
  | var i => exact hm.1 i hk
  | imm c => exact ⟨trivial, BitVec.zero_add c⟩

/-- Evaluate a tuple of `FKey`s under valuation `ρ`. -/
def tupFev (ρ : (t : Ty) → Nat → Val t) : {ts : List Ty} → Tup FKey ts → Tup Val ts
  | [], () => ()
  | _ :: _, (a, as) => (a.fev ρ, tupFev ρ as)

/-- Every `FKey` in a tuple has variable levels `< next`. -/
def TupFLt (next : Nat) : {ts : List Ty} → Tup FKey ts → Prop
  | [], () => True
  | _ :: _, (a, as) => a.FLt next ∧ TupFLt next as

theorem stepBaseOff_good (ρ : (t : Ty) → Nat → Val t) (next : Nat) (m : BaseOffMap)
    (hm : BaseOffGood ρ next m) {sig ts : List Ty} (code : OpCode sig ts)
    (kargs : Tup FKey sig) (hklt : TupFLt next kargs)
    (args₂ : Tup (Arg Val) sig) (hvals : tupFev ρ kargs = vals args₂)
    (P : Tup Val ts → Prop) (hw : code.wp (vals args₂) P) :
    code.wp (vals args₂) (fun xs =>
      P xs ∧
      BaseOffGood (fupdTup ρ next xs) (next + ts.length) (stepBaseOff next m code kargs)) := by
  cases code with
  | add t =>
    rcases kargs with ⟨x, y, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hklt with ⟨hx, hy, _⟩
    dsimp only [tupFev, vals] at hvals; simp only [Prod.mk.injEq] at hvals
    rcases hvals with ⟨hxa, hyb, _⟩
    cases t with
    | bits n =>
      by_cases hn : n = 64
      · subst hn
        simp only [OpCode.wp_add, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2,
          vals] at hw ⊢
        cases y with
        | imm d =>
          dsimp only [FKey.fev] at hyb
          obtain ⟨hflt, hev⟩ := resolveKey_good hm hx
          rw [show stepBaseOff next m (.add (.bits 64)) (x, .imm d, ()) =
            m.insert next ((resolveKey m x).1, (resolveKey m x).2 + d) from rfl]
          refine ⟨hw, hm.insert_next _ hflt ?_⟩
          rw [← BitVec.add_assoc, hev, hxa, ← hyb]
        | var v =>
          cases x with
          | imm d =>
            dsimp only [FKey.fev] at hxa
            obtain ⟨hflt, hev⟩ := resolveKey_good hm hy
            rw [show stepBaseOff next m (.add (.bits 64)) (.imm d, .var v, ()) =
              m.insert next ((resolveKey m (.var v)).1, (resolveKey m (.var v)).2 + d) from rfl]
            refine ⟨hw, hm.insert_next _ hflt ?_⟩
            rw [← BitVec.add_assoc, hev, hyb, ← hxa, BitVec.add_comm]
          | var v' =>
            rw [show stepBaseOff next m (.add (.bits 64)) (.var v', .var v, ()) = m from rfl]
            exact ⟨hw, hm.upd_fupdTup _⟩
      · rw [show stepBaseOff next m (.add (.bits n)) (x, y, ()) = m by
          dsimp only [stepBaseOff]; simp only [dite_eq_right (fun h => absurd h hn)]]
        exact OpCode.wp_mono _ _ (fun xs h => ⟨h, hm.upd_fupdTup xs⟩) hw
    | _ => exact OpCode.wp_mono _ _ (fun xs h => ⟨h, hm.upd_fupdTup xs⟩) hw
  | sub t =>
    rcases kargs with ⟨x, y, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hklt with ⟨hx, hy, _⟩
    dsimp only [tupFev, vals] at hvals; simp only [Prod.mk.injEq] at hvals
    rcases hvals with ⟨hxa, hyb, _⟩
    cases t with
    | bits n =>
      by_cases hn : n = 64
      · subst hn
        simp only [OpCode.wp_sub, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2,
          vals] at hw ⊢
        cases y with
        | imm d =>
          dsimp only [FKey.fev] at hyb
          obtain ⟨hflt, hev⟩ := resolveKey_good hm hx
          rw [show stepBaseOff next m (.sub (.bits 64)) (x, .imm d, ()) =
            m.insert next ((resolveKey m x).1, (resolveKey m x).2 - d) from rfl]
          refine ⟨hw, hm.insert_next _ hflt ?_⟩
          rw [BitVec.sub_eq_add_neg, ← BitVec.add_assoc, hev, hxa, ← hyb, ← BitVec.sub_eq_add_neg]
        | var v =>
          rw [show stepBaseOff next m (.sub (.bits 64)) (x, .var v, ()) = m from rfl]
          exact ⟨hw, hm.upd_fupdTup _⟩
      · rw [show stepBaseOff next m (.sub (.bits n)) (x, y, ()) = m by
          dsimp only [stepBaseOff]; simp only [dite_eq_right (fun h => absurd h hn)]]
        exact OpCode.wp_mono _ _ (fun xs h => ⟨h, hm.upd_fupdTup xs⟩) hw
    | _ => exact OpCode.wp_mono _ _ (fun xs h => ⟨h, hm.upd_fupdTup xs⟩) hw
  | copy t =>
    rcases kargs with ⟨x, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
    rcases hklt with ⟨hx, _⟩
    dsimp only [tupFev, vals] at hvals; simp only [Prod.mk.injEq] at hvals
    cases t with
    | bits n =>
      by_cases hn : n = 64
      · subst hn
        obtain ⟨hflt, hev⟩ := resolveKey_good hm hx
        dsimp only [vals] at hw ⊢; simp only [OpCode.wp_copy] at hw ⊢
        rw [show stepBaseOff next m (.copy (.bits 64)) (x, ()) =
          m.insert next (resolveKey m x) from rfl]
        exact ⟨hw, hm.insert_next _ hflt (hev.trans hvals.1)⟩
      · rw [show stepBaseOff next m (.copy (.bits n)) (x, ()) = m by
          dsimp only [stepBaseOff]; simp only [dite_eq_right (fun h => absurd h hn)]]
        exact OpCode.wp_mono _ _ (fun xs h => ⟨h, hm.upd_fupdTup xs⟩) hw
    | _ => exact OpCode.wp_mono _ _ (fun xs h => ⟨h, hm.upd_fupdTup xs⟩) hw
  | _ =>
    all_goals
      exact OpCode.wp_mono _ (vals args₂) (fun xs h => ⟨h, hm.upd_fupdTup xs⟩) hw

/-! ## Context invariants (`KGood`, `MGood`), cache invariants, and group summaries -/

/-- `K`-context agreement with valuation `ρ` below `next`. -/
def KGood (ρ : (t : Ty) → Nat → Val t) (next : Nat) (Gk : Ctx K Val) : Prop :=
  ∀ p ∈ Gk, p.2.1 < next ∧ ρ p.1 p.2.1 = p.2.2

theorem KGood.cons {ρ : (t : Ty) → Nat → Val t} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {t : Ty} (v : Val t) :
    KGood (fupd ρ next v) (next + 1) (⟨t, next, v⟩ :: Gk) := by
  intro p hp
  cases hp with
  | head => exact ⟨Nat.lt_succ_self _, fupd_eq ρ next v⟩
  | tail _ hp =>
    obtain ⟨hlt, heq⟩ := hG p hp
    exact ⟨Nat.lt_succ_of_lt hlt, (fupd_ne ρ v (Nat.ne_of_lt hlt)).trans heq⟩

private theorem KGood.tup_levels_only (ρ : (t : Ty) → Nat → Val t) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    KGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (Tup.levels ts b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | _ :: ts, (x, xs), b => by
    simp only [Tup.levels, Tup.zip, fupdTup, List.length_cons]
    intro p hp
    cases hp with
    | head =>
      dsimp only
      refine ⟨Nat.lt_add_of_pos_right (Nat.succ_pos _), ?_⟩
      rw [fupdTup_lt (fupd ρ b x) xs (Nat.lt_succ_self b), fupd_eq]
    | tail _ hp =>
      have ih := KGood.tup_levels_only (fupd ρ b x) xs (b + 1) p hp
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem KGood.upd_all {ρ : (t : Ty) → Nat → Val t} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {ts : List Ty} (xs : Tup Val ts) :
    KGood (fupdTup ρ next xs) (next + ts.length) Gk := by
  intro p hp
  obtain ⟨hlt, heq⟩ := hG p hp
  exact ⟨Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _), (fupdTup_lt ρ xs hlt).trans heq⟩

theorem KGood.freshTup {ρ : (t : Ty) → Nat → Val t} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {ts : List Ty} (xs : Tup Val ts) :
    KGood (fupdTup ρ next xs) (next + ts.length) (Tup.zip (Tup.levels ts next) xs ++ Gk) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact KGood.tup_levels_only ρ xs next p hp
  · exact hG.upd_all xs p hp

theorem ArgRel.k_lt {ρ : (t : Ty) → Nat → Val t} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {t : Ty} {ak : Arg K t} {a₂ : Arg Val t}
    (h : ArgRel Gk t ak a₂) : FKey.FLt next ak := by
  cases h with
  | var hm => exact (hG _ hm).1
  | imm _ => trivial

theorem ArgRel.k_ev {ρ : (t : Ty) → Nat → Val t} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {t : Ty} {ak : Arg K t} {a₂ : Arg Val t}
    (h : ArgRel Gk t ak a₂) : FKey.fev ρ ak = a₂.val := by
  cases h with
  | var hm => exact (hG _ hm).2
  | imm _ => rfl

theorem TRel.k_lt {ρ : (t : Ty) → Nat → Val t} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) :
    {ts : List Ty} → {aks : Tup FKey ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₂ → TupFLt next aks
  | [], (), (), .nil => trivial
  | _ :: _, (_, _), (_, _), .cons h hs => ⟨ArgRel.k_lt hG h, TRel.k_lt hG hs⟩

theorem TRel.k_vals {ρ : (t : Ty) → Nat → Val t} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) :
    {ts : List Ty} → {aks : Tup FKey ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₂ → tupFev ρ aks = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (ArgRel.k_ev hG h) (TRel.k_vals hG hs)

/-- `MVal`-context agreement with valuation `ρ` below `next`. -/
def MGood (ρ : (t : Ty) → Nat → Val t) (next : Nat) (G : Ctx (MVal Val) Val) : Prop :=
  ∀ p ∈ G, p.2.1.out.val = p.2.2 ∧ p.2.1.key.FLt next ∧ p.2.1.key.fev ρ = p.2.2

theorem MGood.upd_all {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {ts : List Ty} (xs : Tup Val ts) :
    MGood (fupdTup ρ next xs) (next + ts.length) G := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hG p hp
  exact ⟨h1, h2.add, (FKey.fev_fupdTup xs h2).trans h3⟩

theorem MGood.cons_fupd {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} {mv : MVal Val t} {v : Val t}
    (h1 : mv.out.val = v) (h2 : mv.key.FLt (next + 1)) (h3 : mv.key.fev (fupd ρ next v) = v) :
    MGood (fupd ρ next v) (next + 1) (⟨t, mv, v⟩ :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨h1, h2, h3⟩
  | tail _ hp =>
    obtain ⟨ha, hb, hc⟩ := hG p hp
    exact ⟨ha, hb.mono, (FKey.fev_fupd v hb).trans hc⟩

theorem MGood.cons_fresh {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} (v : Val t) :
    MGood (fupd ρ next v) (next + 1) (⟨t, MVal.fresh v next, v⟩ :: G) :=
  hG.cons_fupd rfl (Nat.lt_succ_self next) (fupd_eq ρ next v)

private theorem MGood.freshMVals_only (ρ : (t : Ty) → Nat → Val t) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    MGood (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshMVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | _ :: ts, (x, xs), b => by
    simp only [freshMVals, tupFreshWith, Tup.zip, fupdTup, List.length_cons]
    intro p hp
    cases hp with
    | head =>
      dsimp only [MVal.fresh, FKey.FLt, FKey.fev]
      refine ⟨rfl, Nat.lt_add_of_pos_right (Nat.succ_pos _), ?_⟩
      rw [fupdTup_lt (fupd ρ b x) xs (Nat.lt_succ_self b), fupd_eq]
    | tail _ hp =>
      have ih := MGood.freshMVals_only (fupd ρ b x) xs (b + 1) p hp
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem MGood.freshMVals {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {ts : List Ty} (xs : Tup Val ts) :
    MGood (fupdTup ρ next xs) (next + ts.length)
      (Tup.zip (freshMVals ts xs next) xs ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact MGood.freshMVals_only ρ xs next p hp
  · exact hG.upd_all xs p hp

theorem ArgRel.mout_val {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} {a₁ : Arg (MVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.mout.val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem ArgRel.mkey_lt {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} {a₁ : Arg (MVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.mkey.FLt next
  | .var h => (hG _ h).2.1
  | .imm _ => trivial

theorem ArgRel.mkey_ev {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} {a₁ : Arg (MVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.mkey.fev ρ = a₂.val
  | .var h => (hG _ h).2.2
  | .imm _ => rfl

theorem TRel.mout_vals {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {ts : List Ty} {as₁ : Tup (Arg (MVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupMOut as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => Arg.mout) (fun ha => ha.mout_val hG) h

theorem TRel.mkey_lt {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) :
    {ts : List Ty} → {as₁ : Tup (Arg (MVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → TupFLt next (tupMKey as₁)
  | [], (), (), .nil => trivial
  | _ :: _, (_, _), (_, _), .cons h hs => ⟨h.mkey_lt hG, TRel.mkey_lt hG hs⟩

theorem TRel.mkey_vals {ρ : (t : Ty) → Nat → Val t} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) :
    {ts : List Ty} → {as₁ : Tup (Arg (MVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → tupFev ρ (tupMKey as₁) = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (h.mkey_ev hG) (TRel.mkey_vals hG hs)

/-- Semantic agreement of a dominating cache entry with valuation `ρ` and memory `m`. -/
def MemEntryGood (ρ : (t : Ty) → Nat → Val t) (next : Nat) (e : CacheEntry Val)
    (m : Mem 64) : Prop :=
  e.baseKey.FLt next ∧ e.valKey.FLt next ∧ e.valKey.fev ρ = e.val.val ∧
    loadVal m e.ty (e.baseKey.fev ρ + e.off) = some e.val.val

/-- Dominating cache invariant: every cached entry agrees with `ρ` and `m`. -/
def MemCacheGood (ρ : (t : Ty) → Nat → Val t) (next : Nat) (cache : List (CacheEntry Val))
    (m : Mem 64) : Prop :=
  ∀ e ∈ cache, MemEntryGood ρ next e m

/-- Static invariant entry captured at `.group` entry (`addr` is fixed across inner binders). -/
structure InvEntry : Type where
  baseKey : FKey i64
  off : BitVec 64
  addr : BitVec 64
  ty : Ty
  val : Val ty

/-- Memory-only agreement for group invariant entries (independent of `ρ` and `next`). -/
def InvMemGood (inv : List InvEntry) (m : Mem 64) : Prop :=
  ∀ e ∈ inv, loadVal m e.ty e.addr = some e.val

/-- Static base-key agreement for group invariant entries below `next`. -/
def InvKeysGood (ρ : (t : Ty) → Nat → Val t) (next : Nat) (inv : List InvEntry) : Prop :=
  ∀ e ∈ inv, e.baseKey.FLt next ∧ e.baseKey.fev ρ + e.off = e.addr

/-- Combined semantic invariant `MemLoadGood` pairing dominating cache and enclosing group frame. -/
def MemLoadGood (ρ : (t : Ty) → Nat → Val t) (next : Nat)
    (cache : List (CacheEntry Val)) (inv : List InvEntry) (m : Mem 64) : Prop :=
  MemCacheGood ρ next cache m ∧ InvMemGood inv m ∧ InvKeysGood ρ next inv

private theorem MemLoadGood.empty (ρ : (t : Ty) → Nat → Val t) (next : Nat) (m : Mem 64) :
    MemLoadGood ρ next [] [] m :=
  ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-- Summary preservation condition: `s` has no `.call` (`≠ .unknown`) and every write span in `s`
is provably disjoint from every entry in `inv`. -/
def SummaryPreserves (s : MemSummary) (inv : List InvEntry) : Prop :=
  ∀ e ∈ inv, match s with
    | .unknown => False
    | .exact ws => ∀ w ∈ ws, fkey64Beq e.baseKey w.baseKey = true ∧
        spanDisjoint w.off w.bytes e.off e.ty.bytes = true

/-- Label invariant: `P m` enables transforming `e₂`'s continuation `p.2.2` into `p.2.1`. -/
def MemDGood (P : Mem 64 → Prop) (D : Ctx Cont Cont) : Prop :=
  ∀ p ∈ D, ∀ xs m, P m → p.2.2 xs m → p.2.1 xs m

theorem MemCacheGood.upd_one {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {u : Ty} (v : Val u) :
    MemCacheGood (fupd ρ next v) (next + 1) cache m := by
  intro e he
  obtain ⟨hb, hv, hev, hld⟩ := hc e he
  refine ⟨hb.mono, hv.mono, ?_, ?_⟩
  · rw [FKey.fev_fupd v hv]; exact hev
  · rw [FKey.fev_fupd v hb]; exact hld

theorem MemCacheGood.upd_fupdTup {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {ts : List Ty} (xs : Tup Val ts) :
    MemCacheGood (fupdTup ρ next xs) (next + ts.length) cache m := by
  intro e he
  obtain ⟨hb, hv, hev, hld⟩ := hc e he
  refine ⟨hb.add, hv.add, ?_, ?_⟩
  · rw [FKey.fev_fupdTup xs hv]; exact hev
  · rw [FKey.fev_fupdTup xs hb]; exact hld

theorem InvKeysGood.upd_one {ρ : (t : Ty) → Nat → Val t} {next : Nat} {inv : List InvEntry}
    (hi : InvKeysGood ρ next inv) {u : Ty} (v : Val u) :
    InvKeysGood (fupd ρ next v) (next + 1) inv := by
  intro e he
  obtain ⟨hb, heq⟩ := hi e he
  exact ⟨hb.mono, (FKey.fev_fupd v hb).symm ▸ heq⟩

theorem InvKeysGood.upd_fupdTup {ρ : (t : Ty) → Nat → Val t} {next : Nat} {inv : List InvEntry}
    (hi : InvKeysGood ρ next inv) {ts : List Ty} (xs : Tup Val ts) :
    InvKeysGood (fupdTup ρ next xs) (next + ts.length) inv := by
  intro e he
  obtain ⟨hb, heq⟩ := hi e he
  exact ⟨hb.add, (FKey.fev_fupdTup xs hb).symm ▸ heq⟩

theorem MemCacheGood.store_filter {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) (b : FKey i64) (off : BitVec 64)
    (t : Ty) (ptr : BitVec 64) (v : Val t) (hptr : b.fev ρ + off = ptr) :
    MemCacheGood ρ next (filterCacheWrite b off t.bytes cache) (storeMem m t ptr v) := by
  intro e he
  simp only [filterCacheWrite, List.mem_filter, entryDisjointWrite, Bool.and_eq_true,
    fkey64Beq_iff_eq] at he
  obtain ⟨hem, hb, hsp⟩ := he
  obtain ⟨hbflt, hvflt, hev, hld⟩ := hc e hem
  refine ⟨hbflt, hvflt, hev, ?_⟩
  have hdisj := spanDisjoint_sound hsp (b.fev ρ)
  rw [hb] at hld ⊢
  rw [← hptr, loadVal_storeMem_disjoint m t e.ty (b.fev ρ + off) (b.fev ρ + e.off) v hdisj]
  exact hld

theorem MemCacheGood.store_push {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {b : FKey i64} {off : BitVec 64} {t : Ty}
    {vout : Arg Val t} {vkey : FKey t} {ptr : BitVec 64} {v : Val t}
    (hbflt : b.FLt next) (hvflt : vkey.FLt next) (hev : vkey.fev ρ = vout.val)
    (hv : vout.val = v) (hptr : b.fev ρ + off = ptr) (hbytes : t.bytes ≤ 2 ^ 64) :
    MemCacheGood ρ next
      (⟨b, off, t, vout, vkey⟩ :: filterCacheWrite b off t.bytes cache)
      (storeMem m t ptr v) := by
  intro e he
  cases he with
  | head =>
    refine ⟨hbflt, hvflt, hev, ?_⟩
    rw [hptr, hv]
    exact loadVal_storeMem m t ptr v hbytes
  | tail _ he => exact hc.store_filter b off t ptr v hptr e he

theorem MemCacheGood.cons_load {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {b : FKey i64} {off : BitVec 64} {t : Ty}
    {v : Val t} (hbflt : b.FLt next) (hld : loadVal m t (b.fev ρ + off) = some v) :
    MemCacheGood (fupd ρ next v) (next + 1)
      (⟨b, off, t, .var v, .var next⟩ :: cache) m := by
  intro e he
  cases he with
  | head =>
    refine ⟨hbflt.mono, Nat.lt_succ_self _, fupd_eq ρ next v, ?_⟩
    rw [FKey.fev_fupd v hbflt]
    exact hld
  | tail _ he => exact hc.upd_one v e he

theorem lookupCache_mem {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {b : FKey i64} {off : BitVec 64} {t : Ty}
    {mv : MVal Val t} (hl : lookupCache b off t cache = some mv) :
    mv.key.FLt next ∧ mv.key.fev ρ = mv.out.val ∧
      loadVal m t (b.fev ρ + off) = some mv.out.val := by
  induction cache with
  | nil => cases hl
  | cons e rest ih =>
    dsimp only [lookupCache] at hl
    cases hbo : (fkey64Beq e.baseKey b && e.off == off)
    · rw [hbo] at hl
      exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) hl
    · rw [hbo] at hl
      cases hty : tyDecEq e.ty t with
      | isFalse _ =>
        rw [hty] at hl
        exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) hl
      | isTrue heq =>
        rw [hty] at hl
        injection hl with hmv
        subst hmv
        simp only [Bool.and_eq_true, fkey64Beq_iff_eq, beq_iff_eq] at hbo
        obtain ⟨hb, ho⟩ := hbo
        obtain ⟨_, hvflt, hev, hld⟩ := hc e List.mem_cons_self
        subst heq hb ho
        exact ⟨hvflt, hev, hld⟩

theorem MemCacheGood.filterSummary {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) (s : MemSummary) :
    MemCacheGood ρ next (filterCacheSummary s cache) m :=
  fun e he => hc e (List.mem_filter.1 he).1

/-- Convert surviving `CacheEntry Val`s into `InvEntry`s fixed at current `ρ`. -/
def cacheToInv (ρ : (t : Ty) → Nat → Val t) (c : List (CacheEntry Val)) : List InvEntry :=
  c.map fun e => ⟨e.baseKey, e.off, e.baseKey.fev ρ + e.off, e.ty, e.val.val⟩

theorem InvMemGood.of_cache {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {c : List (CacheEntry Val)} {m : Mem 64} (hc : MemCacheGood ρ next c m) :
    InvMemGood (cacheToInv ρ c) m := by
  intro e he
  dsimp only [cacheToInv] at he; simp only [List.mem_map] at he
  rcases he with ⟨ce, hce, rfl⟩
  exact (hc ce hce).2.2.2

theorem InvKeysGood.of_cache {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {c : List (CacheEntry Val)} {m : Mem 64} (hc : MemCacheGood ρ next c m) :
    InvKeysGood ρ next (cacheToInv ρ c) := by
  intro e he
  dsimp only [cacheToInv] at he; simp only [List.mem_map] at he
  rcases he with ⟨ce, hce, rfl⟩
  exact ⟨(hc ce hce).1, rfl⟩

theorem MemCacheGood.of_inv {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {c : List (CacheEntry Val)} {m₀ m' : Mem 64}
    (hc : MemCacheGood ρ next c m₀) (hi : InvMemGood (cacheToInv ρ c) m') :
    MemCacheGood ρ next c m' := by
  intro e he
  obtain ⟨hb, hv, hev, _⟩ := hc e he
  refine ⟨hb, hv, hev, ?_⟩
  exact hi ⟨e.baseKey, e.off, e.baseKey.fev ρ + e.off, e.ty, e.val.val⟩
    (List.mem_map.2 ⟨e, he, rfl⟩)

theorem InvMemGood.append {inv₁ inv₂ : List InvEntry} {m : Mem 64} :
    InvMemGood inv₁ m → InvMemGood inv₂ m → InvMemGood (inv₁ ++ inv₂) m :=
  fun h1 h2 e he => (List.mem_append.1 he).elim (h1 e) (h2 e)

theorem InvKeysGood.append {ρ : (t : Ty) → Nat → Val t} {next : Nat} {inv₁ inv₂ : List InvEntry} :
    InvKeysGood ρ next inv₁ → InvKeysGood ρ next inv₂ → InvKeysGood ρ next (inv₁ ++ inv₂) :=
  fun h1 h2 e he => (List.mem_append.1 he).elim (h1 e) (h2 e)

theorem SummaryPreserves.join {s₁ s₂ : MemSummary} {inv : List InvEntry} :
    SummaryPreserves (s₁.join s₂) inv ↔ SummaryPreserves s₁ inv ∧ SummaryPreserves s₂ inv := by
  cases s₁ with
  | unknown =>
    cases s₂ <;> dsimp only [SummaryPreserves, MemSummary.join]
    · exact ⟨fun h => ⟨h, fun e he _ _ => False.elim (h e he)⟩, fun ⟨h, _⟩ => h⟩
    · exact ⟨fun h => ⟨h, h⟩, fun ⟨h, _⟩ => h⟩
  | exact ws₁ =>
    cases s₂ with
    | unknown =>
      dsimp only [SummaryPreserves, MemSummary.join]
      exact ⟨fun h => ⟨fun e he _ _ => False.elim (h e he), h⟩, fun ⟨_, h⟩ => h⟩
    | exact ws₂ =>
      dsimp only [SummaryPreserves, MemSummary.join]
      constructor
      · intro h
        exact ⟨fun e he w hw => h e he w (List.mem_append.2 (Or.inl hw)),
               fun e he w hw => h e he w (List.mem_append.2 (Or.inr hw))⟩
      · rintro ⟨h1, h2⟩ e he w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact h1 e he w hw
        · exact h2 e he w hw

theorem SummaryPreserves.addWrite {w : WriteSpan} {s : MemSummary} {inv : List InvEntry} :
    SummaryPreserves (s.addWrite w) inv ↔
      (∀ e ∈ inv, fkey64Beq e.baseKey w.baseKey = true ∧
        spanDisjoint w.off w.bytes e.off e.ty.bytes = true) ∧
      SummaryPreserves s inv := by
  cases s with
  | unknown =>
    simp only [SummaryPreserves, MemSummary.addWrite]
    exact ⟨fun h => ⟨fun e he => False.elim (h e he), h⟩, fun ⟨_, h⟩ => h⟩
  | exact ws =>
    simp only [SummaryPreserves, MemSummary.addWrite]
    constructor
    · intro h
      exact ⟨fun e he => h e he w List.mem_cons_self,
             fun e he w' hw' => h e he w' (List.mem_cons_of_mem _ hw')⟩
    · rintro ⟨hw, hws⟩ e he w' hw'
      cases hw' with
      | head => exact hw e he
      | tail _ hw' => exact hws e he w' hw'

theorem SummaryPreserves.filterSummary (ρ : (t : Ty) → Nat → Val t)
    (s : MemSummary) (cache : List (CacheEntry Val)) :
    SummaryPreserves s (cacheToInv ρ (filterCacheSummary s cache)) := by
  intro e he
  dsimp only [cacheToInv, filterCacheSummary] at he; simp only [List.mem_map, List.mem_filter] at he
  rcases he with ⟨ce, ⟨_, hdisj⟩, rfl⟩
  cases s with
  | unknown => simp [summaryDisjointEntry] at hdisj
  | exact ws =>
    simp only [summaryDisjointEntry, List.all_eq_true, entryDisjointWrite,
      Bool.and_eq_true] at hdisj
    exact fun w hw => hdisj w hw

theorem SummaryPreserves.append {s : MemSummary} {inv₁ inv₂ : List InvEntry} :
    SummaryPreserves s (inv₁ ++ inv₂) ↔ SummaryPreserves s inv₁ ∧ SummaryPreserves s inv₂ :=
  ⟨fun h => ⟨fun e he => h e (List.mem_append.2 (Or.inl he)),
             fun e he => h e (List.mem_append.2 (Or.inr he))⟩,
   fun ⟨h1, h2⟩ e he => (List.mem_append.1 he).elim (h1 e) (h2 e)⟩

theorem InvMemGood.store_disjoint {ρ : (t : Ty) → Nat → Val t} {next : Nat}
    {inv : List InvEntry} {m : Mem 64}
    (hk : InvKeysGood ρ next inv) (hm : InvMemGood inv m)
    {b : FKey i64} {off : BitVec 64} {t : Ty} {ptr : BitVec 64} (v : Val t)
    (hptr : b.fev ρ + off = ptr)
    (hdisj : ∀ e ∈ inv, fkey64Beq e.baseKey b = true ∧
      spanDisjoint off t.bytes e.off e.ty.bytes = true) :
    InvMemGood inv (storeMem m t ptr v) := by
  intro e he
  obtain ⟨_, heq⟩ := hk e he
  obtain ⟨hb, hsp⟩ := hdisj e he
  have hbeq : e.baseKey = b := fkey64Beq_iff_eq.1 hb
  have hsd := spanDisjoint_sound hsp (b.fev ρ)
  rw [← hptr, ← heq, hbeq,
    loadVal_storeMem_disjoint m t e.ty (b.fev ρ + off) (b.fev ρ + e.off) v hsd]
  rw [← hbeq, heq]
  exact hm e he

/-- Wrap each continuation in `Js` with precondition `P m`. -/
def strengthenJs (P : Mem 64 → Prop) : {sig : List (List Ty)} → Tup Cont sig → Tup Cont sig
  | [], () => ()
  | _ :: _, (J, Js) => (fun xs m => P m → J xs m, strengthenJs P Js)

theorem strengthenJs_get (P : Mem 64 → Prop) :
    {sig : List (List Ty)} → (Js : Tup Cont sig) → {ts : List Ty} → (i : Member ts sig) →
    (strengthenJs P Js).get i = fun xs m => P m → Js.get i xs m
  | _ :: _, (_, _), _, .here => rfl
  | _ :: _, (_, Js), _, .there i => strengthenJs_get P Js i

theorem MemDGood.strengthenJs (P : Mem 64 → Prop) :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    ∀ p ∈ Tup.zip Js (strengthenJs P Js), ∀ xs m, P m → p.2.2 xs m → p.2.1 xs m
  | [], (), _, hp => nomatch hp
  | _ :: _, (_, Js), p, hp => by
    cases hp with
    | head => exact fun _ _ hP hJ => hJ hP
    | tail _ hp => exact MemDGood.strengthenJs P Js p hp

/-! ## Block access lemmas and `memLoad_wp` -/

theorem analyzeMemB_get_summary {rs : List Ty} (next : Nat) (baseOff : BaseOffMap)
    {inv : List InvEntry} :
    {sig : List (List Ty)} → (bs : Blocks K KL0 rs sig) → {ts : List Ty} → (i : Member ts sig) →
    SummaryPreserves (analyzeMemB next baseOff bs).1 inv →
    SummaryPreserves (analyzeMem (next + ts.length) baseOff (bs.get i (Tup.levels ts next))).1 inv
  | _ :: _, .cons _ _, _, .here, h => (SummaryPreserves.join.1 h).1
  | _ :: _, .cons _ tl, _, .there i, h =>
    analyzeMemB_get_summary next baseOff tl i (SummaryPreserves.join.1 h).2

theorem memLoadSweepB_analyzeMemB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (baseOff baseOffK : BaseOffMap) (cache : List (CacheEntry V)) :
    {sig : List (List Ty)} → (bk : Blocks K KL0 rs sig) → (bs : Blocks (MVal V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (memLoadSweepB next baseOff cache (analyzeMemB next baseOffK bk).2 bs).get i xs =
      memLoadSweep (next + ts.length) baseOff cache
        (analyzeMem (next + ts.length) baseOffK (bk.get i (Tup.levels ts next))).2
        (bs.get i (freshMVals ts xs next))
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bkt, .cons _ bst, _, .there i', xs =>
    memLoadSweepB_analyzeMemB_get next baseOff baseOffK cache bkt bst i' xs

private theorem memLoadSweep_load {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (baseOff : BaseOffMap) (cache : List (CacheEntry V)) (kt : MemSumTree)
    (t : Ty) (a : Arg (MVal V) i64) (k : MVal V t → Expr (MVal V) L rs) :
    memLoadSweep next baseOff cache (.node1 kt) (.load t a k) =
      match lookupCache (resolveKey baseOff a.mkey).1 (resolveKey baseOff a.mkey).2 t cache with
      | some cached => memLoadSweep (next + 1) baseOff cache kt (k cached)
      | none =>
        .load t a.mout fun v =>
          let cache' := ⟨(resolveKey baseOff a.mkey).1, (resolveKey baseOff a.mkey).2,
            t, .var v, .var next⟩ :: cache
          memLoadSweep (next + 1) baseOff cache' kt (k (MVal.fresh v next)) := by
  delta memLoadSweep; dsimp only [Expr.brecOn, Expr.rec, memLoadSweep._f]
  cases resolveKey baseOff a.mkey
  cases lookupCache _ _ t cache <;> rfl

/-- Weakest-precondition preservation for `memLoadSweep`, proved via `Wf.induct`. -/
theorem memLoad_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (MVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (MVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {Gk : Ctx K Val} {Dk : Ctx KL0 Cont}
      (next : Nat) (ρ : (t : Ty) → Nat → Val t)
      (baseOff baseOffK : BaseOffMap)
      (cache : List (CacheEntry Val)) (inv : List InvEntry)
      (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₂ → KGood ρ next Gk → MGood ρ next G →
      BaseOffGood ρ next baseOff → BaseOffGood ρ next baseOffK →
      MemDGood (InvMemGood inv) D → SummaryPreserves (analyzeMem next baseOffK ek).1 inv →
      ∀ m, MemLoadGood ρ next cache inv m → wp Γ Q X e₂ m →
        wp Γ Q X (memLoadSweep next baseOff cache (analyzeMem next baseOffK ek).2 e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro Gk Dk next ρ baseOff baseOffK cache inv ek hwk hGk hG hbo hboK hD hsp m hml hw
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        dsimp only [analyzeMem, memLoadSweep, wp, Op.wp] at hsp hw ⊢
        have hw1 := stepBaseOff_good ρ next baseOff hbo code (tupMKey args₁)
          (hargs.mkey_lt hG) args₂ (hargs.mkey_vals hG) _ hw
        have hw2 := stepBaseOff_good ρ next baseOffK hboK code argsk
          (hargsk.k_lt hGk) args₂ (hargsk.k_vals hGk) _ hw1
        rw [hargs.mout_vals hG]
        refine OpCode.wp_mono code _ (fun xs ⟨⟨hk2, hbo'⟩, hboK'⟩ => ?_) hw2
        refine ih (freshMVals ts xs next) xs (next + ts.length) (fupdTup ρ next xs)
          _ _ cache inv (kk (Tup.levels ts next)) (hkk (Tup.levels ts next) xs)
          (hGk.freshTup xs) (hG.freshMVals xs) hbo' hboK' hD hsp m ?_ hk2
        exact ⟨hml.1.upd_fupdTup xs, hml.2.1, hml.2.2.upd_fupdTup xs⟩
  | @load G D t a₁ a₂ k₁ k₂ ha _ ih =>
    intro Gk Dk next ρ baseOff baseOffK cache inv ek hwk hGk hG hbo hboK hD hsp m hml hw
    rcases hwk.rhs_load with ⟨ak, kk, rfl, _, hkk⟩
    dsimp only [analyzeMem, wp] at hsp hw ⊢
    rw [memLoadSweep_load]
    rcases hw with ⟨v, hv, hk⟩
    obtain ⟨hbflt, hbev⟩ := resolveKey_good hbo (ha.mkey_lt hG)
    have haddr : (resolveKey baseOff a₁.mkey).1.fev ρ + (resolveKey baseOff a₁.mkey).2 = a₂.val :=
      hbev.trans (ha.mkey_ev hG)
    cases hlook : lookupCache (resolveKey baseOff a₁.mkey).1
        (resolveKey baseOff a₁.mkey).2 t cache with
    | some cached =>
      dsimp only
      obtain ⟨hkeyflt, hkeyev, hld⟩ := lookupCache_mem hml.1 hlook
      rw [haddr, hv, Option.some.injEq] at hld
      have hv_eq : cached.out.val = v := hld.symm
      refine ih cached v (next + 1) (fupd ρ next v) baseOff baseOffK cache inv (kk next)
        (hkk next v) (hGk.cons v)
        (hG.cons_fupd hv_eq hkeyflt.mono (by rw [FKey.fev_fupd v hkeyflt, hkeyev, hv_eq]))
        (hbo.upd_fupd v) (hboK.upd_fupd v) hD hsp m ?_ hk
      exact ⟨hml.1.upd_one v, hml.2.1, hml.2.2.upd_one v⟩
    | none =>
      dsimp only [wp]
      rw [ha.mout_val hG]
      refine ⟨v, hv, ?_⟩
      refine ih (MVal.fresh v next) v (next + 1) (fupd ρ next v) baseOff baseOffK _ inv (kk next)
        (hkk next v) (hGk.cons v) (hG.cons_fresh v)
        (hbo.upd_fupd v) (hboK.upd_fupd v) hD hsp m ?_ hk
      exact ⟨hml.1.cons_load hbflt (by rw [haddr]; exact hv), hml.2.1, hml.2.2.upd_one v⟩
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv ha _ ih =>
    intro Gk Dk next ρ baseOff baseOffK cache inv ek hwk hGk hG hbo hboK hD hsp m hml hw
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, _, hak, hkk⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hsp hw ⊢
    obtain ⟨hdisj, hsp'⟩ := SummaryPreserves.addWrite.1 hsp
    obtain ⟨hbflt, hbev⟩ := resolveKey_good hbo (ha.mkey_lt hG)
    have haddr : (resolveKey baseOff a₁.mkey).1.fev ρ + (resolveKey baseOff a₁.mkey).2 = a₂.val :=
      hbev.trans (ha.mkey_ev hG)
    have haddrK : (resolveKey baseOffK ak).1.fev ρ + (resolveKey baseOffK ak).2 = a₂.val :=
      (resolveKey_good hboK (hak.k_lt hGk)).2.trans (hak.k_ev hGk)
    rw [ha.mout_val hG, hv.mout_val hG]
    refine ⟨hw.1, ?_⟩
    have hinv' : InvMemGood inv (storeMem m t a₂.val v₂.val) :=
      hml.2.1.store_disjoint hml.2.2 v₂.val haddrK hdisj
    split
    · next hbytes =>
      refine ih (Gk := Gk) (Dk := Dk) next ρ baseOff baseOffK _ inv kk hkk hGk hG hbo hboK hD
        hsp' (storeMem m t a₂.val v₂.val) ?_ hw.2
      exact ⟨hml.1.store_push hbflt (hv.mkey_lt hG) ((hv.mkey_ev hG).trans (hv.mout_val hG).symm)
        (hv.mout_val hG) haddr hbytes, hinv', hml.2.2⟩
    · refine ih (Gk := Gk) (Dk := Dk) next ρ baseOff baseOffK _ inv kk hkk hGk hG hbo hboK hD
        hsp' (storeMem m t a₂.val v₂.val) ?_ hw.2
      exact ⟨hml.1.store_filter _ _ t a₂.val v₂.val haddr, hinv', hml.2.2⟩
  | @call G D f as bs args₁ args₂ k₁ k₂ hargs _ ih =>
    intro Gk Dk next ρ baseOff baseOffK _ inv ek hwk hGk hG hbo hboK hD hsp m hml hw
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, _, hkk⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hsp hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    have hinv_nil : inv = [] := by
      cases inv with
      | nil => rfl
      | cons e _ => exact False.elim (hsp e List.mem_cons_self)
    subst hinv_nil
    rw [hargs.mout_vals hG]
    refine ⟨P, E, hΓ, fun r m' hp => ?_, hE⟩
    refine ih (freshMVals _ r next) r (next + _) (fupdTup ρ next r) baseOff baseOffK [] []
      (kk (Tup.levels _ next)) (hkk (Tup.levels _ next) r)
      (hGk.freshTup r) (hG.freshMVals r) (hbo.upd_fupdTup r) (hboK.upd_fupdTup r)
      (fun p hp => hD p hp) (fun _ h => nomatch h) m' (MemLoadGood.empty _ _ m') (hP r m' hp)
  | @jnz G D c₁ c₂ t₁ t₂ e₁' e₂' hc _ _ iht ihe =>
    intro Gk Dk next ρ baseOff baseOffK cache inv ek hwk hGk hG hbo hboK hD hsp m hml hw
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, _, htk, hek⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hsp hw ⊢
    obtain ⟨hspt, hspe⟩ := SummaryPreserves.join.1 hsp
    rw [hc.mout_val hG]
    exact ⟨fun h => iht next ρ baseOff baseOffK cache inv tk htk hGk hG hbo hboK hD hspt m hml
             (hw.1 h),
           fun h => ihe next ρ baseOff baseOffK cache inv ek' hek hGk hG hbo hboK hD hspe m hml
             (hw.2 h)⟩
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro Gk Dk next ρ baseOff baseOffK cache inv ek hwk hGk hG hbo hboK hD hsp m hml hw
    rcases hwk.rhs_jump with ⟨jk, argsk, rfl, _, _⟩
    dsimp only [memLoadSweep, wp] at hw ⊢
    rw [hargs.mout_vals hG]
    exact hD _ hj (vals args₂) m hml.2.1 hw
  | ret hvs =>
    intro _ _ _ ρ _ _ _ _ ek hwk _ hG _ _ _ _ _ _ hw
    rcases hwk.rhs_ret with ⟨_, rfl, _⟩
    dsimp only [memLoadSweep, wp] at hw ⊢
    rw [hvs.mout_vals hG]; exact hw
  | exit f hargs =>
    intro _ _ _ ρ _ _ _ _ ek hwk _ hG _ _ _ _ _ _ hw
    rcases hwk.rhs_exit with ⟨_, rfl, _⟩
    dsimp only [memLoadSweep, wp] at hw ⊢
    rw [hargs.mout_vals hG]; exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ _ ek hwk _ _ _ _ _ _ _ _ hw
    rw [hwk.rhs_hlt]; exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro Gk Dk next ρ baseOff baseOffK cache inv ek hwk hGk hG hbo hboK hD hsp m hml hw
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hsp hw ⊢
    intro Js hclosed
    let ls := Tup.units sig
    let sum := (analyzeMemB next baseOffK (bk ls)).1.join (analyzeMem next baseOffK (kk ls)).1
    let cacheB := filterCacheSummary sum cache
    let inv' := cacheToInv ρ cacheB ++ inv
    let Js' := strengthenJs (InvMemGood inv') Js
    have hD' : MemDGood (InvMemGood inv') (Tup.zip Js Js' ++ D) := by
      intro p hp xs m' hinv'
      rcases List.mem_append.1 hp with hp | hp
      · exact MemDGood.strengthenJs (InvMemGood inv') Js p hp xs m' hinv'
      · exact hD p hp xs m' (fun e he => hinv' e (List.mem_append.2 (Or.inr he)))
    have hsp' : SummaryPreserves sum inv' := by
      rw [SummaryPreserves.append]
      exact ⟨SummaryPreserves.filterSummary ρ sum cache, hsp⟩
    obtain ⟨hspB', hspK'⟩ := SummaryPreserves.join.1 hsp'
    have hinvKeys' : InvKeysGood ρ next inv' :=
      (InvKeysGood.of_cache (hml.1.filterSummary sum)).append hml.2.2
    have hcl2 : Closed Γ Q X (b₂ Js') Js' := by
      rw [closed_iff] at hclosed ⊢
      intro ts i xs m' hb₂
      rw [strengthenJs_get]
      intro hinv_m'
      apply hclosed i xs m'
      rw [memLoadSweepB_analyzeMemB_get]
      have hcb_m' : MemCacheGood (fupdTup ρ next xs) (next + ts.length) cacheB m' :=
        ((hml.1.filterSummary sum).of_inv fun e he =>
          hinv_m' e (List.mem_append.2 (Or.inl he))).upd_fupdTup xs
      exact ihb Js Js' i (freshMVals ts xs next) xs (next + ts.length) (fupdTup ρ next xs)
        baseOff baseOffK cacheB inv' ((bk ls).get i (Tup.levels ts next))
        ((hbk ls Js').get i (Tup.levels ts next) xs)
        (hGk.freshTup xs) (hG.freshMVals xs) (hbo.upd_fupdTup xs) (hboK.upd_fupdTup xs)
        hD' (analyzeMemB_get_summary next baseOffK (bk ls) i hspB') m'
        ⟨hcb_m', hinv_m', hinvKeys'.upd_fupdTup xs⟩ hb₂
    have hml' : MemLoadGood ρ next cache inv' m :=
      ⟨hml.1, (InvMemGood.of_cache (hml.1.filterSummary sum)).append hml.2.1, hinvKeys'⟩
    exact ihk Js Js' next ρ baseOff baseOffK cache inv' (kk ls) (hkk ls Js')
      hGk hG hbo hboK hD' hspK' m hml' (hw Js' hcl2)

/-! ## Relational well-formedness for `memLoadSweep` (`MValRel`, `RelCache`, `memLoad_wf`) -/

section
variable {V₁ V₂ : Ty → Type}

/-- Two `MVal`s are related when their output operands are `ArgRel`-related and keys match. -/
def MValRel (G' : Ctx V₁ V₂) {t : Ty} (m₁ : MVal V₁ t) (m₂ : MVal V₂ t) : Prop :=
  ArgRel G' t m₁.out m₂.out ∧ m₁.key = m₂.key

theorem MValRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {m₁ : MVal V₁ t} {m₂ : MVal V₂ t} (h : MValRel G₁ m₁ m₂) : MValRel G₂ m₁ m₂ :=
  ⟨h.1.weaken hsub, h.2⟩

/-- Context relation for `memLoad_wf`. -/
def MRelG (G' : Ctx V₁ V₂) (G : Ctx (MVal V₁) (MVal V₂)) : Prop :=
  ∀ p ∈ G, MValRel G' p.2.1 p.2.2

theorem MRelG.cons {G' : Ctx V₁ V₂} {G : Ctx (MVal V₁) (MVal V₂)} (hG : MRelG G' G)
    {t : Ty} {m₁ : MVal V₁ t} {m₂ : MVal V₂ t} (hm : MValRel G' m₁ m₂) :
    MRelG G' (⟨t, m₁, m₂⟩ :: G)
  | _, .head _ => hm
  | _, .tail _ hp => hG _ hp

theorem MRelG.weaken {G' G'' : Ctx V₁ V₂} {G : Ctx (MVal V₁) (MVal V₂)}
    (hG : MRelG G' G) (hsub : ∀ p ∈ G', p ∈ G'') : MRelG G'' G :=
  fun p hp => (hG p hp).weaken hsub

private theorem MRelG.freshMVals_only {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts)
    (b : Nat) :
    MRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshMVals ts xs₁ b) (freshMVals ts xs₂ b)) :=
  mem_tup_zip_tupFreshWith (fun x n => MVal.fresh x n) (fun x n => MVal.fresh x n)
    (P := fun G' _ m₁ m₂ => MValRel G' m₁ m₂)
    (fun hsub _ _ _ h => h.weaken hsub)
    (fun _ _ _ => ⟨.var List.mem_cons_self, rfl⟩)
    xs₁ xs₂ b

theorem MRelG.freshMVals {G' : Ctx V₁ V₂} {G : Ctx (MVal V₁) (MVal V₂)} (hG : MRelG G' G)
    {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    MRelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshMVals ts xs₁ b) (freshMVals ts xs₂ b) ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact (MRelG.freshMVals_only xs₁ xs₂ b p hp).weaken fun _ hq => List.mem_append_left G' hq
  · exact (hG p hp).weaken fun _ hq => List.mem_append_right _ hq

theorem MRelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (MVal V₁) (MVal V₂)} (hG : MRelG G' G)
    {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    MRelG (⟨t, v₁, v₂⟩ :: G') (⟨t, MVal.fresh v₁ b, MVal.fresh v₂ b⟩ :: G) :=
  (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq).cons ⟨.var List.mem_cons_self, rfl⟩

theorem ArgRel.mout {G' : Ctx V₁ V₂} {G : Ctx (MVal V₁) (MVal V₂)} (hG : MRelG G' G)
    {t : Ty} {a₁ : Arg (MVal V₁) t} {a₂ : Arg (MVal V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t a₁.mout a₂.mout
  | .var h => (hG _ h).1
  | .imm c => .imm c

theorem ArgRel.mkey_eq {G' : Ctx V₁ V₂} {G : Ctx (MVal V₁) (MVal V₂)} (hG : MRelG G' G)
    {t : Ty} {a₁ : Arg (MVal V₁) t} {a₂ : Arg (MVal V₂) t} :
    ArgRel G t a₁ a₂ → a₁.mkey = a₂.mkey
  | .var h => (hG _ h).2
  | .imm _ => rfl

theorem TRel.mout {G' : Ctx V₁ V₂} {G : Ctx (MVal V₁) (MVal V₂)} (hG : MRelG G' G)
    {ts : List Ty} {as₁ : Tup (Arg (MVal V₁)) ts} {as₂ : Tup (Arg (MVal V₂)) ts}
    (h : TRel (ArgRel G) as₁ as₂) : TRel (ArgRel G') (tupMOut as₁) (tupMOut as₂) :=
  TRel.tupMapArg_rel (fun _ => Arg.mout) (fun _ => Arg.mout) (fun ha => ha.mout hG) h

theorem TRel.mkey_eq {G' : Ctx V₁ V₂} {G : Ctx (MVal V₁) (MVal V₂)} (hG : MRelG G' G) :
    {ts : List Ty} → {as₁ : Tup (Arg (MVal V₁)) ts} → {as₂ : Tup (Arg (MVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ → tupMKey as₁ = tupMKey as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (h.mkey_eq hG) (TRel.mkey_eq hG hs)

/-- Pointwise relation on `CacheEntry` pairs sharing identical `(baseKey, off, ty, valKey)`. -/
inductive RelCacheEntry (G' : Ctx V₁ V₂) : CacheEntry V₁ → CacheEntry V₂ → Prop
  | mk {b : FKey i64} {off : BitVec 64} {t : Ty}
      {v₁ : Arg V₁ t} {v₂ : Arg V₂ t} {k : FKey t} :
      ArgRel G' t v₁ v₂ →
      RelCacheEntry G' ⟨b, off, t, v₁, k⟩ ⟨b, off, t, v₂, k⟩

/-- Pointwise relation on dominating memory caches. -/
inductive RelCache (G' : Ctx V₁ V₂) : List (CacheEntry V₁) → List (CacheEntry V₂) → Prop
  | nil : RelCache G' [] []
  | cons {e₁ e₂ c₁ c₂} : RelCacheEntry G' e₁ e₂ → RelCache G' c₁ c₂ →
      RelCache G' (e₁ :: c₁) (e₂ :: c₂)

theorem RelCache.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {c₁ : List (CacheEntry V₁)} → {c₂ : List (CacheEntry V₂)} →
    RelCache G₁ c₁ c₂ → RelCache G₂ c₁ c₂
  | _, _, .nil => .nil
  | _, _, .cons (.mk harg) hr => .cons (.mk (harg.weaken hsub)) (RelCache.weaken hsub hr)

theorem RelCache.filterWrite {G' : Ctx V₁ V₂} (b : FKey i64) (off : BitVec 64) (bytes : Nat) :
    {c₁ : List (CacheEntry V₁)} → {c₂ : List (CacheEntry V₂)} →
    RelCache G' c₁ c₂ →
    RelCache G' (filterCacheWrite b off bytes c₁) (filterCacheWrite b off bytes c₂)
  | _, _, .nil => .nil
  | _, _, .cons (@RelCacheEntry.mk _ _ _ b' o' t' v₁ v₂ k harg) hr => by
    simp only [filterCacheWrite, List.filter, entryDisjointWrite]
    cases fkey64Beq b' b && spanDisjoint off bytes o' t'.bytes
    · exact RelCache.filterWrite b off bytes hr
    · exact .cons (@RelCacheEntry.mk _ _ _ b' o' t' v₁ v₂ k harg)
        (RelCache.filterWrite b off bytes hr)

theorem RelCache.filterSummary {G' : Ctx V₁ V₂} (s : MemSummary) :
    {c₁ : List (CacheEntry V₁)} → {c₂ : List (CacheEntry V₂)} →
    RelCache G' c₁ c₂ →
    RelCache G' (filterCacheSummary s c₁) (filterCacheSummary s c₂)
  | _, _, .nil => .nil
  | _, _, .cons (@RelCacheEntry.mk _ _ _ b' o' t' v₁ v₂ k harg) hr => by
    simp only [filterCacheSummary, List.filter, summaryDisjointEntry, entryDisjointWrite]
    cases s with
    | unknown => exact RelCache.filterSummary .unknown hr
    | exact ws =>
      dsimp only
      cases ws.all fun w => fkey64Beq b' w.baseKey && spanDisjoint w.off w.bytes o' t'.bytes
      · exact RelCache.filterSummary (.exact ws) hr
      · exact .cons (@RelCacheEntry.mk _ _ _ b' o' t' v₁ v₂ k harg)
          (RelCache.filterSummary (.exact ws) hr)

inductive MLookupRel (G' : Ctx V₁ V₂) (t : Ty) :
    Option (MVal V₁ t) → Option (MVal V₂ t) → Prop
  | none : MLookupRel G' t none none
  | some {m₁ : MVal V₁ t} {m₂ : MVal V₂ t} :
      MValRel G' m₁ m₂ → MLookupRel G' t (some m₁) (some m₂)

theorem RelCache.lookup {G' : Ctx V₁ V₂} (b : FKey i64) (off : BitVec 64) (t : Ty) :
    {c₁ : List (CacheEntry V₁)} → {c₂ : List (CacheEntry V₂)} → RelCache G' c₁ c₂ →
    MLookupRel G' t (lookupCache b off t c₁) (lookupCache b off t c₂)
  | _, _, .nil => .none
  | _, _, .cons (.mk harg) hr => by
    dsimp only [lookupCache]
    cases fkey64Beq _ b && _ == off
    · exact RelCache.lookup b off t hr
    · cases hty : tyDecEq _ t with
      | isFalse _ => exact RelCache.lookup b off t hr
      | isTrue heq => subst heq; exact .some ⟨harg, rfl⟩

end

/-- Well-formedness preservation for `memLoadSweep`, proved via `Wf.induct`. -/
theorem memLoad_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (MVal V₁) (MVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (MVal V₁) L₁ rs} {e₂ : Expr (MVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {Gk : Ctx K (MVal V₁)} {Dk : Ctx KL0 L₁}
      (next : Nat) (baseOff baseOffK : BaseOffMap)
      (c₁ : List (CacheEntry V₁)) (c₂ : List (CacheEntry V₂))
      (ek : Expr K KL0 rs),
      MRelG G' G → RelCache G' c₁ c₂ → Wf Gk Dk ek e₁ →
      Wf G' D (memLoadSweep next baseOff c₁ (analyzeMem next baseOffK ek).2 e₁)
              (memLoadSweep next baseOff c₂ (analyzeMem next baseOffK ek).2 e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' Gk Dk next baseOff baseOffK c₁ c₂ ek hG hc hwk
    rcases hwk.rhs_let with ⟨opk, kk, rfl, _, hkk⟩
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      dsimp only [analyzeMem, memLoadSweep]
      rw [TRel.mkey_eq hG hargs]
      refine .let_ (.mk code (TRel.mout hG hargs)) fun xs₁ xs₂ => ?_
      have hsub : ∀ p ∈ G', p ∈ (Tup.zip xs₁ xs₂ ++ G') := fun _ hq => List.mem_append_right _ hq
      exact ih _ _ (next + ts.length) _ _ c₁ c₂ (kk (Tup.levels ts next))
        (hG.freshMVals xs₁ xs₂ next) (hc.weaken hsub)
        (hkk (Tup.levels ts next) (freshMVals ts xs₁ next))
  | @load G D t a₁ a₂ k₁ k₂ ha _ ih =>
    intro G' Gk Dk next baseOff baseOffK c₁ c₂ ek hG hc hwk
    rcases hwk.rhs_load with ⟨_, kk, rfl, _, hkk⟩
    dsimp only [analyzeMem]
    rw [memLoadSweep_load, memLoadSweep_load, ha.mkey_eq hG]
    have hlook := hc.lookup (resolveKey baseOff a₂.mkey).1 (resolveKey baseOff a₂.mkey).2 t
    generalize hl1 : lookupCache _ _ t c₁ = r₁ at hlook
    generalize hl2 : lookupCache _ _ t c₂ = r₂ at hlook
    cases hlook with
    | some hm =>
      exact ih _ _ (next + 1) baseOff baseOffK c₁ c₂ (kk next) (hG.cons hm) hc (hkk next _)
    | none =>
      refine .load t (ha.mout hG) fun v₁ v₂ => ?_
      have hsub : ∀ p ∈ G', p ∈ (⟨t, v₁, v₂⟩ :: G') := fun _ hq => List.mem_cons_of_mem _ hq
      exact ih _ _ (next + 1) baseOff baseOffK _ _ (kk next)
        (hG.freshOne v₁ v₂ next) (.cons (.mk (.var List.mem_cons_self)) (hc.weaken hsub))
        (hkk next _)
  | @store G D t v₁ v₂ a₁ a₂ k₁ k₂ hv ha _ ih =>
    intro G' Gk Dk next baseOff baseOffK c₁ c₂ ek hG hc hwk
    rcases hwk.rhs_store with ⟨_, _, kk, rfl, _, _, hkk⟩
    dsimp only [analyzeMem, memLoadSweep]
    rw [ha.mkey_eq hG, hv.mkey_eq hG]
    refine .store (hv.mout hG) (ha.mout hG) ?_
    split
    · exact ih next baseOff baseOffK _ _ kk hG
        (.cons (.mk (hv.mout hG)) (hc.filterWrite _ _ t.bytes)) hkk
    · exact ih next baseOff baseOffK _ _ kk hG (hc.filterWrite _ _ t.bytes) hkk
  | call f hargs _ ih =>
    intro G' Gk Dk next baseOff baseOffK c₁ c₂ ek hG hc hwk
    rcases hwk.rhs_call with ⟨_, kk, rfl, _, hkk⟩
    dsimp only [analyzeMem, memLoadSweep]
    refine .call f (TRel.mout hG hargs) fun xs₁ xs₂ => ?_
    exact ih _ _ (next + _) baseOff baseOffK [] [] (kk (Tup.levels _ next))
      (hG.freshMVals xs₁ xs₂ next) .nil (hkk (Tup.levels _ next) (freshMVals _ xs₁ next))
  | jnz hcj _ _ iht ihe =>
    intro G' Gk Dk next baseOff baseOffK c₁ c₂ ek hG hc hwk
    rcases hwk.rhs_jnz with ⟨_, tk, ek', rfl, _, htk, hek⟩
    dsimp only [analyzeMem, memLoadSweep]
    exact .jnz (hcj.mout hG) (iht next baseOff baseOffK c₁ c₂ tk hG hc htk)
      (ihe next baseOff baseOffK c₁ c₂ ek' hG hc hek)
  | jump hj hargs =>
    intro G' _ _ _ _ _ _ _ _ hG _ hwk; rcases hwk.rhs_jump with ⟨_, _, rfl, _, _⟩
    exact .jump hj (TRel.mout hG hargs)
  | ret hvs =>
    intro G' _ _ _ _ _ _ _ _ hG _ hwk; rcases hwk.rhs_ret with ⟨_, rfl, _⟩
    exact .ret (TRel.mout hG hvs)
  | exit f hargs =>
    intro G' _ _ _ _ _ _ _ _ hG _ hwk; rcases hwk.rhs_exit with ⟨_, rfl, _⟩
    exact .exit f (TRel.mout hG hargs)
  | hlt =>
    intro _ _ _ _ _ _ _ _ _ _ _ hwk; rw [hwk.rhs_hlt]; exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' Gk Dk next baseOff baseOffK c₁ c₂ ek hG hc hwk
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    dsimp only [analyzeMem, memLoadSweep]
    let ls := Tup.units sig
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ?_)
    · rw [memLoadSweepB_analyzeMemB_get, memLoadSweepB_analyzeMemB_get]
      have hsub : ∀ p ∈ G', p ∈ (Tup.zip xs₁ xs₂ ++ G') := fun _ hq => List.mem_append_right _ hq
      exact ihb Js₁ Js₂ i _ _ (next + _) baseOff baseOffK _ _ ((bk ls).get i (Tup.levels _ next))
        (hG.freshMVals xs₁ xs₂ next) ((hc.filterSummary _).weaken hsub)
        ((hbk ls Js₁).get i (Tup.levels _ next) (freshMVals _ xs₁ next))
    · exact ihk Js₁ Js₂ next baseOff baseOffK c₁ c₂ (kk ls) hG hc (hkk ls Js₁)

theorem Func.memLoad_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.memLoad f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (MVal V₁) (MVal V₂) L₁ L₂ (freshMVals as xs₁ 0) (freshMVals as xs₂ 0)
  have hwk := hf K (MVal V₁) KL0 L₁ (Tup.levels as 0) (freshMVals as xs₁ 0)
  have hrel : MRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshMVals as xs₁ 0) (freshMVals as xs₂ 0)) := by
    rw [← List.append_nil (Tup.zip xs₁ xs₂),
        ← List.append_nil (Tup.zip (freshMVals as xs₁ 0) (freshMVals as xs₂ 0))]
    exact MRelG.freshMVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact LeanQbe.T.memLoad_wf hwf as.length .empty .empty [] []
    (f K KL0 (Tup.levels as 0)) hrel .nil hwk

theorem Func.memLoad_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.memLoad f) xs m Q X := by
  have hwf := hf (MVal Val) Val Cont Cont (freshMVals as xs 0) xs
  have hwk := hf K Val KL0 Cont (Tup.levels as 0) xs
  let ρ := fupdTup (fun _ _ => default) 0 xs
  have hGk : KGood ρ as.length (Tup.zip (Tup.levels as 0) xs) := by
    rw [← List.append_nil (Tup.zip (Tup.levels as 0) xs)]
    exact Nat.zero_add as.length ▸ KGood.freshTup (ρ := fun _ _ => default) (next := 0) (Gk := [])
      (fun _ hp => nomatch hp) xs
  have hG : MGood ρ as.length (Tup.zip (freshMVals as xs 0) xs) := by
    rw [← List.append_nil (Tup.zip (freshMVals as xs 0) xs)]
    exact Nat.zero_add as.length ▸ MGood.freshMVals (ρ := fun _ _ => default) (next := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact memLoad_wp hwf as.length ρ .empty .empty [] [] (f K KL0 (Tup.levels as 0))
    hwk hGk hG (BaseOffGood.empty ρ as.length) (BaseOffGood.empty ρ as.length)
    (fun _ hp => nomatch hp) (fun _ hp => nomatch hp) m (MemLoadGood.empty ρ as.length m) h

/-! ## `AssumeElim` correctness (`assumeElim_wp`, `assumeElim_wf`, `Func.assumeElim_*`) -/

theorem Expr.isHlt_true_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {e : Expr V L rs} → e.isHlt = true → e = .hlt
  | .hlt, _ => rfl

theorem Wf.isHlt_eq {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (h : Wf G D e₁ e₂) : e₁.isHlt = e₂.isHlt := by cases h <;> rfl

theorem assumeElimB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks V L rs sig) →
    (i : Member ts sig) → (xs : Tup V ts) →
    (assumeElimB bs).get i xs = assumeElim (bs.get i xs)
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => assumeElimB_get bs i xs

/-- Weakest-precondition preservation for `assumeElim`, proved via `Expr.induct`. -/
theorem assumeElim_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (e : Expr Val Cont rs) : ∀ m, wp Γ Q X e m → wp Γ Q X (assumeElim e) m := by
  induction e using Expr.induct with
  | let_ op k ih =>
    intro m h
    dsimp only [assumeElim, wp] at h ⊢
    exact Op.wp_mono (fun r => ih r m) h
  | load t a k ih => intro m ⟨v, hv, hk⟩; exact ⟨v, hv, ih v m hk⟩
  | store v a k ih => intro m ⟨hok, hk⟩; exact ⟨hok, ih _ hk⟩
  | call f args k ih =>
    intro m ⟨P, E, hΓ, hP, hE⟩
    exact ⟨P, E, hΓ, fun r m' hr => ih r m' (hP r m' hr), hE⟩
  | jnz c t e iht ihe =>
    intro m h
    dsimp only [assumeElim, mkJnzAssume]
    cases he : (assumeElim e).isHlt
    · cases ht : (assumeElim t).isHlt
      · simp only [Bool.false_eq_true, ↓reduceIte]; dsimp only [wp]
        exact ⟨fun hc => iht m (h.1 hc), fun hc => ihe m (h.2 hc)⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases hc : c.val
        · exact ihe m (h.2 hc)
        · have hw' := iht m (h.1 hc); rw [Expr.isHlt_true_eq ht] at hw'; exact False.elim hw'
    · simp only [↓reduceIte]
      cases hc : c.val
      · have hw' := ihe m (h.2 hc); rw [Expr.isHlt_true_eq he] at hw'; exact False.elim hw'
      · exact iht m (h.1 hc)
  | jump _ _ | ret _ | exit _ _ | hlt => exact fun _ h => h
  | group bodies k ihb ihk =>
    intro m h Js hc
    refine ihk Js m (h Js ?_)
    rw [closed_iff] at hc ⊢
    intro ts i xs m' hb
    exact hc i xs m' (assumeElimB_get (bodies Js) i xs ▸ ihb Js i xs m' hb)

/-- Relational well-formedness preservation for `assumeElim`, proved via `Wf.induct`. -/
theorem assumeElim_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx V₁ V₂} {D : Ctx L₁ L₂} {e₁ : Expr V₁ L₁ rs} {e₂ : Expr V₂ L₂ rs}
    (hwf : Wf G D e₁ e₂) : Wf G D (assumeElim e₁) (assumeElim e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih => exact .let_ hop ih
  | load t ha _ ih => exact .load t ha ih
  | store hv ha _ ih => exact .store hv ha ih
  | call f hargs _ ih => exact .call f hargs ih
  | jnz hc _ _ iht ihe =>
    dsimp only [assumeElim, mkJnzAssume]; rw [iht.isHlt_eq, ihe.isHlt_eq]
    split
    · exact iht
    · split
      · exact ihe
      · exact .jnz hc iht ihe
  | jump hj hargs => exact .jump hj hargs
  | ret hvs => exact .ret hvs
  | exit f hargs => exact .exit f hargs
  | hlt => exact .hlt
  | group _ _ ihb ihk =>
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) ihk
    rw [assumeElimB_get, assumeElimB_get]; exact ihb Js₁ Js₂ i xs₁ xs₂

theorem Func.assumeElim_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.assumeElim f).Wf :=
  fun V₁ V₂ L₁ L₂ xs₁ xs₂ => LeanQbe.T.assumeElim_wf (hf V₁ V₂ L₁ L₂ xs₁ xs₂)

theorem Func.assumeElim_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.assumeElim f) xs m Q X :=
  let _ := hf
  assumeElim_wp (f Val Cont xs) m h

end LeanQbe.T
