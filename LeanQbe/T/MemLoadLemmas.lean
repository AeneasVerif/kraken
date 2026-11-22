module

public import LeanQbe.T.MemLoad
public import LeanQbe.T.OptUtilLemmas
import LeanQbe.T.OpsLemmas

/-!
# Correctness of `MemLoad` and `AssumeElim` (`O-M2`)

* `spanDisjoint_sound`: `BitVec 64` offset-interval disjointness cancels common `base + idx * scale`
  even across wraparound, connecting to `OpsLemmas.loadVal_storeMem_disjoint`.
* `stepBaseOff_good`: symbolic `(base, idx, scale, off)` tracking preserves `BaseOffGood` across
  `add i64`, `sub i64`, `mul i64`, `shl i64`, `copy i64`, `zext 32 64`, `sext 32 64`, and all other
  opcodes.
* `memLoad_wp`, `memLoad_wf`, `Func.memLoad_wf`, `Func.memLoad_spec`: soundness and
  well-formedness of indexed lexical load CSE, store-to-load forwarding, and acyclic/cyclic group
  kill-set preservation.
* `assumeElim_wp`, `assumeElim_wf`, `Func.assumeElim_wf`, `Func.assumeElim_spec`: soundness and
  well-formedness of `.jnz c t .hlt → t` and `.jnz c .hlt e → e`.
-/

set_option autoImplicit false

namespace LeanQbe.T

/-! ## Key equality, disjointness, `BaseOffGood`, and `stepBaseOff_good` -/

theorem fkey64Beq_iff_eq : {a b : FKey i64} → fkey64Beq a b = true ↔ a = b
  | .var i, .var j => by dsimp only [fkey64Beq]; simp
  | .imm a, .imm b => by dsimp only [fkey64Beq]; simp
  | .var _, .imm _ | .imm _, .var _ => by dsimp only [fkey64Beq]; simp

theorem fkey32Beq_iff_eq : {a b : FKey (.bits 32)} → fkey32Beq a b = true ↔ a = b
  | .var i, .var j => by dsimp only [fkey32Beq]; simp
  | .imm a, .imm b => by dsimp only [fkey32Beq]; simp
  | .var _, .imm _ | .imm _, .var _ => by dsimp only [fkey32Beq]; simp

theorem idxKeyBeq_iff_eq : {a b : IdxKey} → idxKeyBeq a b = true ↔ a = b
  | .none, .none => by dsimp only [idxKeyBeq]; simp
  | .k64 a, .k64 b => by dsimp only [idxKeyBeq]; simp [fkey64Beq_iff_eq]
  | .zext32 a, .zext32 b => by dsimp only [idxKeyBeq]; simp [fkey32Beq_iff_eq]
  | .sext32 a, .sext32 b => by dsimp only [idxKeyBeq]; simp [fkey32Beq_iff_eq]
  | .none, .k64 _ | .none, .zext32 _ | .none, .sext32 _
  | .k64 _, .none | .k64 _, .zext32 _ | .k64 _, .sext32 _
  | .zext32 _, .none | .zext32 _, .k64 _ | .zext32 _, .sext32 _
  | .sext32 _, .none | .sext32 _, .k64 _ | .sext32 _, .zext32 _ => by
    dsimp only [idxKeyBeq]; simp

theorem AddrKey.sameBase_iff {a b : AddrKey} :
    a.sameBase b = true ↔ a.base = b.base ∧ a.idx = b.idx ∧ a.scale = b.scale := by
  simp only [AddrKey.sameBase, Bool.and_eq_true, fkey64Beq_iff_eq, idxKeyBeq_iff_eq, beq_iff_eq,
    and_assoc]

theorem AddrKey.beq_iff {a b : AddrKey} : a.beq b = true ↔ a = b := by
  cases a; cases b
  simp only [AddrKey.beq, Bool.and_eq_true, AddrKey.sameBase_iff, beq_iff_eq, AddrKey.mk.injEq,
    and_assoc]

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

/-- Evaluation of an `IdxKey` under valuation `ρ`. -/
public def IdxKey.eval (ρ : FEnv) : IdxKey → BitVec 64
  | .none => 0#64
  | .k64 k => k.fev ρ
  | .zext32 k => (k.fev ρ).setWidth 64
  | .sext32 k => (k.fev ρ).signExtend 64

/-- All variable levels inside an `IdxKey` are `< next`. -/
public def IdxKey.FLt (next : Nat) : IdxKey → Prop
  | .none => True
  | .k64 k => k.FLt next
  | .zext32 k => k.FLt next
  | .sext32 k => k.FLt next

theorem IdxKey.FLt.le {b₁ b₂ : Nat} (h : b₁ ≤ b₂) : ∀ {ik : IdxKey}, ik.FLt b₁ → ik.FLt b₂
  | .none, _ => trivial
  | .k64 _, hk => FKey.FLt.le h hk
  | .zext32 _, hk => FKey.FLt.le h hk
  | .sext32 _, hk => FKey.FLt.le h hk

theorem IdxKey.FLt.mono {b : Nat} {ik : IdxKey} (h : ik.FLt b) : ik.FLt (b + 1) :=
  h.le (Nat.le_succ b)

theorem IdxKey.FLt.add {b k : Nat} {ik : IdxKey} (h : ik.FLt b) : ik.FLt (b + k) :=
  h.le (Nat.le_add_right b k)

theorem IdxKey.eval_fupd {ρ : FEnv} {b : Nat} {u : Ty} (v : Val u) :
    {ik : IdxKey} → ik.FLt b → ik.eval (fupd ρ b v) = ik.eval ρ
  | .none, _ => rfl
  | .k64 _, h => FKey.fev_fupd v h
  | .zext32 _, h => congrArg (BitVec.setWidth 64) (FKey.fev_fupd v h)
  | .sext32 _, h => congrArg (BitVec.signExtend 64) (FKey.fev_fupd v h)

theorem IdxKey.eval_fupdTup {ρ : FEnv} {b : Nat} {ts : List Ty} (xs : Tup Val ts) :
    {ik : IdxKey} → ik.FLt b → ik.eval (fupdTup ρ b xs) = ik.eval ρ
  | .none, _ => rfl
  | .k64 _, h => FKey.fev_fupdTup xs h
  | .zext32 _, h => congrArg (BitVec.setWidth 64) (FKey.fev_fupdTup xs h)
  | .sext32 _, h => congrArg (BitVec.signExtend 64) (FKey.fev_fupdTup xs h)

/-- Base part `base + idx * scale` of an `AddrKey` under valuation `ρ`. -/
public def AddrKey.baseEval (ρ : FEnv) (ak : AddrKey) : BitVec 64 :=
  ak.base.fev ρ + ak.idx.eval ρ * ak.scale

/-- Full `BitVec 64` evaluation `base + idx * scale + off` of an `AddrKey`. -/
public def AddrKey.eval (ρ : FEnv) (ak : AddrKey) : BitVec 64 :=
  ak.baseEval ρ + ak.off

/-- Variable-level bound for `AddrKey`. -/
public def AddrKey.FLt (next : Nat) (ak : AddrKey) : Prop :=
  ak.base.FLt next ∧ ak.idx.FLt next

theorem AddrKey.FLt.le {b₁ b₂ : Nat} (h : b₁ ≤ b₂) {ak : AddrKey} (hk : ak.FLt b₁) :
    ak.FLt b₂ :=
  ⟨hk.1.le h, hk.2.le h⟩

theorem AddrKey.FLt.mono {b : Nat} {ak : AddrKey} (h : ak.FLt b) : ak.FLt (b + 1) :=
  h.le (Nat.le_succ b)

theorem AddrKey.FLt.add {b k : Nat} {ak : AddrKey} (h : ak.FLt b) : ak.FLt (b + k) :=
  h.le (Nat.le_add_right b k)

theorem AddrKey.eval_fupd {ρ : FEnv} {b : Nat} {u : Ty} (v : Val u) {ak : AddrKey}
    (h : ak.FLt b) : ak.eval (fupd ρ b v) = ak.eval ρ := by
  simp only [AddrKey.eval, AddrKey.baseEval, FKey.fev_fupd v h.1, IdxKey.eval_fupd v h.2]

theorem AddrKey.eval_fupdTup {ρ : FEnv} {b : Nat} {ts : List Ty} (xs : Tup Val ts)
    {ak : AddrKey} (h : ak.FLt b) : ak.eval (fupdTup ρ b xs) = ak.eval ρ := by
  simp only [AddrKey.eval, AddrKey.baseEval, FKey.fev_fupdTup xs h.1, IdxKey.eval_fupdTup xs h.2]

theorem AddrKey.baseEval_eq_of_sameBase (ρ : FEnv) {a b : AddrKey} (h : a.sameBase b = true) :
    a.baseEval ρ = b.baseEval ρ := by
  obtain ⟨h1, h2, h3⟩ := AddrKey.sameBase_iff.1 h
  simp only [AddrKey.baseEval, h1, h2, h3]

/-- Symbolic address map agrees with valuation `ρ` below `next` and is empty above. -/
public def BaseOffGood (ρ : FEnv) (next : Nat) (m : BaseOffMap) : Prop :=
  (∀ i < next,
    let e := m.getD i ⟨.var i, .k64 (.var i)⟩
    e.ak.FLt next ∧ e.ak.eval ρ = ρ i64 i ∧
    e.idxSelf.FLt next ∧ e.idxSelf.eval ρ = ρ i64 i) ∧
  (∀ i ≥ next, m.find? i = none)

theorem BaseOffGood.empty (ρ : FEnv) (next : Nat) :
    BaseOffGood ρ next .empty := by
  refine ⟨fun i hi => ?_, fun _ _ => rfl⟩
  simp only [Trie.getD_empty]
  exact ⟨⟨hi, trivial⟩, by simp [AddrKey.eval, AddrKey.baseEval, AddrKey.var, IdxKey.eval,
    FKey.fev], hi, rfl⟩

theorem BaseOffGood.upd_fupd {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) {u : Ty} (v : Val u) :
    BaseOffGood (fupd ρ next v) (next + 1) m := by
  refine ⟨fun i hi => ?_, fun i hi => hm.2 i (by omega)⟩
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hlt | rfl
  · obtain ⟨hflt, hev, hiflt, hiev⟩ := hm.1 i hlt
    refine ⟨hflt.mono, ?_, hiflt.mono, ?_⟩
    · rw [AddrKey.eval_fupd v hflt, fupd_ne ρ v (Nat.ne_of_lt hlt)]
      exact hev
    · rw [IdxKey.eval_fupd v hiflt, fupd_ne ρ v (Nat.ne_of_lt hlt)]
      exact hiev
  · have hnone := hm.2 i (Nat.le_refl i)
    simp only [Trie.getD, hnone, Option.getD_none]
    exact ⟨⟨hi, trivial⟩, by simp [AddrKey.eval, AddrKey.baseEval, AddrKey.var, IdxKey.eval,
      FKey.fev], hi, rfl⟩

theorem BaseOffGood.upd_fupdTup {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) :
    {ts : List Ty} → (xs : Tup Val ts) → BaseOffGood (fupdTup ρ next xs) (next + ts.length) m
  | [], () => hm
  | _ :: ts, (x, xs) => by
    simp only [fupdTup, List.length_cons]
    have h1 := (hm.upd_fupd x).upd_fupdTup xs
    rwa [show next + 1 + ts.length = next + (ts.length + 1) by omega] at h1

theorem BaseOffGood.insert_next {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) (v : Val i64) {e : BaseOffEntry}
    (hakFlt : e.ak.FLt (next + 1)) (hakEv : e.ak.eval (fupd ρ next v) = v)
    (hiFlt : e.idxSelf.FLt (next + 1)) (hiEv : e.idxSelf.eval (fupd ρ next v) = v) :
    BaseOffGood (fupd ρ next v) (next + 1) (m.insert next e) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hi) with hlt | rfl
    · rw [Trie.getD_insert_ne m e ⟨.var i, .k64 (.var i)⟩ (Nat.ne_of_lt hlt)]
      obtain ⟨hflt, hev, hiflt, hiev⟩ := hm.1 i hlt
      refine ⟨hflt.mono, ?_, hiflt.mono, ?_⟩
      · rw [AddrKey.eval_fupd v hflt, fupd_ne ρ v (Nat.ne_of_lt hlt)]
        exact hev
      · rw [IdxKey.eval_fupd v hiflt, fupd_ne ρ v (Nat.ne_of_lt hlt)]
        exact hiev
    · simp only [Trie.getD_insert_self]
      refine ⟨hakFlt, ?_, hiFlt, ?_⟩
      · rw [fupd_eq]; exact hakEv
      · rw [fupd_eq]; exact hiEv
  · rw [Trie.find?_insert_ne m e (by omega)]
    exact hm.2 i (by omega)

theorem BaseOffGood.insert_old {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) (v : Val i64) {e : BaseOffEntry}
    (hakFlt : e.ak.FLt next) (hakEv : e.ak.eval ρ = v)
    (hiFlt : e.idxSelf.FLt next) (hiEv : e.idxSelf.eval ρ = v) :
    BaseOffGood (fupd ρ next v) (next + 1) (m.insert next e) :=
  hm.insert_next v hakFlt.mono ((AddrKey.eval_fupd v hakFlt).trans hakEv)
    hiFlt.mono ((IdxKey.eval_fupd v hiFlt).trans hiEv)

theorem resolveEntry_good {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) {k : FKey i64} (hk : k.FLt next) :
    (resolveEntry m k).ak.FLt next ∧ (resolveEntry m k).ak.eval ρ = k.fev ρ ∧
    (resolveEntry m k).idxSelf.FLt next ∧ (resolveEntry m k).idxSelf.eval ρ = k.fev ρ := by
  cases k with
  | var i => exact hm.1 i hk
  | imm c =>
    dsimp only [resolveEntry]
    refine ⟨⟨trivial, trivial⟩, by simp [AddrKey.eval, AddrKey.baseEval, AddrKey.const,
      IdxKey.eval, FKey.fev], ?_, ?_⟩
    · split <;> trivial
    · split
      · next h => simp [IdxKey.eval, beq_iff_eq.1 h, FKey.fev]
      · rfl

theorem resolveKey_good {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) {k : FKey i64} (hk : k.FLt next) :
    (resolveKey m k).FLt next ∧ (resolveKey m k).eval ρ = k.fev ρ :=
  ⟨(resolveEntry_good hm hk).1, (resolveEntry_good hm hk).2.1⟩

theorem resolveIdx_good {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) {k : FKey i64} (hk : k.FLt next) :
    (resolveIdx m k).FLt next ∧ (resolveIdx m k).eval ρ = k.fev ρ :=
  ⟨(resolveEntry_good hm hk).2.2.1, (resolveEntry_good hm hk).2.2.2⟩

private theorem bv_add4 (a b c d : BitVec 64) : (a + c) + (b + d) = (a + b) + (c + d) := by
  rw [BitVec.add_assoc a c, BitVec.add_comm c (b + d), BitVec.add_assoc b d c,
    ← BitVec.add_assoc a b (d + c), BitVec.add_comm d c]

theorem addAddr_good {ρ : FEnv} {next : Nat} {m : BaseOffMap} (hm : BaseOffGood ρ next m)
    {x y : FKey i64} (hx : x.FLt next) (hy : y.FLt next) {ak : AddrKey}
    (h : addAddr m x y = some ak) :
    ak.FLt next ∧ ak.eval ρ = x.fev ρ + y.fev ρ := by
  obtain ⟨h1Flt, h1Ev⟩ := resolveKey_good hm hx
  obtain ⟨h2Flt, h2Ev⟩ := resolveKey_good hm hy
  dsimp only [addAddr] at h
  by_cases c1 : (fkey64Beq (resolveKey m x).base (.imm 0#64) &&
      (resolveKey m x).scale == 0#64) = true
  · simp only [c1, ↓reduceIte, Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, fkey64Beq_iff_eq, beq_iff_eq] at c1
    have ha1 : (resolveKey m x).off = x.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c1.1, c1.2, FKey.fev] using h1Ev
    refine ⟨h2Flt, ?_⟩
    simp only [AddrKey.eval, AddrKey.baseEval] at h2Ev ⊢
    rw [← BitVec.add_assoc, h2Ev, ha1, BitVec.add_comm]
  simp only [c1, Bool.false_eq_true, ↓reduceIte] at h
  by_cases c2 : (fkey64Beq (resolveKey m y).base (.imm 0#64) &&
      (resolveKey m y).scale == 0#64) = true
  · simp only [c2, ↓reduceIte, Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, fkey64Beq_iff_eq, beq_iff_eq] at c2
    have ha2 : (resolveKey m y).off = y.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c2.1, c2.2, FKey.fev] using h2Ev
    refine ⟨h1Flt, ?_⟩
    simp only [AddrKey.eval, AddrKey.baseEval] at h1Ev ⊢
    rw [← BitVec.add_assoc, h1Ev, ha2]
  simp only [c2, Bool.false_eq_true, ↓reduceIte] at h
  by_cases c3 : ((resolveKey m x).scale == 0#64 &&
      fkey64Beq (resolveKey m y).base (.imm 0#64)) = true
  · simp only [c3, ↓reduceIte, Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, fkey64Beq_iff_eq, beq_iff_eq] at c3
    have ha1 : (resolveKey m x).base.fev ρ + (resolveKey m x).off = x.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c3.1] using h1Ev
    have ha2 : (resolveKey m y).idx.eval ρ * (resolveKey m y).scale +
        (resolveKey m y).off = y.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c3.2, FKey.fev] using h2Ev
    refine ⟨⟨h1Flt.1, h2Flt.2⟩, ?_⟩
    simp only [AddrKey.eval, AddrKey.baseEval]
    rw [bv_add4, ha1, ha2]
  simp only [c3, Bool.false_eq_true, ↓reduceIte] at h
  by_cases c4 : ((resolveKey m y).scale == 0#64 &&
      fkey64Beq (resolveKey m x).base (.imm 0#64)) = true
  · simp only [c4, ↓reduceIte, Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, fkey64Beq_iff_eq, beq_iff_eq] at c4
    have ha2 : (resolveKey m y).base.fev ρ + (resolveKey m y).off = y.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c4.1] using h2Ev
    have ha1 : (resolveKey m x).idx.eval ρ * (resolveKey m x).scale +
        (resolveKey m x).off = x.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c4.2, FKey.fev] using h1Ev
    refine ⟨⟨h2Flt.1, h1Flt.2⟩, ?_⟩
    simp only [AddrKey.eval, AddrKey.baseEval]
    rw [BitVec.add_comm (resolveKey m x).off, bv_add4, ha2, ha1, BitVec.add_comm]
  simp only [c4, Bool.false_eq_true, ↓reduceIte] at h
  by_cases c5 : ((resolveKey m x).scale == 0#64 && (resolveKey m y).scale == 0#64) = true
  · simp only [c5, ↓reduceIte] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at c5
    have ha1 : (resolveKey m x).base.fev ρ + (resolveKey m x).off = x.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c5.1] using h1Ev
    have ha2 : (resolveKey m y).base.fev ρ + (resolveKey m y).off = y.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c5.2] using h2Ev
    cases hb1 : (resolveKey m x).base with
    | imm _ => rw [hb1] at h; cases h
    | var v₁ =>
      cases hb2 : (resolveKey m y).base with
      | imm _ => rw [hb1, hb2] at h; cases h
      | var v₂ =>
        rw [hb1, hb2] at h
        have hv1 : FKey.FLt next (.var v₁) := hb1 ▸ h1Flt.1
        have hv2 : FKey.FLt next (.var v₂) := hb2 ▸ h2Flt.1
        obtain ⟨hi1Flt, hi1Ev⟩ := resolveIdx_good hm hv1
        obtain ⟨hi2Flt, hi2Ev⟩ := resolveIdx_good hm hv2
        by_cases hlt1 : v₁ < v₂
        · simp only [hlt1, ↓reduceIte, Option.some.injEq] at h; subst h
          refine ⟨⟨hv1, hi2Flt⟩, ?_⟩
          simp only [AddrKey.eval, AddrKey.baseEval, hi2Ev, BitVec.mul_one]
          rw [bv_add4, ← hb1, ha1, ← hb2, ha2]
        · simp only [hlt1, ↓reduceIte] at h
          by_cases hlt2 : v₂ < v₁
          · simp only [hlt2, ↓reduceIte, Option.some.injEq] at h; subst h
            refine ⟨⟨hv2, hi1Flt⟩, ?_⟩
            simp only [AddrKey.eval, AddrKey.baseEval, hi1Ev, BitVec.mul_one]
            rw [BitVec.add_comm (resolveKey m x).off, bv_add4, ← hb2, ha2, ← hb1, ha1,
              BitVec.add_comm]
          · simp only [hlt2, ↓reduceIte, Option.some.injEq] at h; subst h
            have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.le_of_not_lt hlt2) (Nat.le_of_not_lt hlt1)
            refine ⟨⟨trivial, hi1Flt⟩, ?_⟩
            simp only [AddrKey.eval, AddrKey.baseEval, hi1Ev]
            rw [show FKey.fev ρ (Arg.imm 0#64 : FKey i64) = 0#64 from rfl, BitVec.zero_add,
              show (2#64 : BitVec 64) = 1#64 + 1#64 from rfl, BitVec.mul_add, BitVec.mul_one,
              bv_add4]
            have h1' : FKey.fev ρ (Arg.var v₁ : FKey i64) + (resolveKey m x).off = x.fev ρ :=
              hb1 ▸ ha1
            have h2' : FKey.fev ρ (Arg.var v₁ : FKey i64) + (resolveKey m y).off = y.fev ρ := by
              rw [heqv, ← hb2]; exact ha2
            rw [h1', h2']
  · simp only [c5, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem subAddr_good {ρ : FEnv} {next : Nat} {m : BaseOffMap} (hm : BaseOffGood ρ next m)
    {x y : FKey i64} (hx : x.FLt next) (hy : y.FLt next) {ak : AddrKey}
    (h : subAddr m x y = some ak) :
    ak.FLt next ∧ ak.eval ρ = x.fev ρ - y.fev ρ := by
  obtain ⟨h1Flt, h1Ev⟩ := resolveKey_good hm hx
  obtain ⟨_, h2Ev⟩ := resolveKey_good hm hy
  dsimp only [subAddr] at h
  by_cases c : (fkey64Beq (resolveKey m y).base (.imm 0#64) &&
      (resolveKey m y).scale == 0#64) = true
  · simp only [c, ↓reduceIte, Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, fkey64Beq_iff_eq, beq_iff_eq] at c
    have ha2 : (resolveKey m y).off = y.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c.1, c.2, FKey.fev] using h2Ev
    refine ⟨h1Flt, ?_⟩
    simp only [AddrKey.eval, AddrKey.baseEval] at h1Ev ⊢
    rw [BitVec.sub_eq_add_neg, ← BitVec.add_assoc, h1Ev, ha2, ← BitVec.sub_eq_add_neg]
  · simp only [c, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem scaleAddr_good {ρ : FEnv} {next : Nat} {m : BaseOffMap} (hm : BaseOffGood ρ next m)
    {arg : FKey i64} (harg : arg.FLt next) (d : BitVec 64) {ak : AddrKey}
    (h : scaleAddr m arg d = some ak) :
    ak.FLt next ∧ ak.eval ρ = arg.fev ρ * d := by
  obtain ⟨haFlt, haEv⟩ := resolveKey_good hm harg
  dsimp only [scaleAddr] at h
  by_cases cd0 : (d == 0#64) = true
  · simp only [cd0, ↓reduceIte, Option.some.injEq] at h; subst h
    rw [beq_iff_eq.1 cd0]
    exact ⟨⟨trivial, trivial⟩, by simp [AddrKey.eval, AddrKey.baseEval, AddrKey.const,
      IdxKey.eval, FKey.fev]⟩
  simp only [cd0, Bool.false_eq_true, ↓reduceIte] at h
  by_cases cd1 : (d == 1#64) = true
  · simp only [cd1, ↓reduceIte, Option.some.injEq] at h; subst h
    rw [beq_iff_eq.1 cd1]
    exact ⟨haFlt, by rw [haEv, BitVec.mul_one]⟩
  simp only [cd1, Bool.false_eq_true, ↓reduceIte] at h
  by_cases c1 : (fkey64Beq (resolveKey m arg).base (.imm 0#64) &&
      (resolveKey m arg).scale == 0#64) = true
  · simp only [c1, ↓reduceIte, Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, fkey64Beq_iff_eq, beq_iff_eq] at c1
    have ha : (resolveKey m arg).off = arg.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, c1.1, c1.2, FKey.fev] using haEv
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    simp only [AddrKey.eval, AddrKey.baseEval, AddrKey.const, IdxKey.eval]
    rw [show FKey.fev ρ (Arg.imm 0#64 : FKey i64) = 0#64 from rfl, BitVec.zero_mul,
      BitVec.add_zero, BitVec.zero_add, ha]
  simp only [c1, Bool.false_eq_true, ↓reduceIte] at h
  by_cases c2 : fkey64Beq (resolveKey m arg).base (.imm 0#64) = true
  · simp only [c2, ↓reduceIte, Option.some.injEq] at h; subst h
    have hb : (resolveKey m arg).base = .imm 0#64 := fkey64Beq_iff_eq.1 c2
    have ha : (resolveKey m arg).idx.eval ρ * (resolveKey m arg).scale +
        (resolveKey m arg).off = arg.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, hb, FKey.fev] using haEv
    refine ⟨⟨trivial, haFlt.2⟩, ?_⟩
    simp only [AddrKey.eval, AddrKey.baseEval]
    rw [show FKey.fev ρ (Arg.imm 0#64 : FKey i64) = 0#64 from rfl, BitVec.zero_add,
      ← BitVec.mul_assoc, ← BitVec.add_mul, ha]
  simp only [c2, Bool.false_eq_true, ↓reduceIte] at h
  by_cases c3 : ((resolveKey m arg).scale == 0#64) = true
  · simp only [c3, ↓reduceIte, Option.some.injEq] at h; subst h
    have hs : (resolveKey m arg).scale = 0#64 := beq_iff_eq.1 c3
    have ha : (resolveKey m arg).base.fev ρ + (resolveKey m arg).off = arg.fev ρ := by
      simpa [AddrKey.eval, AddrKey.baseEval, hs] using haEv
    obtain ⟨hiFlt, hiEv⟩ := resolveIdx_good hm haFlt.1
    refine ⟨⟨trivial, hiFlt⟩, ?_⟩
    simp only [AddrKey.eval, AddrKey.baseEval, hiEv]
    rw [show FKey.fev ρ (Arg.imm 0#64 : FKey i64) = 0#64 from rfl, BitVec.zero_add,
      ← BitVec.add_mul, ha]
  · simp only [c3, Bool.false_eq_true, ↓reduceIte] at h; cases h

theorem BaseOffGood.insertAddrOpt {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) (v : Val i64) {o : Option AddrKey}
    (ho : ∀ ak, o = some ak → ak.FLt next ∧ ak.eval ρ = v) :
    BaseOffGood (fupd ρ next v) (next + 1) (insertAddrOpt next m o) := by
  cases o with
  | none => exact hm.upd_fupd v
  | some ak =>
    obtain ⟨hflt, hev⟩ := ho ak rfl
    exact hm.insert_next v hflt.mono ((AddrKey.eval_fupd v hflt).trans hev)
      (Nat.lt_succ_self next) (fupd_eq ρ next v)

private theorem bv64_shiftLeft_eq_mul_twoPow (x d : BitVec 64) :
    x <<< (d.toNat % 64) = x * BitVec.twoPow 64 (d.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  have hs : d.toNat % 64 < 64 := Nat.mod_lt _ (by omega)
  have hpow : 2 ^ (d.toNat % 64) < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hs
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_twoPow, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hpow]

/-- Evaluate a tuple of `FKey`s under valuation `ρ`. -/
def tupFev (ρ : FEnv) : {ts : List Ty} → Tup FKey ts → Tup Val ts
  | [], () => ()
  | _ :: _, (a, as) => (a.fev ρ, tupFev ρ as)

/-- Every `FKey` in a tuple has variable levels `< next`. -/
def TupFLt (next : Nat) : {ts : List Ty} → Tup FKey ts → Prop
  | [], () => True
  | _ :: _, (a, as) => a.FLt next ∧ TupFLt next as

theorem stepBaseOff_add64 (next : Nat) (m : BaseOffMap) (x y : FKey i64) :
    stepBaseOff next m (.add i64) (x, y, ()) = insertAddrOpt next m (addAddr m x y) := by
  simp [stepBaseOff, stepBaseOff2]

theorem stepBaseOff_sub64 (next : Nat) (m : BaseOffMap) (x y : FKey i64) :
    stepBaseOff next m (.sub i64) (x, y, ()) = insertAddrOpt next m (subAddr m x y) := by
  simp [stepBaseOff, stepBaseOff2]

theorem stepBaseOff_mul64_r (next : Nat) (m : BaseOffMap) (x : FKey i64) (d : BitVec 64) :
    stepBaseOff next m (.mul i64) (x, .imm d, ()) =
      insertAddrOpt next m (scaleAddr m x d) := by
  simp [stepBaseOff, stepBaseOff2]

theorem stepBaseOff_mul64_l (next : Nat) (m : BaseOffMap) (d : BitVec 64) (v : Nat) :
    stepBaseOff next m (.mul i64) (.imm d, .var v, ()) =
      insertAddrOpt next m (scaleAddr m (.var v) d) := by
  simp [stepBaseOff, stepBaseOff2]

theorem stepBaseOff_mul64_vv (next : Nat) (m : BaseOffMap) (v₁ v₂ : Nat) :
    stepBaseOff next m (.mul i64) (.var v₁, .var v₂, ()) = m := by
  simp [stepBaseOff, stepBaseOff2, insertAddrOpt]

theorem stepBaseOff_shl64_imm (next : Nat) (m : BaseOffMap) (x : FKey i64) (d : BitVec 64) :
    stepBaseOff next m (.shl i64) (x, .imm d, ()) =
      insertAddrOpt next m (scaleAddr m x (BitVec.twoPow 64 (d.toNat % 64))) := by
  simp [stepBaseOff, stepBaseOff2]

theorem stepBaseOff_shl64_var (next : Nat) (m : BaseOffMap) (x : FKey i64) (v : Nat) :
    stepBaseOff next m (.shl i64) (x, .var v, ()) = m := by
  simp [stepBaseOff, stepBaseOff2]

theorem stepBaseOff_copy64 (next : Nat) (m : BaseOffMap) (x : FKey i64) :
    stepBaseOff next m (.copy i64) (x, ()) = m.insert next (resolveEntry m x) := by
  simp [stepBaseOff]

theorem stepBaseOff_zext32_64 (next : Nat) (m : BaseOffMap) (x : FKey (.bits 32)) :
    stepBaseOff next m (.zext 32 64) (x, ()) = m.insert next ⟨.var next, .zext32 x⟩ := by
  simp [stepBaseOff]

theorem stepBaseOff_sext32_64 (next : Nat) (m : BaseOffMap) (x : FKey (.bits 32)) :
    stepBaseOff next m (.sext 32 64) (x, ()) = m.insert next ⟨.var next, .sext32 x⟩ := by
  simp [stepBaseOff]

theorem BaseOffGood.stepBaseOff_same {ρ : FEnv} {next : Nat} {m : BaseOffMap}
    (hm : BaseOffGood ρ next m) {sig ts : List Ty} (code : OpCode sig ts)
    (kargs : Tup FKey sig) (heq : stepBaseOff next m code kargs = m)
    (args₂ : Tup (Arg Val) sig) (P : Tup Val ts → Prop) (hw : code.wp (vals args₂) P) :
    code.wp (vals args₂) (fun xs =>
      P xs ∧
      BaseOffGood (fupdTup ρ next xs) (next + ts.length) (stepBaseOff next m code kargs)) := by
  rw [heq]
  exact OpCode.wp_mono _ _ (fun xs h => ⟨h, hm.upd_fupdTup xs⟩) hw

theorem stepBaseOff2_ne (next : Nat) (m : BaseOffMap) (code : OpCode [i64, i64] [i64])
    (h1 : code ≠ .add i64) (h2 : code ≠ .sub i64)
    (h3 : code ≠ .mul i64) (h4 : code ≠ .shl i64) (x y : FKey i64) :
    stepBaseOff2 next m code x y = m := by
  simp [stepBaseOff2, h1, h2, h3, h4]

theorem stepBaseOff_good (ρ : FEnv) (next : Nat) (m : BaseOffMap)
    (hm : BaseOffGood ρ next m) {sig ts : List Ty} (code : OpCode sig ts)
    (kargs : Tup FKey sig) (hklt : TupFLt next kargs)
    (args₂ : Tup (Arg Val) sig) (hvals : tupFev ρ kargs = vals args₂)
    (P : Tup Val ts → Prop) (hw : code.wp (vals args₂) P) :
    code.wp (vals args₂) (fun xs =>
      P xs ∧
      BaseOffGood (fupdTup ρ next xs) (next + ts.length) (stepBaseOff next m code kargs)) := by
  by_cases h2 : sig = [i64, i64] ∧ ts = [i64]
  · rcases h2 with ⟨rfl, rfl⟩
    rcases kargs with ⟨x, y, ⟨⟩⟩; rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
    rcases hklt with ⟨hx, hy, _⟩
    dsimp only [tupFev, vals] at hvals; simp only [Prod.mk.injEq] at hvals
    rcases hvals with ⟨hxa, hyb, _⟩
    by_cases hadd : code = .add i64
    · subst hadd
      simp only [OpCode.wp_add, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, vals] at hw ⊢
      refine ⟨hw, ?_⟩
      rw [stepBaseOff_add64]
      simpa [fupdTup] using hm.insertAddrOpt (a₂.val + b₂.val) fun ak hak => by
        obtain ⟨h1, h2⟩ := addAddr_good hm hx hy hak; exact ⟨h1, by rw [h2, hxa, hyb]⟩
    · by_cases hsub : code = .sub i64
      · subst hsub
        simp only [OpCode.wp_sub, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2,
          vals] at hw ⊢
        refine ⟨hw, ?_⟩
        rw [stepBaseOff_sub64]
        simpa [fupdTup] using hm.insertAddrOpt (a₂.val - b₂.val) fun ak hak => by
          obtain ⟨h1, h2⟩ := subAddr_good hm hx hy hak; exact ⟨h1, by rw [h2, hxa, hyb]⟩
      · by_cases hmul : code = .mul i64
        · subst hmul
          simp only [OpCode.wp_mul, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2,
            vals] at hw ⊢
          refine ⟨hw, ?_⟩
          cases y with
          | imm d =>
            rw [stepBaseOff_mul64_r]
            simpa [fupdTup] using hm.insertAddrOpt (a₂.val * b₂.val) fun ak hak => by
              obtain ⟨h1, h2⟩ := scaleAddr_good hm hx d hak
              exact ⟨h1, by rw [h2, hxa, ← hyb]; rfl⟩
          | var v =>
            cases x with
            | imm d =>
              rw [stepBaseOff_mul64_l]
              simpa [fupdTup] using hm.insertAddrOpt (a₂.val * b₂.val) fun ak hak => by
                obtain ⟨h1, h2⟩ := scaleAddr_good hm hy d hak
                exact ⟨h1, by rw [h2, hyb, ← hxa]; exact BitVec.mul_comm _ _⟩
            | var v' =>
              rw [stepBaseOff_mul64_vv]
              simpa [fupdTup] using hm.upd_fupd (a₂.val * b₂.val)
        · by_cases hshl : code = .shl i64
          · subst hshl
            simp only [OpCode.wp_shl, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2,
              vals] at hw ⊢
            refine ⟨hw, ?_⟩
            cases y with
            | imm d =>
              rw [stepBaseOff_shl64_imm]
              simpa [fupdTup] using
                hm.insertAddrOpt (a₂.val <<< (b₂.val.toNat % 64)) fun ak hak => by
                  obtain ⟨h1, h2⟩ := scaleAddr_good hm hx (BitVec.twoPow 64 (d.toNat % 64)) hak
                  exact ⟨h1, by rw [h2, hxa, bv64_shiftLeft_eq_mul_twoPow, ← hyb]; rfl⟩
            | var _ =>
              rw [stepBaseOff_shl64_var]
              simpa [fupdTup] using hm.upd_fupd _
          · exact hm.stepBaseOff_same code _ (by
              simp [stepBaseOff, stepBaseOff2_ne next m code hadd hsub hmul hshl])
              (a₂, b₂, ()) P hw
  · by_cases h1 : sig = [i64] ∧ ts = [i64]
    · rcases h1 with ⟨rfl, rfl⟩
      rcases kargs with ⟨x, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
      rcases hklt with ⟨hx, _⟩
      dsimp only [tupFev, vals] at hvals; simp only [Prod.mk.injEq] at hvals
      by_cases hcopy : code = .copy i64
      · subst hcopy
        obtain ⟨hakFlt, hakEv, hiFlt, hiEv⟩ := resolveEntry_good hm hx
        dsimp only [vals] at hw ⊢; simp only [OpCode.wp_copy] at hw ⊢
        rw [stepBaseOff_copy64]
        exact ⟨hw, hm.insert_old _ hakFlt (hakEv.trans hvals.1) hiFlt (hiEv.trans hvals.1)⟩
      · exact hm.stepBaseOff_same code _ (by simp [stepBaseOff, hcopy]) (a₂, ()) P hw
    · by_cases h32 : sig = [.bits 32] ∧ ts = [i64]
      · rcases h32 with ⟨rfl, rfl⟩
        rcases kargs with ⟨x, ⟨⟩⟩; rcases args₂ with ⟨a₂, ⟨⟩⟩
        rcases hklt with ⟨hx, _⟩
        dsimp only [tupFev, vals] at hvals; simp only [Prod.mk.injEq] at hvals
        by_cases hz : code = .zext 32 64
        · subst hz
          dsimp only [vals] at hw ⊢; simp only [OpCode.wp_zext] at hw ⊢
          refine ⟨hw.1, hw.2, ?_⟩
          rw [stepBaseOff_zext32_64]
          refine hm.insert_next _ ⟨Nat.lt_succ_self next, trivial⟩ ?_ hx.mono ?_
          · simp [AddrKey.eval, AddrKey.baseEval, AddrKey.var, IdxKey.eval, FKey.fev, fupd_eq]
          · simp [IdxKey.eval, FKey.fev_fupd _ hx, hvals.1]
        · by_cases hsx : code = .sext 32 64
          · subst hsx
            dsimp only [vals] at hw ⊢; simp only [OpCode.wp_sext] at hw ⊢
            refine ⟨hw.1, hw.2, ?_⟩
            rw [stepBaseOff_sext32_64]
            refine hm.insert_next _ ⟨Nat.lt_succ_self next, trivial⟩ ?_ hx.mono ?_
            · simp [AddrKey.eval, AddrKey.baseEval, AddrKey.var, IdxKey.eval, FKey.fev, fupd_eq]
            · simp [IdxKey.eval, FKey.fev_fupd _ hx, hvals.1]
          · exact hm.stepBaseOff_same code _ (by simp [stepBaseOff, hz, hsx]) (a₂, ()) P hw
      · have heq : stepBaseOff next m code kargs = m := by
          dsimp only [stepBaseOff]
          split
          · split
            · rename_i hs ht; exact absurd ⟨hs, ht⟩ h2
            · rfl
          · split
            · split
              · rename_i _ hs ht; exact absurd ⟨hs, ht⟩ h1
              · rfl
            · split
              · split
                · rename_i _ _ hs ht; exact absurd ⟨hs, ht⟩ h32
                · rfl
              · rfl
        exact hm.stepBaseOff_same code kargs heq args₂ P hw

/-! ## Context invariants (`KGood`, `MGood`), cache invariants, and group summaries -/

/-- `K`-context agreement with valuation `ρ` below `next`. -/
public def KGood (ρ : FEnv) (next : Nat) (Gk : Ctx K Val) : Prop :=
  ∀ p ∈ Gk, p.2.1 < next ∧ ρ p.1 p.2.1 = p.2.2

theorem KGood.cons {ρ : FEnv} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {t : Ty} (v : Val t) :
    KGood (fupd ρ next v) (next + 1) (⟨t, next, v⟩ :: Gk) := by
  intro p hp
  cases hp with
  | head => exact ⟨Nat.lt_succ_self _, fupd_eq ρ next v⟩
  | tail _ hp =>
    obtain ⟨hlt, heq⟩ := hG p hp
    exact ⟨Nat.lt_succ_of_lt hlt, (fupd_ne ρ v (Nat.ne_of_lt hlt)).trans heq⟩

private theorem KGood.tup_levels_only (ρ : FEnv) :
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

theorem KGood.upd_all {ρ : FEnv} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {ts : List Ty} (xs : Tup Val ts) :
    KGood (fupdTup ρ next xs) (next + ts.length) Gk := by
  intro p hp
  obtain ⟨hlt, heq⟩ := hG p hp
  exact ⟨Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _), (fupdTup_lt ρ xs hlt).trans heq⟩

theorem KGood.freshTup {ρ : FEnv} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {ts : List Ty} (xs : Tup Val ts) :
    KGood (fupdTup ρ next xs) (next + ts.length) (Tup.zip (Tup.levels ts next) xs ++ Gk) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact KGood.tup_levels_only ρ xs next p hp
  · exact hG.upd_all xs p hp

theorem ArgRel.k_lt {ρ : FEnv} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {t : Ty} {ak : Arg K t} {a₂ : Arg Val t}
    (h : ArgRel Gk t ak a₂) : FKey.FLt next ak := by
  cases h with
  | var hm => exact (hG _ hm).1
  | imm _ => trivial

theorem ArgRel.k_ev {ρ : FEnv} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) {t : Ty} {ak : Arg K t} {a₂ : Arg Val t}
    (h : ArgRel Gk t ak a₂) : FKey.fev ρ ak = a₂.val := by
  cases h with
  | var hm => exact (hG _ hm).2
  | imm _ => rfl

theorem TRel.k_lt {ρ : FEnv} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) :
    {ts : List Ty} → {aks : Tup FKey ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₂ → TupFLt next aks
  | [], (), (), .nil => trivial
  | _ :: _, (_, _), (_, _), .cons h hs => ⟨ArgRel.k_lt hG h, TRel.k_lt hG hs⟩

theorem TRel.k_vals {ρ : FEnv} {next : Nat} {Gk : Ctx K Val}
    (hG : KGood ρ next Gk) :
    {ts : List Ty} → {aks : Tup FKey ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₂ → tupFev ρ aks = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (ArgRel.k_ev hG h) (TRel.k_vals hG hs)

/-- `MVal`-context agreement with valuation `ρ` below `next`. -/
public def MGood (ρ : FEnv) (next : Nat) (G : Ctx (MVal Val) Val) : Prop :=
  ∀ p ∈ G, p.2.1.out.val = p.2.2 ∧ p.2.1.key.FLt next ∧ p.2.1.key.fev ρ = p.2.2

theorem MGood.upd_all {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {ts : List Ty} (xs : Tup Val ts) :
    MGood (fupdTup ρ next xs) (next + ts.length) G := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hG p hp
  exact ⟨h1, h2.add, (FKey.fev_fupdTup xs h2).trans h3⟩

theorem MGood.cons_fupd {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} {mv : MVal Val t} {v : Val t}
    (h1 : mv.out.val = v) (h2 : mv.key.FLt (next + 1)) (h3 : mv.key.fev (fupd ρ next v) = v) :
    MGood (fupd ρ next v) (next + 1) (⟨t, mv, v⟩ :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨h1, h2, h3⟩
  | tail _ hp =>
    obtain ⟨ha, hb, hc⟩ := hG p hp
    exact ⟨ha, hb.mono, (FKey.fev_fupd v hb).trans hc⟩

theorem MGood.cons_fresh {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} (v : Val t) :
    MGood (fupd ρ next v) (next + 1) (⟨t, MVal.fresh v next, v⟩ :: G) :=
  hG.cons_fupd rfl (Nat.lt_succ_self next) (fupd_eq ρ next v)

private theorem MGood.freshMVals_only (ρ : FEnv) :
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

theorem MGood.freshMVals {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {ts : List Ty} (xs : Tup Val ts) :
    MGood (fupdTup ρ next xs) (next + ts.length)
      (Tup.zip (freshMVals ts xs next) xs ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact MGood.freshMVals_only ρ xs next p hp
  · exact hG.upd_all xs p hp

theorem ArgRel.mout_val {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} {a₁ : Arg (MVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.mout.val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem ArgRel.mkey_lt {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} {a₁ : Arg (MVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.mkey.FLt next
  | .var h => (hG _ h).2.1
  | .imm _ => trivial

theorem ArgRel.mkey_ev {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {t : Ty} {a₁ : Arg (MVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.mkey.fev ρ = a₂.val
  | .var h => (hG _ h).2.2
  | .imm _ => rfl

theorem TRel.mout_vals {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) {ts : List Ty} {as₁ : Tup (Arg (MVal Val)) ts} {as₂ : Tup (Arg Val) ts}
    (h : TRel (ArgRel G) as₁ as₂) : vals (tupMOut as₁) = vals as₂ :=
  TRel.tupMapArg_vals (fun _ => Arg.mout) (fun ha => ha.mout_val hG) h

theorem TRel.mkey_lt {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) :
    {ts : List Ty} → {as₁ : Tup (Arg (MVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → TupFLt next (tupMKey as₁)
  | [], (), (), .nil => trivial
  | _ :: _, (_, _), (_, _), .cons h hs => ⟨h.mkey_lt hG, TRel.mkey_lt hG hs⟩

theorem TRel.mkey_vals {ρ : FEnv} {next : Nat} {G : Ctx (MVal Val) Val}
    (hG : MGood ρ next G) :
    {ts : List Ty} → {as₁ : Tup (Arg (MVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → tupFev ρ (tupMKey as₁) = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (h.mkey_ev hG) (TRel.mkey_vals hG hs)

/-- Semantic agreement of a dominating cache entry with valuation `ρ` and memory `m`. -/
public def MemEntryGood (ρ : FEnv) (next : Nat) (e : CacheEntry Val) (m : Mem 64) : Prop :=
  e.ak.FLt next ∧ e.valKey.FLt next ∧ e.valKey.fev ρ = e.val.val ∧
    loadVal m e.ty (e.ak.eval ρ) = some e.val.val

/-- Dominating cache invariant: every cached entry agrees with `ρ` and `m`. -/
public def MemCacheGood (ρ : FEnv) (next : Nat) (cache : List (CacheEntry Val))
    (m : Mem 64) : Prop :=
  ∀ e ∈ cache, MemEntryGood ρ next e m

/-- Static invariant entry captured at `.group` entry (`addr` is fixed across inner binders). -/
public structure InvEntry : Type where
  ak : AddrKey
  addr : BitVec 64
  ty : Ty
  val : Val ty

/-- Memory-only agreement for group invariant entries (independent of `ρ` and `next`). -/
public def InvMemGood (inv : List InvEntry) (m : Mem 64) : Prop :=
  ∀ e ∈ inv, loadVal m e.ty e.addr = some e.val

/-- Static address-key agreement for group invariant entries below `next`. -/
public def InvKeysGood (ρ : FEnv) (next : Nat) (inv : List InvEntry) : Prop :=
  ∀ e ∈ inv, e.ak.FLt next ∧ e.ak.eval ρ = e.addr

/-- Combined semantic invariant `MemLoadGood` pairing dominating cache and enclosing group frame. -/
public def MemLoadGood (ρ : FEnv) (next : Nat)
    (cache : List (CacheEntry Val)) (inv : List InvEntry) (m : Mem 64) : Prop :=
  MemCacheGood ρ next cache m ∧ InvMemGood inv m ∧ InvKeysGood ρ next inv

private theorem MemLoadGood.empty (ρ : FEnv) (next : Nat) (m : Mem 64) :
    MemLoadGood ρ next [] [] m :=
  ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h)⟩

/-- Summary preservation condition: `s` has no `.call` (`≠ .unknown`) and every write span in `s`
is provably disjoint from every entry in `inv`. -/
public def SummaryPreserves (s : MemSummary) (inv : List InvEntry) : Prop :=
  ∀ e ∈ inv, match s with
    | .unknown => False
    | .exact ws => ∀ w ∈ ws, e.ak.sameBase w.ak = true ∧
        spanDisjoint w.ak.off w.bytes e.ak.off e.ty.bytes = true

/-- Label carrying a unique de Bruijn level alongside its `Cont` continuation. -/
public abbrev LCont : List Ty → Type := fun ts => Nat × Cont ts

/-- Tag a continuation tuple with consecutive de Bruijn levels starting at `nl`. -/
def tagConts (nl : Nat) : {sig : List (List Ty)} → Tup Cont sig → Tup LCont sig
  | [], () => ()
  | _ :: _, (J, Js) => ((nl, J), tagConts (nl + 1) Js)

/-- Context invariant linking `K`-level labels `KL` to `LCont`. -/
public def KLGood (nl : Nat) (Dk : Ctx KL LCont) : Prop :=
  ∀ p ∈ Dk, p.2.1 = p.2.2.1 ∧ p.2.2.1 < nl

/-- Context invariant linking `Val` identically between `eL` and `e₂`. -/
public def EqG (G₂ : Ctx Val Val) : Prop :=
  ∀ p ∈ G₂, p.2.1 = p.2.2

/-- Context invariant linking `Cont` to `LCont` between `e₂` and `eL`. -/
public def EqD (D₂ : Ctx Cont LCont) : Prop :=
  ∀ p ∈ D₂, p.2.1 = p.2.2.2

/-- Label invariant guarded by live jump-target set `l` and memory frame `inv`. -/
public def MemDGood (inv : List InvEntry) (l : Trie Unit) (D : Ctx Cont LCont) : Prop :=
  ∀ p ∈ D, (l.find? p.2.2.1).isSome = true →
    ∀ xs m, InvMemGood inv m → p.2.2.2 xs m → p.2.1 xs m

theorem MemCacheGood.upd_one {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {u : Ty} (v : Val u) :
    MemCacheGood (fupd ρ next v) (next + 1) cache m := by
  intro e he
  obtain ⟨hak, hv, hev, hld⟩ := hc e he
  refine ⟨hak.mono, hv.mono, ?_, ?_⟩
  · rw [FKey.fev_fupd v hv]; exact hev
  · rw [AddrKey.eval_fupd v hak]; exact hld

theorem MemCacheGood.upd_fupdTup {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {ts : List Ty} (xs : Tup Val ts) :
    MemCacheGood (fupdTup ρ next xs) (next + ts.length) cache m := by
  intro e he
  obtain ⟨hak, hv, hev, hld⟩ := hc e he
  refine ⟨hak.add, hv.add, ?_, ?_⟩
  · rw [FKey.fev_fupdTup xs hv]; exact hev
  · rw [AddrKey.eval_fupdTup xs hak]; exact hld

theorem InvKeysGood.upd_one {ρ : FEnv} {next : Nat} {inv : List InvEntry}
    (hi : InvKeysGood ρ next inv) {u : Ty} (v : Val u) :
    InvKeysGood (fupd ρ next v) (next + 1) inv := by
  intro e he
  obtain ⟨hak, heq⟩ := hi e he
  exact ⟨hak.mono, (AddrKey.eval_fupd v hak).trans heq⟩

theorem InvKeysGood.upd_fupdTup {ρ : FEnv} {next : Nat} {inv : List InvEntry}
    (hi : InvKeysGood ρ next inv) {ts : List Ty} (xs : Tup Val ts) :
    InvKeysGood (fupdTup ρ next xs) (next + ts.length) inv := by
  intro e he
  obtain ⟨hak, heq⟩ := hi e he
  exact ⟨hak.add, (AddrKey.eval_fupdTup xs hak).trans heq⟩

theorem MemCacheGood.store_filter {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) (akW : AddrKey)
    (t : Ty) (ptr : BitVec 64) (v : Val t) (hptr : akW.eval ρ = ptr) :
    MemCacheGood ρ next (filterCacheWrite akW t.bytes cache) (storeMem m t ptr v) := by
  intro e he
  simp only [filterCacheWrite, List.mem_filter, entryDisjointWrite, Bool.and_eq_true] at he
  obtain ⟨hem, hsb, hsp⟩ := he
  obtain ⟨hakflt, hvflt, hev, hld⟩ := hc e hem
  refine ⟨hakflt, hvflt, hev, ?_⟩
  have hbase : e.ak.baseEval ρ = akW.baseEval ρ := AddrKey.baseEval_eq_of_sameBase ρ hsb
  have hdisj := spanDisjoint_sound hsp (akW.baseEval ρ)
  have heW : akW.baseEval ρ + akW.off = ptr := hptr
  have heE : akW.baseEval ρ + e.ak.off = e.ak.eval ρ := by
    simp only [AddrKey.eval, hbase]
  rw [← heW, ← heE,
    loadVal_storeMem_disjoint m t e.ty (akW.baseEval ρ + akW.off) (akW.baseEval ρ + e.ak.off)
      v hdisj]
  rw [heE]
  exact hld

theorem MemCacheGood.store_push {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {akW : AddrKey} {t : Ty}
    {vout : Arg Val t} {vkey : FKey t} {ptr : BitVec 64} {v : Val t}
    (hakflt : akW.FLt next) (hvflt : vkey.FLt next) (hev : vkey.fev ρ = vout.val)
    (hv : vout.val = v) (hptr : akW.eval ρ = ptr) (hbytes : t.bytes ≤ 2 ^ 64) :
    MemCacheGood ρ next
      (⟨akW, t, vout, vkey⟩ :: filterCacheWrite akW t.bytes cache)
      (storeMem m t ptr v) := by
  intro e he
  cases he with
  | head =>
    refine ⟨hakflt, hvflt, hev, ?_⟩
    rw [hptr, hv]
    exact loadVal_storeMem m t ptr v hbytes
  | tail _ he => exact hc.store_filter akW t ptr v hptr e he

theorem MemCacheGood.cons_load {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {ak : AddrKey} {t : Ty}
    {v : Val t} (hakflt : ak.FLt next) (hld : loadVal m t (ak.eval ρ) = some v) :
    MemCacheGood (fupd ρ next v) (next + 1)
      (⟨ak, t, .var v, .var next⟩ :: cache) m := by
  intro e he
  cases he with
  | head =>
    refine ⟨hakflt.mono, Nat.lt_succ_self _, fupd_eq ρ next v, ?_⟩
    rw [AddrKey.eval_fupd v hakflt]
    exact hld
  | tail _ he => exact hc.upd_one v e he

theorem lookupCache_mem {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) {ak : AddrKey} {t : Ty}
    {mv : MVal Val t} (hl : lookupCache ak t cache = some mv) :
    mv.key.FLt next ∧ mv.key.fev ρ = mv.out.val ∧
      loadVal m t (ak.eval ρ) = some mv.out.val := by
  induction cache with
  | nil => cases hl
  | cons e rest ih =>
    dsimp only [lookupCache] at hl
    cases hbo : e.ak.beq ak
    · rw [hbo] at hl
      exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) hl
    · rw [hbo] at hl
      cases hty : tyDecEq e.ty t with
      | isFalse _ =>
        rw [hty] at hl
        exact ih (fun x hx => hc x (List.mem_cons_of_mem _ hx)) hl
      | isTrue heq =>
        rw [hty] at hl
        cases hl
        subst heq
        obtain ⟨_, hvflt, hvev, hld⟩ := hc e List.mem_cons_self
        have hak : e.ak = ak := AddrKey.beq_iff.1 hbo
        rw [hak] at hld
        exact ⟨hvflt, hvev, hld⟩

/-- Snapshot a cache into static `InvEntry`s evaluated under `ρ`. -/
def cacheToInv (ρ : FEnv) (cache : List (CacheEntry Val)) : List InvEntry :=
  cache.map fun e => ⟨e.ak, e.ak.eval ρ, e.ty, e.val.val⟩

theorem MemCacheGood.filterSummary {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) (s : MemSummary) :
    MemCacheGood ρ next (filterCacheSummary s cache) m :=
  fun e he => hc e (List.mem_filter.1 he).1

theorem InvMemGood.of_cache {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) : InvMemGood (cacheToInv ρ cache) m := by
  intro e he
  dsimp only [cacheToInv] at he; simp only [List.mem_map] at he
  rcases he with ⟨ce, hce, rfl⟩
  exact (hc ce hce).2.2.2

theorem InvKeysGood.of_cache {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m : Mem 64}
    (hc : MemCacheGood ρ next cache m) : InvKeysGood ρ next (cacheToInv ρ cache) := by
  intro e he
  dsimp only [cacheToInv] at he; simp only [List.mem_map] at he
  rcases he with ⟨ce, hce, rfl⟩
  exact ⟨(hc ce hce).1, rfl⟩

theorem MemCacheGood.of_inv {ρ : FEnv} {next : Nat}
    {cache : List (CacheEntry Val)} {m m' : Mem 64}
    (hc : MemCacheGood ρ next cache m)
    (hi : InvMemGood (cacheToInv ρ cache) m') : MemCacheGood ρ next cache m' := by
  intro e he
  obtain ⟨hb, hv, hev, _⟩ := hc e he
  refine ⟨hb, hv, hev, ?_⟩
  exact hi ⟨e.ak, e.ak.eval ρ, e.ty, e.val.val⟩ (List.mem_map.2 ⟨e, he, rfl⟩)

theorem InvMemGood.append {inv₁ inv₂ : List InvEntry} {m : Mem 64} :
    InvMemGood inv₁ m → InvMemGood inv₂ m → InvMemGood (inv₁ ++ inv₂) m :=
  fun h1 h2 e he => (List.mem_append.1 he).elim (h1 e) (h2 e)

theorem InvKeysGood.append {ρ : FEnv} {next : Nat} {inv₁ inv₂ : List InvEntry} :
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
      (∀ e ∈ inv, e.ak.sameBase w.ak = true ∧
        spanDisjoint w.ak.off w.bytes e.ak.off e.ty.bytes = true) ∧
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

theorem SummaryPreserves.filterSummary (ρ : FEnv)
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

theorem InvMemGood.store_disjoint {ρ : FEnv} {next : Nat}
    {inv : List InvEntry} {m : Mem 64}
    (hk : InvKeysGood ρ next inv) (hm : InvMemGood inv m)
    {akW : AddrKey} {t : Ty} {ptr : BitVec 64} (v : Val t)
    (hptr : akW.eval ρ = ptr)
    (hdisj : ∀ e ∈ inv, e.ak.sameBase akW = true ∧
      spanDisjoint akW.off t.bytes e.ak.off e.ty.bytes = true) :
    InvMemGood inv (storeMem m t ptr v) := by
  intro e he
  obtain ⟨_, heq⟩ := hk e he
  obtain ⟨hsb, hsp⟩ := hdisj e he
  have hbase : e.ak.baseEval ρ = akW.baseEval ρ := AddrKey.baseEval_eq_of_sameBase ρ hsb
  have hsd := spanDisjoint_sound hsp (akW.baseEval ρ)
  have heW : akW.baseEval ρ + akW.off = ptr := hptr
  have heE : akW.baseEval ρ + e.ak.off = e.addr := by
    rw [← heq]; simp only [AddrKey.eval, hbase]
  rw [← heW, ← heE,
    loadVal_storeMem_disjoint m t e.ty (akW.baseEval ρ + akW.off) (akW.baseEval ρ + e.ak.off)
      v hsd]
  rw [heE]
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

theorem KLGood.append_levels {nl : Nat} {Dk : Ctx KL LCont} (hKL : KLGood nl Dk) :
    {sig : List (List Ty)} → (Js : Tup Cont sig) →
    KLGood (nl + sig.length) (Tup.zip (Tup.levels sig nl) (tagConts nl Js) ++ Dk)
  | [], () => hKL
  | _ :: sig, (J, Js) => by
    simp only [Tup.levels, tagConts, Tup.zip, List.length_cons]
    intro p hp
    cases hp with
    | head => exact ⟨rfl, Nat.lt_add_of_pos_right (Nat.succ_pos _)⟩
    | tail _ hp =>
      have ih := KLGood.append_levels (nl := nl + 1) (Dk := Dk)
        (fun q hq => ⟨(hKL q hq).1, Nat.lt_succ_of_lt (hKL q hq).2⟩) Js p hp
      rw [show nl + 1 + sig.length = nl + (sig.length + 1) by omega] at ih
      exact ih

theorem EqG.freshTup {G₂ : Ctx Val Val} (hG : EqG G₂) :
    {ts : List Ty} → (xs : Tup Val ts) → EqG (Tup.zip xs xs ++ G₂)
  | [], () => hG
  | _ :: _, (x, xs) => fun p hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact EqG.freshTup hG xs p hp

theorem EqG.cons {G₂ : Ctx Val Val} (hG : EqG G₂) {t : Ty} (v : Val t) :
    EqG (⟨t, v, v⟩ :: G₂)
  | _, .head _ => rfl
  | _, .tail _ hp => hG _ hp

theorem EqG.vals_eq {G₂ : Ctx Val Val} (hG : EqG G₂) {t : Ty}
    {a₁ a₂ : Arg Val t} : ArgRel G₂ t a₁ a₂ → a₁.val = a₂.val
  | .var hm => hG _ hm
  | .imm _ => rfl

theorem EqG.trel_vals_eq {G₂ : Ctx Val Val} (hG : EqG G₂) :
    {ts : List Ty} → {as₁ as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G₂) as₁ as₂ → vals as₁ = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (hG.vals_eq h) (hG.trel_vals_eq hs)

theorem EqG.op_eq {G₂ : Ctx Val Val} (hG : EqG G₂) {rs : List Ty}
    {op₁ op₂ : Op Val rs} : OpRel G₂ op₁ op₂ → Op.wp op₁ = Op.wp op₂
  | .mk code hargs => by
    funext post
    simp only [Op.wp, hG.trel_vals_eq hargs]

theorem EqD.append_tag {D₂ : Ctx Cont LCont} (hD : EqD D₂) :
    {sig : List (List Ty)} → (nl : Nat) → (Js : Tup Cont sig) →
    EqD (Tup.zip Js (tagConts nl Js) ++ D₂)
  | [], _, () => hD
  | _ :: _, nl, (_, Js) => fun p hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact EqD.append_tag hD (nl + 1) Js p hp

theorem mem_zip_tagConts_bounds :
    {sig : List (List Ty)} → (nl : Nat) → (Js : Tup Cont sig) → (Js' : Tup Cont sig) →
    ∀ p ∈ Tup.zip Js (tagConts nl Js'), nl ≤ p.2.2.1 ∧ p.2.2.1 < nl + sig.length
  | [], _, (), (), _, hp => nomatch hp
  | _ :: sig, nl, (_, Js), (_, Js'), p, hp => by
    cases hp with
    | head => exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right (Nat.succ_pos _)⟩
    | tail _ hp =>
      have ih := mem_zip_tagConts_bounds (nl + 1) Js Js' p hp
      exact ⟨by omega, by simp [List.length_cons]; omega⟩

theorem mem_zip_tagConts_inv (P : Mem 64 → Prop) :
    {sig : List (List Ty)} → (nl : Nat) → (Js : Tup Cont sig) →
    ∀ p ∈ Tup.zip Js (tagConts nl (strengthenJs P Js)),
      ∀ xs m, P m → p.2.2.2 xs m → p.2.1 xs m
  | [], _, (), _, hp => nomatch hp
  | _ :: _, nl, (_, Js), p, hp => by
    cases hp with
    | head => exact fun _ _ hP hJ => hJ hP
    | tail _ hp => exact mem_zip_tagConts_inv P (nl + 1) Js p hp

theorem MemDGood.sub {inv : List InvEntry} {l₁ l₂ : Trie Unit} {D : Ctx Cont LCont}
    (hsub : TrieSub l₁ l₂) (hD : MemDGood inv l₂ D) : MemDGood inv l₁ D :=
  fun p hp hl => hD p hp (hsub p.2.2.1 hl)

theorem MemDGood.weaken_inv {inv₁ inv₂ : List InvEntry} {l : Trie Unit} {D : Ctx Cont LCont}
    (hsub : ∀ e ∈ inv₁, e ∈ inv₂) (hD : MemDGood inv₁ l D) : MemDGood inv₂ l D :=
  fun p hp hl xs m hinv => hD p hp hl xs m (fun e he => hinv e (hsub e he))

theorem MemDGood.append_inv {inv₁ inv₂ : List InvEntry} {l : Trie Unit} {D : Ctx Cont LCont}
    (hD : MemDGood inv₂ l D) : MemDGood (inv₁ ++ inv₂) l D :=
  hD.weaken_inv fun _ h => List.mem_append_right _ h

/-! ## Block access lemmas and `memLoad_wp` -/

theorem analyzeMemB_get_summary {rs : List Ty} (next nl : Nat) (baseOff : BaseOffMap)
    {inv : List InvEntry} :
    {sig : List (List Ty)} → (bs : Blocks K KL rs sig) → {ts : List Ty} → (i : Member ts sig) →
    SummaryPreserves (analyzeMemB next nl baseOff bs).1 inv →
    SummaryPreserves
      (analyzeMem (next + ts.length) nl baseOff (bs.get i (Tup.levels ts next))).1 inv
  | _ :: _, .cons _ _, _, .here, h => (SummaryPreserves.join.1 h).1
  | _ :: _, .cons _ tl, _, .there i, h =>
    analyzeMemB_get_summary next nl baseOff tl i (SummaryPreserves.join.1 h).2

theorem analyzeMemB_get_live_sub {rs : List Ty} (next nl : Nat) (baseOff : BaseOffMap) :
    {sig : List (List Ty)} → (bs : Blocks K KL rs sig) → {ts : List Ty} → (i : Member ts sig) →
    TrieSub (analyzeMem (next + ts.length) nl baseOff (bs.get i (Tup.levels ts next))).2.1
      (analyzeMemB next nl baseOff bs).2.1
  | _ :: _, .cons _ _, _, .here => TrieSub.union_left _ _
  | _ :: _, .cons _ tl, _, .there i =>
    TrieSub.trans (analyzeMemB_get_live_sub next nl baseOff tl i) (TrieSub.union_right _ _)

theorem memLoadSweepB_analyzeMemB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next nl : Nat) (baseOff baseOffK : BaseOffMap) (cache : List (CacheEntry V)) :
    {sig : List (List Ty)} → (bk : Blocks K KL rs sig) → (bs : Blocks (MVal V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (memLoadSweepB next baseOff cache (analyzeMemB next nl baseOffK bk).2.2 bs).get i xs =
      memLoadSweep (next + ts.length) baseOff cache
        (analyzeMem (next + ts.length) nl baseOffK (bk.get i (Tup.levels ts next))).2.2
        (bs.get i (freshMVals ts xs next))
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bkt, .cons _ bst, _, .there i', xs =>
    memLoadSweepB_analyzeMemB_get next nl baseOff baseOffK cache bkt bst i' xs

private theorem memLoadSweep_load' {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (baseOff : BaseOffMap) (cache : List (CacheEntry V)) (mst : MemSumTree)
    (t : Ty) (a : Arg (MVal V) i64) (k : MVal V t → Expr (MVal V) L rs) :
    memLoadSweep next baseOff cache mst (.load t a k) =
      let kt := match mst with | .node1 kt' => kt' | _ => .leaf
      match lookupCache (resolveKey baseOff a.mkey) t cache with
      | some cached => memLoadSweep (next + 1) baseOff cache kt (k cached)
      | none =>
        .load t a.mout fun v =>
          let cache' := ⟨resolveKey baseOff a.mkey, t, .var v, .var next⟩ :: cache
          memLoadSweep (next + 1) baseOff cache' kt (k (MVal.fresh v next)) := by
  delta memLoadSweep; dsimp only [Expr.brecOn, Expr.rec, memLoadSweep._f]
  cases lookupCache (resolveKey baseOff a.mkey) t cache <;> rfl

/-- Weakest-precondition preservation for `memLoadSweep`, proved via `Wf.induct`. -/
public theorem memLoad_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (MVal Val) Val} {D : Ctx Cont LCont}
    {e₁ : Expr (MVal Val) Cont rs} {eL : Expr Val LCont rs}
    (hwf : Wf G D e₁ eL) :
    ∀ {Gk : Ctx K Val} {Dk : Ctx KL LCont} {G₂ : Ctx Val Val} {D₂ : Ctx Cont LCont}
      (next nl : Nat) (ρ : FEnv) (baseOff baseOffK : BaseOffMap)
      (cache : List (CacheEntry Val)) (inv : List InvEntry)
      (ek : Expr K KL rs) (e₂ : Expr Val Cont rs),
      Wf Gk Dk ek eL → Wf G₂ D₂ e₂ eL →
      KGood ρ next Gk → MGood ρ next G → EqG G₂ → EqD D₂ → KLGood nl Dk →
      BaseOffGood ρ next baseOff → BaseOffGood ρ next baseOffK →
      MemDGood inv (analyzeMem next nl baseOffK ek).2.1 D →
      SummaryPreserves (analyzeMem next nl baseOffK ek).1 inv →
      ∀ m, MemLoadGood ρ next cache inv m → wp Γ Q X e₂ m →
        wp Γ Q X (memLoadSweep next baseOff cache (analyzeMem next nl baseOffK ek).2.2 e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ opL k₁ kL hop _ ih =>
    intro Gk Dk G₂ D₂ next nl ρ baseOff baseOffK cache inv ek e₂ hwk hw2
      hGk hG hG2 hD2 hKL hbo hboK hD hsp m hml hw
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    rcases hw2.rhs_let with ⟨op₂, k₂, rfl, hop2, hkk2⟩
    cases hop with
    | @mk sig _ code args₁ argsL hargs =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        dsimp only [analyzeMem, memLoadSweep, wp] at hsp hD hw ⊢
        rw [hG2.op_eq hop2] at hw
        dsimp only [Op.wp] at hw ⊢
        have hw1 := stepBaseOff_good ρ next baseOff hbo code (tupMKey args₁)
          (hargs.mkey_lt hG) argsL (hargs.mkey_vals hG) _ hw
        have hw2 := stepBaseOff_good ρ next baseOffK hboK code argsk
          (hargsk.k_lt hGk) argsL (hargsk.k_vals hGk) _ hw1
        rw [hargs.mout_vals hG]
        refine OpCode.wp_mono code _ (fun xs ⟨⟨hk2, hbo'⟩, hboK'⟩ => ?_) hw2
        refine ih (freshMVals ts xs next) xs (next + ts.length) nl (fupdTup ρ next xs)
          _ _ cache inv (kk (Tup.levels ts next)) (k₂ xs) (hkk (Tup.levels ts next) xs)
          (hkk2 xs xs) (hGk.freshTup xs) (hG.freshMVals xs) (hG2.freshTup xs) hD2 hKL
          hbo' hboK' hD hsp m ?_ hk2
        exact ⟨hml.1.upd_fupdTup xs, hml.2.1, hml.2.2.upd_fupdTup xs⟩
  | @load G D t a₁ aL k₁ kL ha _ ih =>
    intro Gk Dk G₂ D₂ next nl ρ baseOff baseOffK cache inv ek e₂ hwk hw2
      hGk hG hG2 hD2 hKL hbo hboK hD hsp m hml hw
    rcases hwk.rhs_load with ⟨ak, kk, rfl, _, hkk⟩
    rcases hw2.rhs_load with ⟨a₂, k₂, rfl, ha2, hkk2⟩
    dsimp only [analyzeMem, wp] at hsp hD hw ⊢
    rw [memLoadSweep_load']
    rw [hG2.vals_eq ha2] at hw
    dsimp only at ⊢
    rcases hw with ⟨v, hv, hk⟩
    obtain ⟨hakflt, hakev⟩ := resolveKey_good hbo (ha.mkey_lt hG)
    have haddr : (resolveKey baseOff a₁.mkey).eval ρ = aL.val :=
      hakev.trans (ha.mkey_ev hG)
    cases hlook : lookupCache (resolveKey baseOff a₁.mkey) t cache with
    | some cached =>
      dsimp only
      obtain ⟨hkeyflt, hkeyev, hld⟩ := lookupCache_mem hml.1 hlook
      rw [haddr, hv, Option.some.injEq] at hld
      have hv_eq : cached.out.val = v := hld.symm
      refine ih cached v (next + 1) nl (fupd ρ next v) baseOff baseOffK cache inv
        (kk next) (k₂ v) (hkk next v) (hkk2 v v) (hGk.cons v)
        (hG.cons_fupd hv_eq hkeyflt.mono (by rw [FKey.fev_fupd v hkeyflt, hkeyev, hv_eq]))
        (hG2.cons v) hD2 hKL (hbo.upd_fupd v) (hboK.upd_fupd v) hD hsp m ?_ hk
      exact ⟨hml.1.upd_one v, hml.2.1, hml.2.2.upd_one v⟩
    | none =>
      dsimp only [wp]
      rw [ha.mout_val hG]
      refine ⟨v, hv, ?_⟩
      refine ih (MVal.fresh v next) v (next + 1) nl (fupd ρ next v) baseOff baseOffK _ inv
        (kk next) (k₂ v) (hkk next v) (hkk2 v v) (hGk.cons v) (hG.cons_fresh v)
        (hG2.cons v) hD2 hKL (hbo.upd_fupd v) (hboK.upd_fupd v) hD hsp m ?_ hk
      exact ⟨hml.1.cons_load hakflt (by rw [haddr]; exact hv), hml.2.1, hml.2.2.upd_one v⟩
  | @store G D t v₁ vL a₁ aL k₁ kL hv ha _ ih =>
    intro Gk Dk G₂ D₂ next nl ρ baseOff baseOffK cache inv ek e₂ hwk hw2
      hGk hG hG2 hD2 hKL hbo hboK hD hsp m hml hw
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, _, hak, hkk⟩
    rcases hw2.rhs_store with ⟨v₂, a₂, k₂, rfl, hv2, ha2, hkk2⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hsp hD hw ⊢
    rw [hG2.vals_eq hv2, hG2.vals_eq ha2] at hw
    obtain ⟨hdisj, hsp'⟩ := SummaryPreserves.addWrite.1 hsp
    obtain ⟨hakflt, hakev⟩ := resolveKey_good hbo (ha.mkey_lt hG)
    have haddr : (resolveKey baseOff a₁.mkey).eval ρ = aL.val :=
      hakev.trans (ha.mkey_ev hG)
    have haddrK : (resolveKey baseOffK ak).eval ρ = aL.val :=
      (resolveKey_good hboK (hak.k_lt hGk)).2.trans (hak.k_ev hGk)
    rw [ha.mout_val hG, hv.mout_val hG]
    refine ⟨hw.1, ?_⟩
    have hinv' : InvMemGood inv (storeMem m t aL.val vL.val) :=
      hml.2.1.store_disjoint hml.2.2 vL.val haddrK hdisj
    split
    · next hbytes =>
      refine ih (Gk := Gk) (Dk := Dk) (G₂ := G₂) (D₂ := D₂) next nl ρ baseOff baseOffK _ inv
        kk k₂ hkk hkk2 hGk hG hG2 hD2 hKL hbo hboK hD hsp' (storeMem m t aL.val vL.val) ?_ hw.2
      exact ⟨hml.1.store_push hakflt (hv.mkey_lt hG) ((hv.mkey_ev hG).trans (hv.mout_val hG).symm)
        (hv.mout_val hG) haddr hbytes, hinv', hml.2.2⟩
    · refine ih (Gk := Gk) (Dk := Dk) (G₂ := G₂) (D₂ := D₂) next nl ρ baseOff baseOffK _ inv
        kk k₂ hkk hkk2 hGk hG hG2 hD2 hKL hbo hboK hD hsp' (storeMem m t aL.val vL.val) ?_ hw.2
      exact ⟨hml.1.store_filter _ t aL.val vL.val haddr, hinv', hml.2.2⟩
  | @call G D f as bs args₁ argsL k₁ kL hargs _ ih =>
    intro Gk Dk G₂ D₂ next nl ρ baseOff baseOffK _ inv ek e₂ hwk hw2
      hGk hG hG2 hD2 hKL hbo hboK hD hsp m hml hw
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, _, hkk⟩
    rcases hw2.rhs_call with ⟨args₂, k₂, rfl, hargs2, hkk2⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hsp hD hw ⊢
    rw [hG2.trel_vals_eq hargs2] at hw
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    have hinv_nil : inv = [] := by
      cases inv with
      | nil => rfl
      | cons e _ => exact False.elim (hsp e List.mem_cons_self)
    subst hinv_nil
    rw [hargs.mout_vals hG]
    refine ⟨P, E, hΓ, fun r m' hp => ?_, hE⟩
    refine ih (freshMVals _ r next) r (next + _) nl (fupdTup ρ next r) baseOff baseOffK [] []
      (kk (Tup.levels _ next)) (k₂ r) (hkk (Tup.levels _ next) r) (hkk2 r r)
      (hGk.freshTup r) (hG.freshMVals r) (hG2.freshTup r) hD2 hKL
      (hbo.upd_fupdTup r) (hboK.upd_fupdTup r) hD (fun _ h => nomatch h) m'
      (MemLoadGood.empty _ _ m') (hP r m' hp)
  | @jnz G D c₁ cL t₁ tL e₁' eL' hc _ _ iht ihe =>
    intro Gk Dk G₂ D₂ next nl ρ baseOff baseOffK cache inv ek e₂ hwk hw2
      hGk hG hG2 hD2 hKL hbo hboK hD hsp m hml hw
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, _, htk, hek⟩
    rcases hw2.rhs_jnz with ⟨c₂, t₂, e₂', rfl, hc2, ht2, he2⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hsp hD hw ⊢
    obtain ⟨hspt, hspe⟩ := SummaryPreserves.join.1 hsp
    rw [hc.mout_val hG]
    rw [hG2.vals_eq hc2] at hw
    exact ⟨fun h => iht next nl ρ baseOff baseOffK cache inv tk t₂ htk ht2 hGk hG hG2 hD2 hKL
             hbo hboK (hD.sub (TrieSub.union_left _ _)) hspt m hml (hw.1 h),
           fun h => ihe next nl ρ baseOff baseOffK cache inv ek' e₂' hek he2 hGk hG hG2 hD2 hKL
             hbo hboK (hD.sub (TrieSub.union_right _ _)) hspe m hml (hw.2 h)⟩
  | @jump G D ts j₁ jL args₁ argsL hj hargs =>
    intro Gk Dk G₂ D₂ next nl ρ baseOff baseOffK cache inv ek e₂ hwk hw2
      hGk hG hG2 hD2 hKL hbo hboK hD hsp m hml hw
    rcases hwk.rhs_jump with ⟨jk, argsk, rfl, hjk, _⟩
    rcases hw2.rhs_jump with ⟨j₂, args₂, rfl, hj2, hargs2⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hD hw ⊢
    have hj_eq : j₂ = jL.2 := hD2 _ hj2
    rw [hargs.mout_vals hG]
    rw [hG2.trel_vals_eq hargs2, hj_eq] at hw
    have hjk_eq : jk = jL.1 := (hKL _ hjk).1
    have hmem : (((Trie.empty : Trie Unit).insert jk ()).find? jL.1).isSome = true := by
      rw [hjk_eq, Trie.find?_insert_self]; rfl
    exact hD _ hj hmem (vals argsL) m hml.2.1 hw
  | ret hvs =>
    intro _ _ _ _ _ _ _ _ _ _ _ ek e₂ hwk hw2 _ hG hG2 _ _ _ _ _ _ m _ hw
    rcases hwk.rhs_ret with ⟨_, rfl, _⟩
    rcases hw2.rhs_ret with ⟨vs₂, rfl, hvs2⟩
    dsimp only [memLoadSweep, wp] at hw ⊢
    rw [hvs.mout_vals hG]
    rw [hG2.trel_vals_eq hvs2] at hw; exact hw
  | exit f hargs =>
    intro _ _ _ _ _ _ _ _ _ _ _ ek e₂ hwk hw2 _ hG hG2 _ _ _ _ _ _ m _ hw
    rcases hwk.rhs_exit with ⟨_, rfl, _⟩
    rcases hw2.rhs_exit with ⟨args₂, rfl, hargs2⟩
    dsimp only [memLoadSweep, wp] at hw ⊢
    rw [hargs.mout_vals hG]
    rw [hG2.trel_vals_eq hargs2] at hw; exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ _ _ _ _ ek e₂ hwk hw2 _ _ _ _ _ _ _ _ _ _ _ hw
    rw [hw2.rhs_hlt] at hw; rw [hwk.rhs_hlt]; exact hw
  | @group G D sig b₁ bL k₁ kL _ _ ihb ihk =>
    intro Gk Dk G₂ D₂ next nl ρ baseOff baseOffK cache inv ek e₂ hwk hw2
      hGk hG hG2 hD2 hKL hbo hboK hD hsp m hml hw
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    rcases hw2.rhs_group with ⟨b₂, k₂, rfl, hb2, hk2⟩
    dsimp only [analyzeMem, memLoadSweep, wp] at hsp hD hw ⊢
    intro Js hclosed
    let ls := Tup.levels sig nl
    let nl' := nl + sig.length
    let sb := (analyzeMemB next nl' baseOffK (bk ls)).1
    let lb := (analyzeMemB next nl' baseOffK (bk ls)).2.1
    let sk := (analyzeMem next nl' baseOffK (kk ls)).1
    let sum := sb.join sk
    let sumB := if anyLive nl sig.length lb then sum else sk
    let cacheB := filterCacheSummary sumB cache
    let inv' := cacheToInv ρ cacheB ++ inv
    let Js' := strengthenJs (InvMemGood inv') Js
    let JsL := tagConts nl Js'
    have hKL' : KLGood nl' (Tup.zip ls JsL ++ Dk) := hKL.append_levels Js'
    have hD2' : EqD (Tup.zip Js' JsL ++ D₂) := hD2.append_tag nl Js'
    have hspSumB : SummaryPreserves sumB inv' := by
      rw [SummaryPreserves.append]
      refine ⟨SummaryPreserves.filterSummary ρ sumB cache, ?_⟩
      cases hlive : anyLive nl sig.length lb
      · simp only [sumB, hlive, Bool.false_eq_true, ↓reduceIte]
        exact (SummaryPreserves.join.1 hsp).2
      · simp only [sumB, hlive, ↓reduceIte]
        exact hsp
    have hspK' : SummaryPreserves sk inv' := by
      cases hlive : anyLive nl sig.length lb
      · simpa [sumB, hlive] using hspSumB
      · have hspSum : SummaryPreserves sum inv' := by simpa [sumB, hlive] using hspSumB
        exact (SummaryPreserves.join.1 hspSum).2
    have hDK' : MemDGood inv' (analyzeMem next nl' baseOffK (kk ls)).2.1 (Tup.zip Js JsL ++ D) := by
      intro p hp hl xs m' hinv' hJ
      rcases List.mem_append.1 hp with hp | hp
      · exact mem_zip_tagConts_inv (InvMemGood inv') nl Js p hp xs m' hinv' hJ
      · exact hD p hp (trieMem_union_right hl) xs m'
          (fun e he => hinv' e (List.mem_append.2 (Or.inr he))) hJ
    have hinvKeys' : InvKeysGood ρ next inv' :=
      (InvKeysGood.of_cache (hml.1.filterSummary sumB)).append hml.2.2
    have hcl2 : Closed Γ Q X (b₂ Js') Js' := by
      rw [closed_iff] at hclosed ⊢
      intro ts i xs m' hb₂
      rw [strengthenJs_get]
      intro hinv_m'
      apply hclosed i xs m'
      rw [memLoadSweepB_analyzeMemB_get next nl' baseOff baseOffK cacheB (bk ls)]
      have hcb_m' : MemCacheGood (fupdTup ρ next xs) (next + ts.length) cacheB m' :=
        ((hml.1.filterSummary sumB).of_inv fun e he =>
          hinv_m' e (List.mem_append.2 (Or.inl he))).upd_fupdTup xs
      have hb1L := (hb2 Js' JsL).get i xs xs
      have hbkL := (hbk ls JsL).get i (Tup.levels ts next) xs
      cases hlive : anyLive nl sig.length lb
      · have hspB0 : SummaryPreserves (analyzeMem (next + ts.length) nl' baseOffK
            ((bk ls).get i (Tup.levels ts next))).1 inv :=
          analyzeMemB_get_summary next nl' baseOffK (bk ls) i (SummaryPreserves.join.1 hsp).1
        have hDB0 : MemDGood inv (analyzeMem (next + ts.length) nl' baseOffK
            ((bk ls).get i (Tup.levels ts next))).2.1 (Tup.zip Js JsL ++ D) := by
          refine MemDGood.sub (analyzeMemB_get_live_sub next nl' baseOffK (bk ls) i) ?_
          intro p hp hl xs' m'' hinv'' hJ
          rcases List.mem_append.1 hp with hp | hp
          · have hbnd := mem_zip_tagConts_bounds nl Js Js' p hp
            have hf := anyLive_eq_false sig.length nl lb hlive p.2.2.1 hbnd.1 hbnd.2
            rw [hf] at hl; cases hl
          · exact hD p hp (trieMem_union_left hl) xs' m'' hinv'' hJ
        have hinv_outer : InvMemGood inv m' :=
          fun e he => hinv_m' e (List.mem_append.2 (Or.inr he))
        exact ihb Js JsL i (freshMVals ts xs next) xs (next + ts.length) nl' (fupdTup ρ next xs)
          baseOff baseOffK cacheB inv ((bk ls).get i (Tup.levels ts next)) ((b₂ Js').get i xs)
          hbkL hb1L (hGk.freshTup xs) (hG.freshMVals xs) (hG2.freshTup xs) hD2' hKL'
          (hbo.upd_fupdTup xs) (hboK.upd_fupdTup xs) hDB0 hspB0 m'
          ⟨hcb_m', hinv_outer, hml.2.2.upd_fupdTup xs⟩ hb₂
      · have hspSum : SummaryPreserves sum inv' := by simpa [sumB, hlive] using hspSumB
        have hspB' : SummaryPreserves (analyzeMem (next + ts.length) nl' baseOffK
            ((bk ls).get i (Tup.levels ts next))).1 inv' :=
          analyzeMemB_get_summary next nl' baseOffK (bk ls) i (SummaryPreserves.join.1 hspSum).1
        have hDB' : MemDGood inv' (analyzeMem (next + ts.length) nl' baseOffK
            ((bk ls).get i (Tup.levels ts next))).2.1 (Tup.zip Js JsL ++ D) := by
          refine MemDGood.sub (analyzeMemB_get_live_sub next nl' baseOffK (bk ls) i) ?_
          intro p hp hl xs' m'' hinv'' hJ
          rcases List.mem_append.1 hp with hp | hp
          · exact mem_zip_tagConts_inv (InvMemGood inv') nl Js p hp xs' m'' hinv'' hJ
          · exact hD p hp (trieMem_union_left hl) xs' m''
              (fun e he => hinv'' e (List.mem_append.2 (Or.inr he))) hJ
        exact ihb Js JsL i (freshMVals ts xs next) xs (next + ts.length) nl' (fupdTup ρ next xs)
          baseOff baseOffK cacheB inv' ((bk ls).get i (Tup.levels ts next)) ((b₂ Js').get i xs)
          hbkL hb1L (hGk.freshTup xs) (hG.freshMVals xs) (hG2.freshTup xs) hD2' hKL'
          (hbo.upd_fupdTup xs) (hboK.upd_fupdTup xs) hDB' hspB' m'
          ⟨hcb_m', hinv_m', hinvKeys'.upd_fupdTup xs⟩ hb₂
    have hml' : MemLoadGood ρ next cache inv' m :=
      ⟨hml.1, (InvMemGood.of_cache (hml.1.filterSummary sumB)).append hml.2.1, hinvKeys'⟩
    exact ihk Js JsL next nl' ρ baseOff baseOffK cache inv' (kk ls) (k₂ Js')
      (hkk ls JsL) (hk2 Js' JsL) hGk hG hG2 hD2' hKL' hbo hboK hDK' hspK' m hml' (hw Js' hcl2)

/-! ## Relational well-formedness for `memLoadSweep` (`MValRel`, `RelCache`, `memLoad_wf`) -/

section
variable {V₁ V₂ : Ty → Type}

/-- Two `MVal`s are related when their output operands are `ArgRel`-related and keys match. -/
public def MValRel (G' : Ctx V₁ V₂) {t : Ty} (m₁ : MVal V₁ t) (m₂ : MVal V₂ t) : Prop :=
  ArgRel G' t m₁.out m₂.out ∧ m₁.key = m₂.key

theorem MValRel.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {m₁ : MVal V₁ t} {m₂ : MVal V₂ t} (h : MValRel G₁ m₁ m₂) : MValRel G₂ m₁ m₂ :=
  ⟨h.1.weaken hsub, h.2⟩

/-- Context relation for `memLoad_wf`. -/
public def MRelG (G' : Ctx V₁ V₂) (G : Ctx (MVal V₁) (MVal V₂)) : Prop :=
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

/-- Pointwise relation on `CacheEntry` pairs sharing identical `(ak, ty, valKey)`. -/
public inductive RelCacheEntry (G' : Ctx V₁ V₂) : CacheEntry V₁ → CacheEntry V₂ → Prop
  | mk {ak : AddrKey} {t : Ty}
      {v₁ : Arg V₁ t} {v₂ : Arg V₂ t} {k : FKey t} :
      ArgRel G' t v₁ v₂ →
      RelCacheEntry G' ⟨ak, t, v₁, k⟩ ⟨ak, t, v₂, k⟩

/-- Pointwise relation on dominating memory caches. -/
public inductive RelCache (G' : Ctx V₁ V₂) : List (CacheEntry V₁) → List (CacheEntry V₂) → Prop
  | nil : RelCache G' [] []
  | cons {e₁ e₂ c₁ c₂} : RelCacheEntry G' e₁ e₂ → RelCache G' c₁ c₂ →
      RelCache G' (e₁ :: c₁) (e₂ :: c₂)

theorem RelCache.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {c₁ : List (CacheEntry V₁)} → {c₂ : List (CacheEntry V₂)} →
    RelCache G₁ c₁ c₂ → RelCache G₂ c₁ c₂
  | _, _, .nil => .nil
  | _, _, .cons (.mk harg) hr => .cons (.mk (harg.weaken hsub)) (RelCache.weaken hsub hr)

theorem RelCache.filterWrite {G' : Ctx V₁ V₂} (ak : AddrKey) (bytes : Nat) :
    {c₁ : List (CacheEntry V₁)} → {c₂ : List (CacheEntry V₂)} →
    RelCache G' c₁ c₂ →
    RelCache G' (filterCacheWrite ak bytes c₁) (filterCacheWrite ak bytes c₂)
  | _, _, .nil => .nil
  | _, _, .cons (@RelCacheEntry.mk _ _ _ ak' t' v₁ v₂ k harg) hr => by
    simp only [filterCacheWrite, List.filter, entryDisjointWrite]
    cases ak'.sameBase ak && spanDisjoint ak.off bytes ak'.off t'.bytes
    · exact RelCache.filterWrite ak bytes hr
    · exact .cons (@RelCacheEntry.mk _ _ _ ak' t' v₁ v₂ k harg)
        (RelCache.filterWrite ak bytes hr)

theorem RelCache.filterSummary {G' : Ctx V₁ V₂} (s : MemSummary) :
    {c₁ : List (CacheEntry V₁)} → {c₂ : List (CacheEntry V₂)} →
    RelCache G' c₁ c₂ →
    RelCache G' (filterCacheSummary s c₁) (filterCacheSummary s c₂)
  | _, _, .nil => .nil
  | _, _, .cons (@RelCacheEntry.mk _ _ _ ak' t' v₁ v₂ k harg) hr => by
    simp only [filterCacheSummary, List.filter, summaryDisjointEntry, entryDisjointWrite]
    cases s with
    | unknown => exact RelCache.filterSummary .unknown hr
    | exact ws =>
      dsimp only
      cases ws.all fun w => ak'.sameBase w.ak && spanDisjoint w.ak.off w.bytes ak'.off t'.bytes
      · exact RelCache.filterSummary (.exact ws) hr
      · exact .cons (@RelCacheEntry.mk _ _ _ ak' t' v₁ v₂ k harg)
          (RelCache.filterSummary (.exact ws) hr)

inductive MLookupRel (G' : Ctx V₁ V₂) (t : Ty) :
    Option (MVal V₁ t) → Option (MVal V₂ t) → Prop
  | none : MLookupRel G' t none none
  | some {m₁ : MVal V₁ t} {m₂ : MVal V₂ t} :
      MValRel G' m₁ m₂ → MLookupRel G' t (some m₁) (some m₂)

theorem RelCache.lookup {G' : Ctx V₁ V₂} (ak : AddrKey) (t : Ty) :
    {c₁ : List (CacheEntry V₁)} → {c₂ : List (CacheEntry V₂)} → RelCache G' c₁ c₂ →
    MLookupRel G' t (lookupCache ak t c₁) (lookupCache ak t c₂)
  | _, _, .nil => .none
  | _, _, .cons (.mk harg) hr => by
    dsimp only [lookupCache]
    cases AddrKey.beq _ ak
    · exact RelCache.lookup ak t hr
    · cases hty : tyDecEq _ t with
      | isFalse _ => exact RelCache.lookup ak t hr
      | isTrue heq => subst heq; exact .some ⟨harg, rfl⟩

end

private def mstGet {sig : List (List Ty)} (bsMST : MemSumBlocks) {ts : List Ty}
    (i : Member ts sig) : MemSumTree :=
  match bsMST with
  | .nil => .leaf
  | .cons kh kt => match i with
    | .here => kh
    | .there i' => mstGet kt i'

private theorem memLoadSweepB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (baseOff : BaseOffMap) (cache : List (CacheEntry V)) :
    {sig : List (List Ty)} → (bsMST : MemSumBlocks) → (bs : Blocks (MVal V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (memLoadSweepB next baseOff cache bsMST bs).get i xs =
      memLoadSweep (next + ts.length) baseOff cache (mstGet bsMST i)
        (bs.get i (freshMVals ts xs next))
  | _ :: _, .nil, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .nil, .cons _ bst, _, .there i', xs =>
    memLoadSweepB_get next baseOff cache .nil bst i' xs
  | _ :: _, .cons _ ktt, .cons _ bst, _, .there i', xs =>
    memLoadSweepB_get next baseOff cache ktt bst i' xs

/-- Well-formedness preservation for `memLoadSweep`, proved via `Wf.induct`. -/
public theorem memLoad_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (MVal V₁) (MVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (MVal V₁) L₁ rs} {e₂ : Expr (MVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}
      (next : Nat) (baseOff : BaseOffMap)
      (c₁ : List (CacheEntry V₁)) (c₂ : List (CacheEntry V₂))
      (mst : MemSumTree),
      MRelG G' G → RelCache G' c₁ c₂ →
      Wf G' D (memLoadSweep next baseOff c₁ mst e₁)
              (memLoadSweep next baseOff c₂ mst e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' next baseOff c₁ c₂ mst hG hc
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      dsimp only [memLoadSweep]
      rw [TRel.mkey_eq hG hargs]
      refine .let_ (.mk code (TRel.mout hG hargs)) fun xs₁ xs₂ => ?_
      have hsub : ∀ p ∈ G', p ∈ (Tup.zip xs₁ xs₂ ++ G') :=
        fun _ hq => List.mem_append_right _ hq
      exact ih (freshMVals ts xs₁ next) (freshMVals ts xs₂ next) (next + ts.length) _
        c₁ c₂ _ (hG.freshMVals xs₁ xs₂ next) (hc.weaken hsub)
  | @load G D t a₁ a₂ k₁ k₂ ha _ ih =>
    intro G' next baseOff c₁ c₂ mst hG hc
    rw [memLoadSweep_load', memLoadSweep_load', ha.mkey_eq hG]
    dsimp only
    have hlook := hc.lookup (resolveKey baseOff a₂.mkey) t
    generalize hl1 : lookupCache _ t c₁ = r₁ at hlook
    generalize hl2 : lookupCache _ t c₂ = r₂ at hlook
    cases hlook with
    | none =>
      refine .load t (ha.mout hG) fun v₁ v₂ => ?_
      exact ih (MVal.fresh v₁ next) (MVal.fresh v₂ next) (next + 1) baseOff _ _ _
        (hG.freshOne v₁ v₂ next)
        (.cons (.mk (.var List.mem_cons_self))
          (hc.weaken fun _ hq => List.mem_cons_of_mem _ hq))
    | some hm => exact ih _ _ (next + 1) baseOff c₁ c₂ _ (hG.cons hm) hc
  | store hv ha _ ih =>
    intro G' next baseOff c₁ c₂ mst hG hc
    dsimp only [memLoadSweep]
    rw [ha.mkey_eq hG, hv.mkey_eq hG]
    refine .store (hv.mout hG) (ha.mout hG) ?_
    split
    · exact ih next baseOff _ _ _ hG
        (.cons (.mk (hv.mout hG)) (hc.filterWrite _ _))
    · exact ih next baseOff _ _ _ hG (hc.filterWrite _ _)
  | call f hargs _ ih =>
    intro G' next baseOff c₁ c₂ mst hG _
    dsimp only [memLoadSweep]
    refine .call f (TRel.mout hG hargs) fun xs₁ xs₂ => ?_
    exact ih (freshMVals _ xs₁ next) (freshMVals _ xs₂ next) (next + _) baseOff [] [] _
      (hG.freshMVals xs₁ xs₂ next) .nil
  | jnz hcj _ _ iht ihe =>
    intro G' next baseOff c₁ c₂ mst hG hc
    dsimp only [memLoadSweep]
    exact .jnz (hcj.mout hG) (iht next baseOff c₁ c₂ _ hG hc)
      (ihe next baseOff c₁ c₂ _ hG hc)
  | jump hj hargs =>
    intro G' _ _ _ _ _ hG _
    exact .jump hj (TRel.mout hG hargs)
  | ret hvs =>
    intro G' _ _ _ _ _ hG _
    exact .ret (TRel.mout hG hvs)
  | exit f hargs =>
    intro G' _ _ _ _ _ hG _
    exact .exit f (TRel.mout hG hargs)
  | hlt =>
    intro _ _ _ _ _ _ _ _; exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' next baseOff c₁ c₂ mst hG hc
    dsimp only [memLoadSweep]
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) (fun Js₁ Js₂ => ?_)
    · rw [memLoadSweepB_get, memLoadSweepB_get]
      have hsub : ∀ p ∈ G', p ∈ (Tup.zip xs₁ xs₂ ++ G') := fun _ hq => List.mem_append_right _ hq
      exact ihb Js₁ Js₂ i (freshMVals _ xs₁ next) (freshMVals _ xs₂ next) (next + _) baseOff
        _ _ _ (hG.freshMVals xs₁ xs₂ next) ((hc.filterSummary _).weaken hsub)
    · exact ihk Js₁ Js₂ next baseOff c₁ c₂ _ hG hc

public theorem Func.memLoad_wf {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.memLoad f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (MVal V₁) (MVal V₂) L₁ L₂ (freshMVals as xs₁ 0) (freshMVals as xs₂ 0)
  have hrel : MRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshMVals as xs₁ 0) (freshMVals as xs₂ 0)) := by
    rw [← List.append_nil (Tup.zip xs₁ xs₂),
        ← List.append_nil (Tup.zip (freshMVals as xs₁ 0) (freshMVals as xs₂ 0))]
    exact MRelG.freshMVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact LeanQbe.T.memLoad_wf hwf as.length .empty [] [] _ hrel .nil

public theorem Func.memLoad_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.memLoad f) xs m Q X := by
  have hwf := hf (MVal Val) Val Cont LCont (freshMVals as xs 0) xs
  have hwk := hf K Val KL LCont (Tup.levels as 0) xs
  have hw2 := hf Val Val Cont LCont xs xs
  let ρ := fupdTup (fun _ _ => default) 0 xs
  have hGk : KGood ρ as.length (Tup.zip (Tup.levels as 0) xs) := by
    rw [← List.append_nil (Tup.zip (Tup.levels as 0) xs)]
    exact Nat.zero_add as.length ▸ KGood.freshTup (ρ := fun _ _ => default) (next := 0) (Gk := [])
      (fun _ hp => nomatch hp) xs
  have hG : MGood ρ as.length (Tup.zip (freshMVals as xs 0) xs) := by
    rw [← List.append_nil (Tup.zip (freshMVals as xs 0) xs)]
    exact Nat.zero_add as.length ▸ MGood.freshMVals (ρ := fun _ _ => default) (next := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  have hG2 : EqG (Tup.zip xs xs) := by
    rw [← List.append_nil (Tup.zip xs xs)]
    exact EqG.freshTup (G₂ := []) (fun _ hp => nomatch hp) xs
  exact memLoad_wp hwf as.length 0 ρ .empty .empty [] [] (f K KL (Tup.levels as 0))
    (f Val Cont xs) hwk hw2 hGk hG hG2 (fun _ hp => nomatch hp) (fun _ hp => nomatch hp)
    (BaseOffGood.empty ρ as.length) (BaseOffGood.empty ρ as.length)
    (fun _ hp => nomatch hp) (fun _ hp => nomatch hp) m (MemLoadGood.empty ρ as.length m) h

/-! ## `AssumeElim` correctness (`assumeElim_wp`, `assumeElim_wf`, `Func.assumeElim_*`) -/

theorem Expr.isHlt_true_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {e : Expr V L rs} (h : e.isHlt = true) : e = .hlt := by
  cases e <;> first | rfl | exact Bool.noConfusion h

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
public theorem assumeElim_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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
public theorem assumeElim_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
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

public theorem Func.assumeElim_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.assumeElim f).Wf :=
  fun V₁ V₂ L₁ L₂ xs₁ xs₂ => LeanQbe.T.assumeElim_wf (hf V₁ V₂ L₁ L₂ xs₁ xs₂)

public theorem Func.assumeElim_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.assumeElim f) xs m Q X :=
  let _ := hf
  assumeElim_wp (f Val Cont xs) m h

end LeanQbe.T
