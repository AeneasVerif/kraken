module

public import LeanQbe.T.Examples.Arisca.ArtSoundAux

/-!
# Soundness of the ART checker

`checkArt_sound : checkArt signed aigN aigLen artN artLen = true →`
`  ∃ g, parseAig (toBytes aigN aigLen) = some g ∧`
`    ∀ ρ, W(O)(ρ) ≡ Wspec(a)(ρ)·Wspec(b)(ρ) (mod 2^|O|)`.

Proof architecture: fix a PI assignment `ρ`; every net symbol gets the value
`σ (2n+ph) = litVal (bind n) ⊕ ph`. Invariants: `RulesOk` (every installed rule evaluates to its
net), `PairsOk` (registered HA pairs never both true), `evalP σ P = evalP σ P₀` through MAIN.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanQbe.T.Examples.Arisca

@[expose] public section

/-! ## AIG semantics (trusted definitions) -/

/-- fan-ins of AND node `n` (node `I+1+i` is `ands[i]`) -/
def Aig.andAt (g : Aig) (n : Nat) : Nat × Nat := g.ands.getD (n - g.I - 1) (0, 0)

/-- value of node `n` under the PI assignment `ρ` (PI `i` is node `i+1`). -/
def Aig.nodeVal (g : Aig) (ρ : Nat → Bool) (n : Nat) : Bool :=
  if n = 0 then false
  else if n ≤ g.I then ρ (n - 1)
  else
    (if (g.andAt n).1 / 2 < n then
        g.nodeVal ρ ((g.andAt n).1 / 2) ^^ ((g.andAt n).1 % 2 == 1) else false) &&
    (if (g.andAt n).2 / 2 < n then
        g.nodeVal ρ ((g.andAt n).2 / 2) ^^ ((g.andAt n).2 % 2 == 1) else false)
termination_by n

/-- value of literal `l` -/
def Aig.litVal (g : Aig) (ρ : Nat → Bool) (l : Nat) : Bool := g.nodeVal ρ (l / 2) ^^ (l % 2 == 1)

/-- `t` encodes a row: bit `j` is `bs[j]` -/
def tOf : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * tOf bs

/-- symbol valuation induced by `ρ` and the bindings: `σ (2n+ph) = litVal (bind n) ⊕ ph` -/
noncomputable def sig (g : Aig) (ρ : Nat → Bool) (e : Env) (i : Nat) : Bool :=
  (Option.elim (e.bind.get e.nd (i / 2)) false (g.litVal ρ)) ^^ (i % 2 == 1)

def RulesOk (w : Nat) (σ : Nat → Bool) (e : Env) (rules : Tree Poly) : Prop :=
  ∀ v Q, rules.get e.nd v = some Q → bv w (σ (2 * v)) = evalP w σ Q

def GInv (w : Nat) (σ : Nat → Bool) (e : Env) (st : GS) : Prop :=
  RulesOk w σ e st.rules ∧ PairsOk σ st.pr

/-! ## Spec words (trusted statement) -/

/-- `Σ_j 2^j · out_j` over the listed output positions -/
def outWordL (g : Aig) (ρ : Nat → Bool) : List Nat → Nat
  | [] => 0
  | j :: js => 2 ^ j * (g.litVal ρ (g.outs.getD j 0)).toNat + outWordL g ρ js

/-- unsigned value of the AIG outputs `O[0..|O|)` (LSB first) -/
def outWord (g : Aig) (ρ : Nat → Bool) : Nat := outWordL g ρ (List.range g.outs.length)

/-- `Σ_{j ∈ js} 2^j · out_{off+j}` over relative output bit indices `js` -/
def outSliceL (g : Aig) (ρ : Nat → Bool) (off : Nat) : List Nat → Nat
  | [] => 0
  | j :: js => 2 ^ j * (g.litVal ρ (g.outs.getD (off + j) 0)).toNat + outSliceL g ρ off js

/-- unsigned value of the `w`-bit output slice `O[off .. off + w)` (LSB first) -/
def outSlice (g : Aig) (ρ : Nat → Bool) (off w : Nat) : Nat :=
  outSliceL g ρ off (List.range w)

/-- helper exposing start index `j` for `miterHalfTerms` induction -/
noncomputable def miterHalfGo (M : Nat) (neg : Bool) (rules : Tree Poly) (nd : Nat)
    (refs aouts : List Nat) (j : Nat) : List Poly :=
  List.rec (motive := fun _ => Nat → List Nat → List Poly) (fun _ _ => [])
    (fun r _ ih j ao =>
      List.rec [] (fun a ao' _ => miterTerm M neg rules nd r a j :: ih (Nat.succ j) ao') ao)
    refs j aouts

/-- `Σ_i c_i · ρ(off+i)`, `c_i = 2^i`, except `c_{n-1} = -2^(n-1)` when `signed` -/
def inWordL (signed : Bool) (n : Nat) (ρ : Nat → Bool) (off : Nat) : List Nat → Int
  | [] => 0
  | i :: is =>
    (if signed = true ∧ i + 1 = n then -(2 ^ i : Int) else 2 ^ i) * (ρ (off + i)).toNat +
      inWordL signed n ρ off is

/-- value of the `n`-bit input word `PI[off .. off+n)` (LSB first), two's complement if `signed` -/
def inWord (signed : Bool) (n : Nat) (ρ : Nat → Bool) (off : Nat) : Int :=
  inWordL signed n ρ off (List.range n)

end

public section

/-! ## Recursor reduction lemmas -/

@[simp] theorem brec_false {α : Sort _} (f t : α) : (Bool.rec f t false : α) = f := rfl
@[simp] theorem brec_true {α : Sort _} (f t : α) : (Bool.rec f t true : α) = t := rfl
@[simp] theorem orec_none {α : Type _} {β : Sort _} (n : β) (s : α → β) :
    (Option.rec n s none : β) = n := rfl
@[simp] theorem orec_some {α : Type _} {β : Sort _} (n : β) (s : α → β) (a : α) :
    (Option.rec n s (some a) : β) = s a := rfl

theorem natrec_succ {motive : Nat → Sort _} (z : motive 0) (s : (n : Nat) → motive n → motive (n+1))
    (n : Nat) : (Nat.rec z s (n+1) : motive (n+1)) = s n (Nat.rec z s n) := rfl

theorem beq_true {a b : Nat} : Nat.beq a b = true ↔ a = b := by
  simp [Nat.beq_eq]
theorem ble_true {a b : Nat} : Nat.ble a b = true ↔ a ≤ b := by
  simp [Nat.ble_eq]

/-! ## Tries -/

theorem Tree.getP_empty {α : Type} (k d p : Nat) : Tree.getP (α := α) k d p .empty = none := by
  cases d <;> rfl

theorem Tree.getP_setP {α : Type} (k k' : Nat) (v x : α) (d : Nat) :
    ∀ (p p' : Nat) (t : Tree α), Tree.getP k' d p' (Tree.setP k v d p t) = some x →
      (k' = k ∧ x = v) ∨ Tree.getP k' d p' t = some x := by
  induction d with
  | zero =>
    intro p p' t h
    change (Bool.rec none (some v) (Nat.beq k' k) : Option α) = some x at h
    cases hb : Nat.beq k' k <;> simp [hb] at h
    exact .inl ⟨beq_true.mp hb, h.symm⟩
  | succ d ih =>
    intro p p' t h
    have key : ∀ (l r : Tree α),
        (Tree.getP k' (d+1) p' (Bool.rec (Tree.br l (Tree.setP k v d (Nat.shiftRight p 1) r))
          (Tree.br (Tree.setP k v d (Nat.shiftRight p 1) l) r)
          (Nat.beq (Nat.land p 1) 0)) = some x) →
        (k' = k ∧ x = v) ∨ Tree.getP k' (d+1) p' (Tree.br l r) = some x := by
      intro l r h
      cases hp : Nat.beq (Nat.land p 1) 0 <;> cases hp' : Nat.beq (Nat.land p' 1) 0 <;>
        simp only [hp, brec_false, brec_true] at h <;>
        change (Bool.rec _ _ (Nat.beq (Nat.land p' 1) 0) : Option α) = some x at h <;>
        simp only [hp', brec_false, brec_true] at h <;>
        first
        | exact .inr (by change (Bool.rec _ _ (Nat.beq (Nat.land p' 1) 0) : Option α) = some x
                         simp only [hp', brec_false, brec_true]; exact h)
        | (rcases ih _ _ _ h with h | h
           · exact .inl h
           · exact .inr (by change (Bool.rec _ _ (Nat.beq (Nat.land p' 1) 0) : Option α) = some x
                            simp only [hp', brec_false, brec_true]; exact h))
    cases t with
    | empty =>
      rcases key .empty .empty h with h | h
      · exact .inl h
      · change (Bool.rec (Tree.getP k' d (Nat.shiftRight p' 1) Tree.empty)
          (Tree.getP k' d (Nat.shiftRight p' 1) Tree.empty) (Nat.beq (Nat.land p' 1) 0) : Option α)
          = some x at h
        rw [Tree.getP_empty] at h
        cases hq : Nat.beq (Nat.land p' 1) 0 <;> rw [hq] at h <;> cases h
    | tip a b =>
      rcases key .empty .empty h with h | h
      · exact .inl h
      · change (Bool.rec (Tree.getP k' d (Nat.shiftRight p' 1) Tree.empty)
          (Tree.getP k' d (Nat.shiftRight p' 1) Tree.empty) (Nat.beq (Nat.land p' 1) 0) : Option α)
          = some x at h
        rw [Tree.getP_empty] at h
        cases hq : Nat.beq (Nat.land p' 1) 0 <;> rw [hq] at h <;> cases h
    | br l r => exact key l r h

theorem Tree.get_set {α : Type} {d k k' : Nat} {v x : α} {t : Tree α}
    (h : (t.set d k v).get d k' = some x) : (k' = k ∧ x = v) ∨ t.get d k' = some x :=
  Tree.getP_setP k k' v x d k k' t h

theorem Tree.get_empty {α : Type} (d k : Nat) : (Tree.empty : Tree α).get d k = none :=
  Tree.getP_empty k d k

/-! ## CPS readers -/

theorem rd_true {ws : List Nat} {k : Nat → List Nat → Bool} (h : rd ws false k = true) :
    ∃ w ws', ws = w :: ws' ∧ k w ws' = true := by
  cases ws with
  | nil => exact absurd h (by simp [rd])
  | cons w ws => exact ⟨w, ws, rfl, h⟩

theorem rdN_true_aux {k : List Nat → List Nat → Bool} (n : Nat) :
    ∀ (acc ws : List Nat),
      (Nat.rec (motive := fun _ => List Nat → List Nat → Bool) (fun acc ws => k acc.reverse ws)
        (fun _ ih acc ws => rd ws false fun w ws => ih (w :: acc) ws) n acc ws) = true →
      ∃ xs ws', xs.length = n + acc.length ∧ k xs ws' = true := by
  induction n with
  | zero => intro acc ws h; exact ⟨_, _, by simp, h⟩
  | succ n ih =>
    intro acc ws h
    obtain ⟨w, ws', -, h⟩ := rd_true h
    obtain ⟨xs, ws'', hl, h⟩ := ih _ _ h
    exact ⟨xs, ws'', by simp at hl; omega, h⟩

theorem rdN_true {n : Nat} {k : List Nat → List Nat → Bool} {ws : List Nat}
    (h : rdN false n k ws = true) : ∃ xs ws', xs.length = n ∧ k xs ws' = true := by
  obtain ⟨xs, ws', hl, h⟩ := rdN_true_aux (k := k) n [] ws h
  exact ⟨xs, ws', by simpa using hl, h⟩

/-! ## AIG node lemmas -/

theorem Aig.nodeVal_zero (g : Aig) (ρ : Nat → Bool) : g.nodeVal ρ 0 = false := by
  rw [Aig.nodeVal]; simp

theorem Aig.nodeVal_pi (g : Aig) (ρ : Nat → Bool) (n : Nat) (h0 : n ≠ 0) (h : n ≤ g.I) :
    g.nodeVal ρ n = ρ (n - 1) := by
  rw [Aig.nodeVal]; simp [h0, h]

theorem Aig.nodeVal_and (g : Aig) (ρ : Nat → Bool) (n : Nat) (h0 : n ≠ 0) (h : ¬ n ≤ g.I)
    (h1 : (g.andAt n).1 / 2 < n) (h2 : (g.andAt n).2 / 2 < n) :
    g.nodeVal ρ n = (g.litVal ρ (g.andAt n).1 && g.litVal ρ (g.andAt n).2) := by
  rw [Aig.nodeVal]; simp [h0, h, h1, h2, Aig.litVal]

/-! ## The AND trie -/

theorem andTree_get_aux (d : Nat) (ands : List (Nat × Nat)) :
    ∀ (n : Nat) (t : Tree (Nat × Nat)) (k : Nat) (r : Nat × Nat),
      (List.rec (motive := fun _ => Nat → Tree (Nat × Nat) → Tree (Nat × Nat)) (fun _ t => t)
        (fun a _ ih n t => ih (Nat.succ n) (Tree.set d n a t)) ands n t).get d k = some r →
      (∃ i, i < ands.length ∧ k = n + i ∧ ands.getD i (0, 0) = r) ∨ t.get d k = some r := by
  induction ands with
  | nil => intro n t k r h; exact .inr h
  | cons a as ih =>
    intro n t k r h
    rcases ih _ _ _ _ h with ⟨i, hi, hk, hr⟩ | h
    · exact .inl ⟨i + 1, by simp; omega, by omega, by simpa using hr⟩
    · rcases Tree.get_set h with ⟨hk, hr⟩ | h
      · exact .inl ⟨0, by simp, by omega, by simp [hr]⟩
      · exact .inr h

theorem andTree_get {d I : Nat} {ands : List (Nat × Nat)} {k : Nat} {r : Nat × Nat}
    (h : (andTree d I ands).get d k = some r) :
    I < k ∧ (⟨0, I, [], ands⟩ : Aig).andAt k = r := by
  rcases andTree_get_aux d ands (Nat.succ I) .empty k r h with ⟨i, hi, hk, hr⟩ | h
  · refine ⟨by omega, ?_⟩
    simp only [Aig.andAt]; rw [show k - I - 1 = i by omega]; exact hr
  · simp [Tree.get_empty] at h

/-! ## Cone simulation -/

theorem lookup_some {n v : Nat} {l : List (Nat × Nat)} (h : lookup n l = some v) :
    ∃ x ∈ l, x.1 = n ∧ x.2 = v := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    change (Bool.rec (lookup n l) (some a.2) (Nat.beq n a.1) : Option Nat) = some v at h
    cases hb : Nat.beq n a.1 <;> rw [hb] at h
    · obtain ⟨x, hx, h1, h2⟩ := ih h; exact ⟨x, by simp [hx], h1, h2⟩
    · cases h; exact ⟨a, by simp, (beq_true.mp hb).symm, rfl⟩

theorem shiftRight_one (n : Nat) : Nat.shiftRight n 1 = n / 2 := by
  show n >>> 1 = n / 2
  simp [Nat.shiftRight_eq_div_pow]

theorem land_one (n : Nat) : Nat.land n 1 = n % 2 := by
  show n &&& 1 = n % 2
  exact Nat.and_one_is_mod n

theorem cmpl_bit {full t : Nat} (hfull : full.testBit t = true) (lit v : Nat) :
    (cmpl full lit v).testBit t = (v.testBit t ^^ (lit % 2 == 1)) := by
  unfold cmpl
  cases hb : Nat.beq (Nat.land lit 1) 1 <;> simp only [brec_false, brec_true]
  · have : lit % 2 ≠ 1 := by
      intro h; rw [land_one, h] at hb; exact absurd hb (by decide)
    have h2 : (lit % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; exact this
    rw [h2, Bool.xor_false]
  · have : lit % 2 = 1 := by rw [land_one] at hb; exact beq_true.mp hb
    show (full ^^^ v).testBit t = _
    simp [Nat.testBit_xor, hfull, this]

section sim
variable (g : Aig) (ρ : Nat → Bool) (e : Env)
  (hT : e.andT = andTree e.ad g.I g.ands) (full t : Nat) (hfull : full.testBit t = true)
  (leaves : List (Nat × Nat)) (hl : ∀ x ∈ leaves, x.2.testBit t = g.nodeVal ρ x.1)
include hT hfull hl

theorem sim_ok : ∀ (fuel lit : Nat) (memo : List (Nat × Nat)) (bud : Nat)
    (res : Nat × List (Nat × Nat) × Nat), sim e full leaves fuel lit memo bud = some res →
    (∀ x ∈ memo, x.2.testBit t = g.nodeVal ρ x.1) →
    res.1.testBit t = g.litVal ρ lit ∧ ∀ x ∈ res.2.1, x.2.testBit t = g.nodeVal ρ x.1 := by
  intro fuel
  induction fuel with
  | zero => intro lit memo bud res h; cases h
  | succ f ih =>
    intro lit memo bud res h hm
    change simStep e full leaves (sim e full leaves f) lit memo bud = some res at h
    unfold simStep at h
    have hlv : ∀ v, v.testBit t = g.nodeVal ρ (lit / 2) →
        (cmpl full lit v).testBit t = g.litVal ρ lit := by
      intro v hv; rw [cmpl_bit hfull, hv]; rfl
    cases h1 : lookup (Nat.shiftRight lit 1) leaves with
    | some v =>
      rw [h1] at h; simp only [orec_some] at h; cases h
      obtain ⟨x, hx, hx1, hx2⟩ := lookup_some h1
      refine ⟨hlv v ?_, hm⟩
      rw [← hx2, hl x hx, hx1, shiftRight_one]
    | none =>
      rw [h1] at h; simp only [orec_none] at h
      cases h2 : Nat.beq (Nat.shiftRight lit 1) 0
      · rw [h2] at h; simp only [brec_false] at h
        cases h3 : lookup (Nat.shiftRight lit 1) memo with
        | some v =>
          rw [h3] at h; simp only [orec_some] at h; cases h
          obtain ⟨x, hx, hx1, hx2⟩ := lookup_some h3
          refine ⟨hlv v ?_, hm⟩
          rw [← hx2, hm x hx, hx1, shiftRight_one]
        | none =>
          rw [h3] at h; simp only [orec_none] at h
          cases h4 : Nat.ble (Nat.shiftRight lit 1) e.I
          · rw [h4] at h; simp only [brec_false] at h
            cases h5 : Nat.beq bud 0
            · rw [h5] at h; simp only [brec_false] at h
              cases h6 : e.andT.get e.ad (Nat.shiftRight lit 1) with
              | none => rw [h6] at h; cases h
              | some r =>
                rw [h6] at h; simp only [orec_some] at h
                cases h7 : (Bool.rec false
                    (Nat.ble (Nat.succ r.2) (Nat.mul (Nat.shiftRight lit 1) 2))
                    (Nat.ble (Nat.succ r.1) (Nat.mul (Nat.shiftRight lit 1) 2)) : Bool)
                · rw [h7] at h; cases h
                · rw [h7] at h; simp only [brec_true] at h
                  have hr1 : r.1 + 1 ≤ lit / 2 * 2 ∧ r.2 + 1 ≤ lit / 2 * 2 := by
                    cases h8 : Nat.ble (Nat.succ r.1) (Nat.mul (Nat.shiftRight lit 1) 2) <;>
                      rw [h8] at h7 <;> simp only [brec_false, brec_true] at h7
                    · cases h7
                    · rw [shiftRight_one] at h7 h8
                      exact ⟨ble_true.mp h8, ble_true.mp h7⟩
                  cases h9 : sim e full leaves f r.1 memo (Nat.sub bud 1) with
                  | none => rw [h9] at h; cases h
                  | some x0 =>
                    rw [h9] at h; simp only [orec_some] at h
                    obtain ⟨hx0, hm0⟩ := ih _ _ _ _ h9 hm
                    cases h10 : sim e full leaves f r.2 x0.2.1 x0.2.2 with
                    | none => rw [h10] at h; cases h
                    | some x1 =>
                      rw [h10] at h; simp only [orec_some] at h; cases h
                      obtain ⟨hx1, hm1⟩ := ih _ _ _ _ h10 hm0
                      rw [hT] at h6
                      obtain ⟨hlt, hat⟩ := andTree_get h6
                      have hat' : g.andAt (lit / 2) = r := by
                        rw [shiftRight_one] at hat; exact hat
                      have hn0 : lit / 2 ≠ 0 := by rw [shiftRight_one] at hlt; omega
                      have hnI : ¬ lit / 2 ≤ g.I := by rw [shiftRight_one] at hlt; omega
                      have hval : g.nodeVal ρ (lit / 2) = (g.litVal ρ r.1 && g.litVal ρ r.2) := by
                        rw [Aig.nodeVal_and g ρ _ hn0 hnI (by rw [hat']; omega)
                          (by rw [hat']; omega), hat']
                      have hand : (Nat.land x0.1 x1.1).testBit t = g.nodeVal ρ (lit / 2) := by
                        show (x0.1 &&& x1.1).testBit t = _
                        rw [Nat.testBit_and, hx0, hx1, hval]
                      refine ⟨hlv _ hand, ?_⟩
                      intro x hx
                      simp only [List.mem_cons] at hx
                      rcases hx with rfl | hx
                      · show (Nat.land x0.1 x1.1).testBit t = g.nodeVal ρ (Nat.shiftRight lit 1)
                        rw [shiftRight_one]; exact hand
                      · exact hm1 x hx
            · rw [h5] at h; cases h
          · rw [h4] at h; cases h
      · rw [h2] at h; simp only [brec_true] at h; cases h
        refine ⟨hlv 0 ?_, hm⟩
        rw [beq_true, shiftRight_one] at h2
        rw [h2, Aig.nodeVal_zero]; simp

end sim

theorem tt_ok (g : Aig) (ρ : Nat → Bool) (e : Env) (hT : e.andT = andTree e.ad g.I g.ands)
    (full t : Nat) (hfull : full.testBit t = true) (leaves : List (Nat × Nat))
    (hl : ∀ x ∈ leaves, x.2.testBit t = g.nodeVal ρ x.1) (lit v : Nat)
    (h : tt e full leaves lit = some v) : v.testBit t = g.litVal ρ lit := by
  unfold tt at h
  cases h1 : sim e full leaves 70 lit [] 64 with
  | none => rw [h1] at h; cases h
  | some r =>
    rw [h1] at h; simp only [orec_some] at h; cases h
    exact (sim_ok g ρ e hT full t hfull leaves hl 70 lit [] 64 r h1 (by simp)).1

/-! ## List helpers (indexed) -/

theorem nthN_nil (i : Nat) : nthN [] i = 0 := rfl
theorem nthN_zero (a : Nat) (l : List Nat) : nthN (a :: l) 0 = a := rfl
theorem nthN_succ (a : Nat) (l : List Nat) (i : Nat) : nthN (a :: l) (i + 1) = nthN l i := rfl

theorem nthN_eq_getD (l : List Nat) (k : Nat) : nthN l k = l.getD k 0 := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => cases k with
    | zero => rfl
    | succ k => rw [nthN_succ, ih]; simp

theorem band_true {c x : Bool} (h : (Bool.rec false x c : Bool) = true) : c = true ∧ x = true := by
  cases c <;> simp_all

theorem orec_true {α : Type} {o : Option α} {f : α → Bool}
    (h : (Option.rec false f o : Bool) = true) :
    ∃ a, o = some a ∧ f a = true := by
  cases o <;> simp_all

theorem tOf_bit (bs : List Bool) (j : Nat) : (tOf bs).testBit j = bs.getD j false := by
  induction bs generalizing j with
  | nil => simp [tOf]
  | cons b bs ih =>
    cases j with
    | zero => cases b <;> simp [tOf, Nat.testBit_zero] <;> omega
    | succ j =>
      rw [Nat.testBit_add_one]
      have : (b.toNat + 2 * tOf bs) / 2 = tOf bs := by cases b <;> simp <;> omega
      simp only [tOf]; rw [this, ih]; simp

theorem tOf_lt (bs : List Bool) : tOf bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [tOf]
  | cons b bs ih => cases b <;> simp [tOf, Nat.pow_succ] <;> omega

theorem mkLeaves_spec (full : Nat) (lits : List Nat) :
    ∀ (j : Nat) (acc leaves : List (Nat × Nat)),
      (List.rec (motive := fun _ => Nat → List (Nat × Nat) → Option (List (Nat × Nat)))
        (fun _ acc => some acc)
        (fun b _ ih j acc =>
          Option.rec
            (ih (Nat.succ j) ((Nat.shiftRight b 1, cmpl full b (Nat.land (xmask j) full)) :: acc))
            (fun _ => none) (lookup (Nat.shiftRight b 1) acc))
        lits j acc) = some leaves →
      ∀ x ∈ leaves, x ∈ acc ∨ ∃ i, i < lits.length ∧
        x = (Nat.shiftRight (nthN lits i) 1,
          cmpl full (nthN lits i) (Nat.land (xmask (j + i)) full)) := by
  induction lits with
  | nil => intro j acc leaves h x hx; simp at h; subst h; exact .inl hx
  | cons b bs ih =>
    intro j acc leaves h x hx
    dsimp only at h
    cases h1 : lookup (Nat.shiftRight b 1) acc with
    | some _ => rw [h1] at h; cases h
    | none =>
      rw [h1] at h; simp only [orec_none] at h
      rcases ih _ _ _ h x hx with hx | ⟨i, hi, rfl⟩
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact .inr ⟨0, by simp, by simp [nthN_zero]⟩
        · exact .inl hx
      · exact .inr ⟨i + 1, by simp; omega, by
          rw [nthN_succ, show j + (i + 1) = Nat.succ j + i by omega]⟩

theorem binds_spec (e : Env) (ins : List Nat) :
    ∀ bl, binds e ins = some bl → bl.length = ins.length ∧
      ∀ i, i < ins.length → e.bind.get e.nd (Nat.shiftRight (nthN ins i) 1) = some (nthN bl i) := by
  induction ins with
  | nil => intro bl h; cases h; simp
  | cons x xs ih =>
    intro bl h
    unfold binds at h; dsimp only at h
    cases h1 : e.bind.get e.nd (Nat.shiftRight x 1) with
    | none => rw [h1] at h; cases h
    | some b =>
      rw [h1] at h; simp only [orec_some] at h
      cases h2 : binds e xs with
      | none => unfold binds at h2; rw [h2] at h; cases h
      | some bs =>
        unfold binds at h2; rw [h2] at h; simp only [orec_some] at h; cases h
        obtain ⟨hl, hb⟩ := ih bs (by unfold binds; exact h2)
        refine ⟨by simp [hl], ?_⟩
        intro i hi
        cases i with
        | zero => exact h1
        | succ i => exact hb i (by simp at hi; omega)

theorem ttAll_spec (e : Env) (full : Nat) (leaves : List (Nat × Nat)) (nets : List Nat) :
    ∀ tabs, ttAll e full leaves nets = some tabs → tabs.length = nets.length ∧
      ∀ i, i < nets.length → ∃ b, e.bind.get e.nd (nthN nets i) = some b ∧
        tt e full leaves b = some (nthN tabs i) := by
  induction nets with
  | nil => intro tabs h; cases h; simp
  | cons o os ih =>
    intro tabs h
    unfold ttAll at h; dsimp only at h
    cases h1 : e.bind.get e.nd o with
    | none => rw [h1] at h; cases h
    | some b =>
      rw [h1] at h; simp only [orec_some] at h
      cases h2 : tt e full leaves b with
      | none => rw [h2] at h; cases h
      | some v =>
        rw [h2] at h; simp only [orec_some] at h
        cases h3 : ttAll e full leaves os with
        | none => unfold ttAll at h3; rw [h3] at h; cases h
        | some vs =>
          unfold ttAll at h3; rw [h3] at h; simp only [orec_some] at h; cases h
          obtain ⟨hl, hb⟩ := ih vs (by unfold ttAll; exact h3)
          refine ⟨by simp [hl], ?_⟩
          intro i hi
          cases i with
          | zero => exact ⟨b, h1, h2⟩
          | succ i => exact hb i (by simp at hi; omega)

theorem tinDef_spec (full : Nat) (ins : List Nat) : ∀ j,
    (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
      (fun _ _ ih j => Nat.land (xmask j) full :: ih (Nat.succ j)) ins j).length = ins.length ∧
    ∀ i, i < ins.length → nthN (List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
      (fun _ _ ih j => Nat.land (xmask j) full :: ih (Nat.succ j)) ins j) i =
        Nat.land (xmask (j + i)) full := by
  induction ins with
  | nil => intro j; simp
  | cons x xs ih =>
    intro j
    obtain ⟨hl, hn⟩ := ih (Nat.succ j)
    dsimp only
    refine ⟨by rw [List.length_cons, hl]; rfl, ?_⟩
    intro i hi
    cases i with
    | zero => rfl
    | succ i =>
      rw [nthN_succ, hn i (by simp at hi; omega), show Nat.succ j + i = j + (i + 1) by omega]

theorem netsOf_spec (ins : List Nat) : (netsOf ins).length = ins.length ∧
    ∀ i, i < ins.length → nthN (netsOf ins) i = Nat.shiftRight (nthN ins i) 1 := by
  induction ins with
  | nil => simp [netsOf]
  | cons x xs ih =>
    obtain ⟨hl, hn⟩ := ih
    refine ⟨by simp [netsOf] at hl ⊢; exact hl, ?_⟩
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hn i (by simp at hi; omega)

theorem zipEnv_spec (ins : List Nat) : ∀ (tin : List Nat) (y : Nat × Nat), y ∈ zipEnv ins tin →
    ∃ i, i < ins.length ∧ i < tin.length ∧
      y = (Nat.mul 2 (Nat.shiftRight (nthN ins i) 1), nthN tin i) := by
  induction ins with
  | nil => intro tin y h; simp [zipEnv] at h
  | cons x xs ih =>
    intro tin y h
    cases tin with
    | nil => simp [zipEnv] at h
    | cons t ts =>
      change y ∈ (Nat.mul 2 (Nat.shiftRight x 1), t) :: zipEnv xs ts at h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, by simp, by simp, rfl⟩
      · obtain ⟨i, h1, h2, rfl⟩ := ih ts y h
        exact ⟨i + 1, by simp; omega, by simp; omega, rfl⟩

theorem getD_map_nthN (f : Nat → Bool) (l : List Nat) (j : Nat) (hj : j < l.length) :
    (l.map f).getD j false = f (nthN l j) := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => simp [nthN_zero]
    | succ j =>
      simp only [List.map_cons, List.getD_cons_succ]
      rw [nthN_succ]; exact ih j (by simp at hj; omega)

/-! ## Checker invariants -/

theorem sig_flip (g : Aig) (ρ : Nat → Bool) (e : Env) (x : Nat) :
    sig g ρ e (2 * x + 1) = !sig g ρ e (2 * x) := by
  unfold sig
  rw [show (2 * x + 1) / 2 = x by omega, show 2 * x / 2 = x by omega,
    show (2 * x + 1) % 2 = 1 by omega, show 2 * x % 2 = 0 by omega]
  simp

theorem sig_bound (g : Aig) (ρ : Nat → Bool) (e : Env) {n b : Nat}
    (h : e.bind.get e.nd n = some b) :
    sig g ρ e (2 * n) = g.litVal ρ b := by
  unfold sig; rw [show 2 * n / 2 = n by omega, h, show 2 * n % 2 = 0 by omega]; simp

theorem RulesOk.set {w : Nat} {σ : Nat → Bool} {e : Env} {rules : Tree Poly}
    (h : RulesOk w σ e rules) {o : Nat} {Q : Poly} (hQ : bv w (σ (2 * o)) = evalP w σ Q) :
    RulesOk w σ e (rules.set e.nd o Q) := by
  intro v Q' hv
  rcases Tree.get_set hv with ⟨rfl, rfl⟩ | hv
  · exact hQ
  · exact h v Q' hv

/-! ## Gates -/

section gates
variable {w : Nat} (g : Aig) (ρ : Nat → Bool) (e : Env) (hM : e.M = 2 ^ w)
  (hT : e.andT = andTree e.ad g.I g.ands)

include hM in
theorem install_ok {σ : Nat → Bool} (env : List (Nat × Nat)) (rows : Nat) (pr : Pairs)
    (hpr : PairsOk σ pr) (t : Nat) (ht : t < rows) (henv : ∀ x ∈ env, x.2.testBit t = σ x.1) :
    ∀ (outs : List Nat) (Qs : List Poly) (tabs : List Nat) (rules rules' : Tree Poly),
      (∀ i, i < outs.length → i < tabs.length → (nthN tabs i).testBit t = σ (2 * nthN outs i)) →
      install e env rows pr outs Qs tabs rules = some rules' → RulesOk w σ e rules →
      RulesOk w σ e rules' := by
  intro outs
  induction outs with
  | nil => intro Qs tabs rules rules' _ h hr; cases h; exact hr
  | cons o os ih =>
    intro Qs tabs rules rules' hout h hr
    unfold install at h; dsimp only at h
    cases Qs with
    | nil => cases h
    | cons Q Qs =>
      cases tabs with
      | nil => cases h
      | cons tab tabs =>
        dsimp only at h
        cases hv : validate e.M env rows Q tab
        · rw [hv] at h; cases h
        · rw [hv] at h; simp only [brec_true] at h
          refine ih Qs tabs _ rules' (fun i hi hi' => ?_) h (hr.set ?_)
          · have := hout (i + 1) (by simp; omega) (by simp; omega)
            rwa [nthN_succ, nthN_succ] at this
          · rw [normP_eval _ (van_ok pr hpr), validate_ok e.M hM env rows Q tab hv t ht henv]
            have := hout 0 (by simp) (by simp)
            rw [nthN_zero, nthN_zero] at this
            rw [this]

include hM in
theorem gateFinish_ok {σ : Nat → Bool} (st : GS) (kind : Nat) (outs ins : List Nat) (rows : Nat)
    (tin tabs ws : List Nat) (kont : GS → List Nat → Bool) (hinv : GInv w σ e st) (t : Nat)
    (ht : t < rows) (hin : ∀ y ∈ zipEnv ins tin, y.2.testBit t = σ y.1)
    (hout : ∀ i, i < outs.length → i < tabs.length →
      (nthN tabs i).testBit t = σ (2 * nthN outs i))
    (hlen : outs.length = nOut kind) (htl : tabs.length = outs.length)
    (h : gateFinish e st kind outs ins rows tin tabs ws kont false = true) :
    ∃ st' ws', GInv w σ e st' ∧ kont st' ws' = true := by
  have hn1 : 1 ≤ nOut kind := by
    unfold nOut; cases Nat.beq kind 6 <;> cases Nat.beq kind 7 <;> simp
  have h0 : (nthN tabs 0).testBit t = σ (2 * nthN outs 0) := hout 0 (by omega) (by omega)
  have henv : ∀ x ∈ (Bool.rec (zipEnv ins tin)
      ((Nat.mul 2 (nthN outs 0), nthN tabs 0) :: zipEnv ins tin)
      (Nat.ble 6 kind) : List (Nat × Nat)), x.2.testBit t = σ x.1 := by
    cases Nat.ble 6 kind
    · exact hin
    · intro x hx
      simp only [brec_true, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact h0
      · exact hin x hx
  unfold gateFinish at h
  obtain ⟨rules', hins, h⟩ := orec_true h
  have hr' :=
    install_ok e hM _ rows st.pr hinv.2 t ht henv outs _ tabs st.rules rules' hout hins hinv.1
  cases hk : Nat.beq kind 6
  · rw [hk] at h; simp only [brec_false] at h; exact ⟨⟨rules', st.pr⟩, ws, ⟨hr', hinv.2⟩, h⟩
  · rw [hk] at h; simp only [brec_true] at h
    obtain ⟨hz, h⟩ := band_true h
    refine ⟨_, _, ⟨hr', ?_⟩, h⟩
    have h2 : outs.length = 2 := by rw [hlen, beq_true.mp hk]; rfl
    have h1 : (nthN tabs 1).testBit t = σ (2 * nthN outs 1) := hout 1 (by omega) (by omega)
    intro c s hcs
    rcases Tree.get_set hcs with ⟨rfl, rfl⟩ | hcs
    · intro ⟨hc, hs⟩
      have : (Nat.land (nthN tabs 0) (nthN tabs 1)).testBit t = true := by
        show (nthN tabs 0 &&& nthN tabs 1).testBit t = true
        rw [Nat.testBit_and, h0, h1, hc, hs]; rfl
      rw [beq_true.mp hz] at this; simp at this
    · exact hinv.2 c s hcs

theorem nIn_le (kind : Nat) : nIn kind ≤ 3 := by
  unfold nIn; cases Nat.beq kind 4 <;> cases Nat.beq kind 5 <;> cases Nat.beq kind 7 <;> simp

theorem full_bit (k t : Nat) (ht : t < 2 ^ k) :
    (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1).testBit t = true := by
  show (2 ^ (2 ^ k) - 1).testBit t = true
  rw [Nat.testBit_two_pow_sub_one]; simpa using ht

include hM hT in
theorem gateBody_ok (st : GS) (kind : Nat) (expl : Bool) (outs ins lits : List Nat) (k : Nat)
    (ws : List Nat) (kont : GS → List Nat → Bool) (hinv : GInv w (sig g ρ e) e st)
    (hk : k ≤ 6) (hlits : lits.length = k)
    (hdef : expl = false → ins.length = k ∧
      ∀ i, i < ins.length → e.bind.get e.nd (Nat.shiftRight (nthN ins i) 1) = some (nthN lits i))
    (hlen : outs.length = nOut kind)
    (h : gateBody e st kind expl outs ins lits k ws kont false = true) :
    ∃ st' ws', GInv w (sig g ρ e) e st' ∧ kont st' ws' = true := by
  unfold gateBody at h
  obtain ⟨-, h⟩ := band_true h
  obtain ⟨leaves, hL, h⟩ := orec_true h
  -- the row of the assignment ρ
  let t := tOf (lits.map (g.litVal ρ))
  have ht : t < 2 ^ k := by have := tOf_lt (lits.map (g.litVal ρ)); simpa [hlits] using this
  have hfull := full_bit k t ht
  have h64 : t < 64 := Nat.lt_of_lt_of_le ht (by
    calc 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hk
      _ = 64 := by decide)
  have hrow : ∀ j, j < k → (Nat.land (xmask j) (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1)).testBit t =
      g.litVal ρ (nthN lits j) := by
    intro j hj
    show (xmask j &&& _).testBit t = _
    rw [Nat.testBit_and, hfull, xmask_bit j t (by omega) h64, Bool.and_true]
    show (tOf (lits.map (g.litVal ρ))).testBit j = _
    rw [tOf_bit, getD_map_nthN _ _ _ (by omega)]
  have hl : ∀ x ∈ leaves, x.2.testBit t = g.nodeVal ρ x.1 := by
    intro x hx
    rcases mkLeaves_spec _ lits 0 [] leaves hL x hx with hx | ⟨i, hi, rfl⟩
    · simp at hx
    · simp only
      rw [cmpl_bit hfull, Nat.zero_add, hrow i (by omega), shiftRight_one]
      unfold Aig.litVal; simp
  obtain ⟨tin, htin, h⟩ := orec_true h
  have hin : ∀ y ∈ zipEnv ins tin, y.2.testBit t = sig g ρ e y.1 := by
    intro y hy
    obtain ⟨i, hi, hi', rfl⟩ := zipEnv_spec ins tin y hy
    cases expl with
    | false =>
      obtain ⟨hik, hb⟩ := hdef rfl
      simp only [brec_false] at htin; cases htin
      obtain ⟨-, hn⟩ := tinDef_spec (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1) ins 0
      show (nthN (tinDef _ ins) i).testBit t = sig g ρ e (2 * Nat.shiftRight (nthN ins i) 1)
      unfold tinDef; rw [hn i hi, Nat.zero_add, hrow i (by omega), sig_bound g ρ e (hb i hi)]
    | true =>
      simp only [brec_true] at htin
      obtain ⟨hl', hb⟩ := ttAll_spec e _ leaves (netsOf ins) tin htin
      obtain ⟨hnl, hn⟩ := netsOf_spec ins
      obtain ⟨b, hb1, hb2⟩ := hb i (by omega)
      rw [hn i hi] at hb1
      show (nthN tin i).testBit t = sig g ρ e (2 * Nat.shiftRight (nthN ins i) 1)
      rw [tt_ok g ρ e hT _ t hfull leaves hl b _ hb2, sig_bound g ρ e hb1]
  obtain ⟨tabs, htabs, h⟩ := orec_true h
  obtain ⟨htl, htb⟩ := ttAll_spec e _ leaves outs tabs htabs
  have hout : ∀ i, i < outs.length → i < tabs.length →
      (nthN tabs i).testBit t = sig g ρ e (2 * nthN outs i) := by
    intro i hi _
    obtain ⟨b, hb1, hb2⟩ := htb i hi
    rw [tt_ok g ρ e hT _ t hfull leaves hl b _ hb2, sig_bound g ρ e hb1]
  exact gateFinish_ok e hM st kind outs ins _ tin tabs ws kont hinv t ht hin hout hlen htl h

include hM hT in
theorem gateStep_ok (st : GS) (ws : List Nat) (kont : GS → List Nat → Bool)
    (hinv : GInv w (sig g ρ e) e st) (h : gateStep e st ws kont false = true) :
    ∃ st' ws', GInv w (sig g ρ e) e st' ∧ kont st' ws' = true := by
  unfold gateStep at h
  obtain ⟨kraw, ws1, -, h⟩ := rd_true h
  obtain ⟨-, h⟩ := band_true h
  obtain ⟨outs, ws2, hlo, h⟩ := rdN_true h
  obtain ⟨ins, ws3, hli, h⟩ := rdN_true h
  obtain ⟨bl, hbl, h⟩ := orec_true h
  obtain ⟨hbll, hbb⟩ := binds_spec e ins bl hbl
  cases h8 : tb kraw 8
  · rw [h8] at h; simp only [brec_false] at h
    exact gateBody_ok g ρ e hM hT st _ false outs ins bl _ ws3 kont hinv
      (Nat.le_trans (nIn_le _) (by decide)) (by omega) (fun _ => ⟨hli, hbb⟩) hlo h
  · rw [h8] at h; simp only [brec_true] at h
    obtain ⟨nl, ws4, -, h⟩ := rd_true h
    obtain ⟨hnl, h⟩ := band_true h
    obtain ⟨lv, ws5, hlv, h⟩ := rdN_true h
    obtain ⟨-, h⟩ := band_true h
    have hnl6 : nl ≤ 6 := by
      cases h1 : Nat.ble 1 nl <;> rw [h1] at hnl <;> simp only [brec_false, brec_true] at hnl
      · cases hnl
      · exact ble_true.mp hnl
    exact gateBody_ok g ρ e hM hT st _ true outs ins lv nl ws5 kont hinv hnl6 hlv
      (fun h => by cases h) hlo h

include hM hT in
theorem gates_ok (kont : GS → List Nat → Bool) (n : Nat) :
    ∀ st ws, GInv w (sig g ρ e) e st → gates e false kont n st ws = true →
      ∃ st' ws', GInv w (sig g ρ e) e st' ∧ kont st' ws' = true := by
  induction n with
  | zero => intro st ws hinv h; exact ⟨st, ws, hinv, h⟩
  | succ n ih =>
    intro st ws hinv h
    obtain ⟨st', ws', hinv', h'⟩ := gateStep_ok g ρ e hM hT st ws _ hinv h
    exact ih st' ws' hinv' h'

end gates

/-! ## Cones -/

section cones
variable {w : Nat} {σ : Nat → Bool} (e : Env) (hM : e.M = 2 ^ w)

include hM in
theorem coneVars_ok (pr : Pairs) (hpr : PairsOk σ pr) (root : Nat) (rules : Tree Poly)
    (hr : RulesOk w σ e rules) (kont : Poly → List Nat → Bool) (k : Nat) :
    ∀ r ws, bv w (σ (2 * root)) = evalP w σ r → coneVars e pr root rules k r ws kont = true →
      ∃ r' ws', bv w (σ (2 * root)) = evalP w σ r' ∧ kont r' ws' = true := by
  induction k with
  | zero => intro r ws hr0 h; exact ⟨r, ws, hr0, h⟩
  | succ k ih =>
    intro r ws hr0 h
    change rd ws false (fun v ws => Option.rec false
      (fun Rv => Bool.rec (coneVars e pr root rules k
          (normP (van pr) (substP e.M (van pr) (Nat.mul 2 v) Rv r)) ws kont) false (Nat.beq v root))
      (rules.get e.nd v)) = true at h
    obtain ⟨v, ws', -, h⟩ := rd_true h
    obtain ⟨Rv, hRv, h⟩ := orec_true h
    cases hb : Nat.beq v root
    · rw [hb] at h; simp only [brec_false] at h
      refine ih _ ws' ?_ h
      rw [normP_eval _ (van_ok pr hpr),
        substP_eval e.M hM _ (van_ok pr hpr) (Nat.mul 2 v) Rv r (hr v Rv hRv)]
      exact hr0
    · rw [hb] at h; cases h

include hM in
theorem cones_ok (kont : GS → List Nat → Bool) (n : Nat) :
    ∀ st ws, GInv w σ e st → cones e kont n st ws = true →
      ∃ st' ws', GInv w σ e st' ∧ kont st' ws' = true := by
  induction n with
  | zero => intro st ws hinv h; exact ⟨st, ws, hinv, h⟩
  | succ n ih =>
    intro st ws hinv h
    change rd ws false (fun root ws => rd ws false fun kk ws =>
        Option.rec false
          (fun r => coneVars e st.pr root st.rules kk r ws
            (fun r' ws => cones e kont n ⟨st.rules.set e.nd root r', st.pr⟩ ws))
          (st.rules.get e.nd root)) = true at h
    obtain ⟨root, ws1, -, h⟩ := rd_true h
    obtain ⟨kk, ws2, -, h⟩ := rd_true h
    obtain ⟨r, hr, h⟩ := orec_true h
    obtain ⟨r', ws3, hr', h⟩ :=
      coneVars_ok e hM st.pr hinv.2 root st.rules hinv.1 _ kk r ws2 (hinv.1 root r hr) h
    exact ih ⟨st.rules.set e.nd root r', st.pr⟩ ws3 ⟨hinv.1.set hr', hinv.2⟩ h

end cones

/-! ## Main reduction -/

theorem bv_not (w : Nat) (b : Bool) : bv w (!b) = 1 - bv w b := by
  cases b <;> simp [bv]

section main
variable {w : Nat} {σ : Nat → Bool} (e : Env) (hM : e.M = 2 ^ w)
  (hflip : ∀ x, σ (2 * x + 1) = !σ (2 * x))

include hM hflip in
theorem mainLoop_ok (pr : Pairs) (hpr : PairsOk σ pr) (rules : Tree Poly) (hr : RulesOk w σ e rules)
    (nNets : Nat) (X : BitVec w) (n : Nat) :
    ∀ P fl ws, evalP w σ P = X → mainLoop e pr rules nNets n P fl ws = true → X = 0 := by
  induction n with
  | zero =>
    intro P fl ws hP h
    change (Bool.rec false (isNil P) (List.rec true (fun _ _ _ => false) ws) : Bool) = true at h
    obtain ⟨-, h⟩ := band_true h
    rw [← hP, isNil_eval P h]
  | succ n ih =>
    intro P fl ws hP h
    change rd ws false (fun op ws =>
        Bool.rec
          (Option.rec false
            (fun R0 =>
              Bool.rec
                (mainLoop e pr rules nNets n (substP e.M (van pr) (Nat.mul 2 (Nat.shiftRight op 1))
                    (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0) P) fl ws)
                (mainLoop e pr rules nNets n
                    (substP e.M (van pr) (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)
                    (oneSub e.M (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0)) P) fl ws)
                (tb fl (Nat.mul 2 (Nat.shiftRight op 1))))
            (rules.get e.nd (Nat.shiftRight op 1)))
          (Bool.rec
            (mainLoop e pr rules nNets n (substP e.M (van pr) (Nat.mul 2 (Nat.shiftRight op 1))
                (oneSub e.M
                  (single e.M 1 (Nat.pow 2 (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)))) P)
              (Nat.lor fl (Nat.pow 2 (Nat.mul 2 (Nat.shiftRight op 1)))) ws)
            false
            (Bool.rec (tb fl (Nat.mul 2 (Nat.shiftRight op 1))) true
              (Nat.ble nNets (Nat.shiftRight op 1))))
          (Nat.beq (Nat.land op 1) 1)) = true at h
    obtain ⟨op, ws', -, h⟩ := rd_true h
    have hv := van_ok (w := w) pr hpr
    cases hf : Nat.beq (Nat.land op 1) 1
    · rw [hf] at h; simp only [brec_false] at h
      obtain ⟨R0, hR0, h⟩ := orec_true h
      have hR1 : bv w (σ (Nat.mul 2 (Nat.shiftRight op 1))) =
          evalP w σ (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0) := by
        rw [flipR_eval e.M hM hflip]; exact hr _ R0 hR0
      cases hfl : tb fl (Nat.mul 2 (Nat.shiftRight op 1))
      · rw [hfl] at h; simp only [brec_false] at h
        exact ih _ fl ws' (by rw [substP_eval e.M hM _ hv _ _ P hR1]; exact hP) h
      · rw [hfl] at h; simp only [brec_true] at h
        refine ih _ fl ws' ?_ h
        rw [substP_eval e.M hM _ hv _ _ P ?_]; exact hP
        show bv w (σ (2 * Nat.shiftRight op 1 + 1)) = _
        rw [hflip, bv_not, oneSub_eval e.M hM, ← hR1]; rfl
    · rw [hf] at h; simp only [brec_true] at h
      cases hc : (Bool.rec (tb fl (Nat.mul 2 (Nat.shiftRight op 1))) true
          (Nat.ble nNets (Nat.shiftRight op 1)) : Bool)
      · rw [hc] at h; simp only [brec_false] at h
        refine ih _ _ ws' ?_ h
        rw [substP_eval e.M hM _ hv _ _ P (flipPoly_eval e.M hM hflip _).symm]; exact hP
      · rw [hc] at h; cases h

end main

/-! ## Spec word lemmas -/

theorem bv_toNat (w : Nat) (b : Bool) : BitVec.ofNat w b.toNat = bv w b := by
  cases b <;> simp [bv]

theorem bv_toNat_int (w : Nat) (b : Bool) : BitVec.ofInt w (b.toNat : Int) = bv w b := by
  cases b <;> simp [bv]

theorem outSum_eq {w : Nat} {σ : Nat → Bool} (g : Aig) (ρ : Nat → Bool) (refs : List Nat) :
    ∀ j, (∀ k, k < refs.length →
        (σ (2 * (nthN refs k / 2)) ^^ (nthN refs k % 2 == 1)) =
          g.litVal ρ (g.outs.getD (j + k) 0)) →
      outSum w σ refs j = BitVec.ofNat w (outWordL g ρ (List.range' j refs.length)) := by
  induction refs with
  | nil => intro j _; simp [outSum, outWordL]
  | cons r rs ih =>
    intro j hk
    rw [List.length_cons, List.range'_succ, outSum, outWordL, ih (j + 1) (fun k hk' => by
      have := hk (k + 1) (by simp; omega); rw [nthN_succ] at this
      rw [this, show j + (k + 1) = j + 1 + k by omega])]
    have h0 := hk 0 (by simp); rw [nthN_zero, Nat.add_zero] at h0
    rw [h0, BitVec.ofNat_add, BitVec.ofNat_mul, bv_toNat]

theorem inSum_eq {w : Nat} {σ : Nat → Bool} (signed : Bool) (n : Nat) (ρ : Nat → Bool) (off : Nat)
    (xs : List Nat) : ∀ i, (∀ k, k < xs.length → σ (2 * nthN xs k) = ρ (off + (i + k))) →
      inSum w σ signed n xs i =
        BitVec.ofInt w (inWordL signed n ρ off (List.range' i xs.length)) := by
  induction xs with
  | nil => intro i _; simp [inSum, inWordL]
  | cons x xs ih =>
    intro i hk
    rw [List.length_cons, List.range'_succ, inSum, inWordL, ih (i + 1) (fun k hk' => by
      have := hk (k + 1) (by simp; omega); rw [nthN_succ] at this
      rw [this, show i + (k + 1) = i + 1 + k by omega])]
    have h0 := hk 0 (by simp); rw [nthN_zero, Nat.add_zero] at h0
    rw [h0, BitVec.ofInt_add, BitVec.ofInt_mul, bv_toNat_int]
    congr 2
    by_cases hc : signed = true ∧ i + 1 = n
    · simp only [hc, and_self, ↓reduceIte, BitVec.ofInt_neg,
        show ((2:Int) ^ i) = ((2 ^ i : Nat) : Int) by simp, BitVec.ofInt_natCast]
    · simp only [hc, ↓reduceIte,
        show ((2:Int) ^ i) = ((2 ^ i : Nat) : Int) by simp, BitVec.ofInt_natCast]

/-! ## Section lemmas -/

theorem len_eq (l : List Nat) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => show Nat.succ (len l) = _; rw [ih]; rfl

theorem inOk_spec (e : Env) (nNets : Nat) (inNet : List Nat) : ∀ j,
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun x _ ih i =>
        Bool.rec false
          (Option.rec false
            (fun b => Bool.rec false (ih (Nat.succ i)) (Nat.beq b (Nat.mul 2 (Nat.succ i))))
            (e.bind.get e.nd x))
          (Nat.ble (Nat.succ x) nNets))
      inNet j) = true →
    ∀ k, k < inNet.length → e.bind.get e.nd (nthN inNet k) = some (2 * (j + k + 1)) := by
  induction inNet with
  | nil => intro j _ k hk; simp at hk
  | cons x xs ih =>
    intro j h k hk
    dsimp only at h
    obtain ⟨-, h⟩ := band_true h
    obtain ⟨b, hb, h⟩ := orec_true h
    obtain ⟨hb2, h⟩ := band_true h
    cases k with
    | zero => rw [nthN_zero, hb, beq_true.mp hb2]; rfl
    | succ k =>
      rw [nthN_succ, ih _ h k (by simp at hk; omega)]; congr 2; omega

theorem outOkAll_spec (e : Env) (nNets : Nat) (outRef : List Nat) : ∀ aouts,
    outOkAll e nNets outRef aouts = true →
    ∀ k, k < outRef.length → k < aouts.length ∧
      ∃ b, e.bind.get e.nd (Nat.shiftRight (nthN outRef k) 1) = some b ∧
      Nat.xor b (Nat.land (nthN outRef k) 1) = nthN aouts k := by
  induction outRef with
  | nil => intro _ _ k hk; simp at hk
  | cons r rs ih =>
    intro aouts h k hk
    unfold outOkAll at h; dsimp only at h
    cases aouts with
    | nil => cases h
    | cons a ao =>
      dsimp only at h
      obtain ⟨-, h⟩ := band_true h
      obtain ⟨b, hb, h⟩ := orec_true h
      obtain ⟨hb2, h⟩ := band_true h
      cases k with
      | zero => exact ⟨by simp, b, hb, beq_true.mp hb2⟩
      | succ k =>
        obtain ⟨h1, h2⟩ := ih ao (by unfold outOkAll; exact h) k (by simp at hk; omega)
        exact ⟨by simp; omega, h2⟩

theorem takeN_spec (n : Nat) : ∀ (l : List Nat), n ≤ l.length →
    (takeN n l).length = n ∧ ∀ k, k < n → nthN (takeN n l) k = nthN l k := by
  induction n with
  | zero => intro l _; exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp at hl
    | cons a l =>
      obtain ⟨h1, h2⟩ := ih l (by simp at hl; omega)
      refine ⟨by show (a :: takeN n l).length = _; simp [h1], ?_⟩
      intro k hk
      cases k with
      | zero => rfl
      | succ k => exact h2 k (by omega)

theorem dropN_spec (n : Nat) : ∀ (l : List Nat),
    (dropN n l).length = l.length - n ∧ ∀ k, nthN (dropN n l) k = nthN l (n + k) := by
  induction n with
  | zero => intro l; exact ⟨by show l.length = l.length - 0; simp, fun k => by
      show nthN l k = nthN l (0 + k); rw [Nat.zero_add]⟩
  | succ n ih =>
    intro l
    cases l with
    | nil => exact ⟨by show (0:Nat) = 0 - (n + 1); omega, fun k => rfl⟩
    | cons a l =>
      obtain ⟨h1, h2⟩ := ih l
      refine ⟨by show (dropN n l).length = _; simp [h1], fun k => ?_⟩
      show nthN (dropN n l) k = _
      rw [h2, show n + 1 + k = (n + k) + 1 by omega, nthN_succ]

theorem xor1_div (b : Nat) : (b ^^^ 1) / 2 = b / 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_div_two, Nat.testBit_div_two, Nat.testBit_xor]
  have : (1:Nat).testBit (i+1) = false := by rw [Nat.testBit_add_one]; simp
  rw [this, Bool.xor_false]

theorem xor1_mod (b : Nat) : (b ^^^ 1) % 2 = 1 - b % 2 := by
  have h := Nat.testBit_xor b 1 0
  rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at h
  have h1 : (b ^^^ 1) % 2 < 2 := Nat.mod_lt _ (by decide)
  have h2 : b % 2 < 2 := Nat.mod_lt _ (by decide)
  revert h h1 h2; generalize (b ^^^ 1) % 2 = x; generalize b % 2 = y
  intro h h1 h2
  have hx : x = 0 ∨ x = 1 := by omega
  have hy : y = 0 ∨ y = 1 := by omega
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

theorem litVal_xor (g : Aig) (ρ : Nat → Bool) (b r : Nat) :
    g.litVal ρ (Nat.xor b (Nat.land r 1)) = (g.litVal ρ b ^^ (r % 2 == 1)) := by
  unfold Aig.litVal
  rw [land_one]
  have hr : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hr with hr | hr <;> rw [hr]
  · rw [show Nat.xor b 0 = b from Nat.xor_zero b]; simp
  · rw [show Nat.xor b 1 = b ^^^ 1 from rfl, xor1_div, xor1_mod]
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hb with hb | hb <;> rw [hb] <;> simp

theorem litVal_pi (g : Aig) (ρ : Nat → Bool) (i : Nat) (hi : i < g.I) :
    g.litVal ρ (2 * (i + 1)) = ρ i := by
  unfold Aig.litVal
  rw [show 2 * (i + 1) / 2 = i + 1 by omega, show 2 * (i + 1) % 2 = 0 by omega,
    Aig.nodeVal_pi g ρ (i + 1) (by omega) (by omega)]
  simp

/-! ## Main theorem -/

theorem checkWords_sound (signed : Bool) (g : Aig) (ws0 : List Nat)
    (h : checkWords signed g ws0 = true) : ∀ ρ : Nat → Bool,
      BitVec.ofNat g.outs.length (outWord g ρ) =
        BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ 0) *
        BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ (g.I / 2)) := by
  intro ρ
  unfold checkWords at h
  obtain ⟨hd, ws1, hhl, h⟩ := rdN_true h
  obtain ⟨hhdr, h⟩ := band_true h
  obtain ⟨bindW, ws2, -, h⟩ := rdN_true h
  obtain ⟨bt, -, h⟩ := orec_true h
  unfold afterBind at h
  obtain ⟨inNet, ws3, hinl, h⟩ := rdN_true h
  obtain ⟨outRef, ws4, houtl, h⟩ := rdN_true h
  obtain ⟨hio, h⟩ := band_true h
  obtain ⟨hin, hout⟩ := band_true hio
  -- header facts
  unfold headerOk at hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨hI, hhdr⟩ := band_true hhdr
  obtain ⟨hI, hev⟩ := band_true hI
  obtain ⟨hO, -⟩ := band_true hhdr
  rw [beq_true] at hI hO hev
  rw [len_eq] at hO
  -- environment
  generalize hw : g.outs.length = w at hO
  let e : Env := ⟨Nat.pow 2 (nthN hd 4), g.M, g.I, bitLen g.M, andTree (bitLen g.M) g.I g.ands,
    bitLen (nthN hd 5), bt⟩
  have hM : e.M = 2 ^ w := by show Nat.pow 2 (nthN hd 4) = 2 ^ w; rw [hO]; rfl
  have hT : e.andT = andTree e.ad g.I g.ands := rfl
  -- phases
  unfold runPhases at h
  have hinit : GInv w (sig g ρ e) e ⟨Tree.empty, ⟨e.nd, Tree.empty, 0⟩⟩ :=
    ⟨fun v Q hv => by simp [Tree.get_empty] at hv, fun c s hcs => by simp [Tree.get_empty] at hcs⟩
  obtain ⟨st, ws5, hst, h⟩ := gates_ok g ρ e hM hT _ _ _ ws4 hinit h
  obtain ⟨st', ws6, hst', h⟩ := cones_ok e hM _ _ st ws5 hst h
  have hP := mainLoop_ok e hM (sig_flip g ρ e) st'.pr hst'.2 st'.rules hst'.1 _ _ _ _ 0 ws6 rfl h
  rw [initP_eval e.M hM st'.pr (van_ok st'.pr hst'.2)] at hP
  -- relate the sums to the spec words
  have hn : Nat.shiftRight (nthN hd 3) 1 = g.I / 2 := by rw [shiftRight_one, hI]
  rw [hn] at hP
  have hinl' : inNet.length = g.I := by rw [hinl, hI]
  have hev' : g.I % 2 = 0 := by rw [← hI, ← land_one]; exact hev
  have hinb := inOk_spec e (nthN hd 5) inNet 0 hin
  obtain ⟨htl, htn⟩ := takeN_spec (g.I / 2) inNet (by omega)
  obtain ⟨hdl, hdn⟩ := dropN_spec (g.I / 2) inNet
  have hA : inSum w (sig g ρ e) signed (g.I / 2) (takeN (g.I / 2) inNet) 0 =
      BitVec.ofInt w (inWord signed (g.I / 2) ρ 0) := by
    rw [inSum_eq signed (g.I / 2) ρ 0 _ 0 (fun k hk => ?_), htl]
    · unfold inWord; rw [List.range_eq_range']
    · rw [htl] at hk
      rw [htn k hk, sig_bound g ρ e (hinb k (by omega)), Nat.zero_add, Nat.zero_add,
        litVal_pi g ρ k (by omega)]
  have hB : inSum w (sig g ρ e) signed (g.I / 2) (dropN (g.I / 2) inNet) 0 =
      BitVec.ofInt w (inWord signed (g.I / 2) ρ (g.I / 2)) := by
    rw [inSum_eq signed (g.I / 2) ρ (g.I / 2) _ 0 (fun k hk => ?_), hdl,
      show inNet.length - g.I / 2 = g.I / 2 by omega]
    · unfold inWord; rw [List.range_eq_range']
    · rw [hdl] at hk
      rw [hdn k, sig_bound g ρ e (hinb (g.I / 2 + k) (by omega)), Nat.zero_add, Nat.zero_add,
        litVal_pi g ρ _ (by omega)]
  have hob := outOkAll_spec e (nthN hd 5) outRef g.outs hout
  have hC : outSum w (sig g ρ e) outRef 0 = BitVec.ofNat w (outWord g ρ) := by
    rw [outSum_eq g ρ outRef 0 (fun k hk => ?_)]
    · unfold outWord; rw [hw, houtl, hO, List.range_eq_range']
    · obtain ⟨-, b, hb1, hb2⟩ := hob k hk
      have hb1' : e.bind.get e.nd (nthN outRef k / 2) = some b := by
        rw [← shiftRight_one]; exact hb1
      rw [sig_bound g ρ e hb1', Nat.zero_add, ← litVal_xor, hb2, nthN_eq_getD]
  rw [hA, hB, hC] at hP
  have := congrArg (· + BitVec.ofInt w (inWord signed (g.I / 2) ρ 0) *
    BitVec.ofInt w (inWord signed (g.I / 2) ρ (g.I / 2))) hP
  simp only [BitVec.sub_add_cancel] at this
  rw [this]; exact BitVec.zero_add _

theorem checkArt_sound (signed : Bool) (aigN aigLen artN artLen : Nat)
    (h : checkArt signed aigN aigLen artN artLen = true) :
    ∃ g, parseAig (toBytes aigN aigLen) = some g ∧ ∀ ρ : Nat → Bool,
      BitVec.ofNat g.outs.length (outWord g ρ) =
        BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ 0) *
        BitVec.ofInt g.outs.length (inWord signed (g.I / 2) ρ (g.I / 2)) := by
  unfold checkArt at h
  obtain ⟨g, hg, h⟩ := orec_true h
  obtain ⟨-, h⟩ := band_true h
  exact ⟨g, hg, checkWords_sound signed g _ h⟩

/-! ## ART v1.5 Miter Soundness (`SPEC_MITER`, `spec = 2`) -/

theorem litVal_const (g : Aig) (ρ : Nat → Bool) (a : Nat) (ha : a ≤ 1) :
    g.litVal ρ a = (a == 1) := by
  cases a with
  | zero =>
    unfold Aig.litVal Aig.nodeVal
    simp
  | succ a' =>
    have : a' = 0 := by omega
    subst this
    unfold Aig.litVal Aig.nodeVal
    simp

theorem outOkMiter_spec (e : Env) (nNets : Nat) (outRef : List Nat) : ∀ aouts,
    outOkMiter e nNets outRef aouts = true →
    ∀ k, k < outRef.length → k < aouts.length ∧
      ((nthN outRef k = UNB ∧ nthN aouts k ≤ 1) ∨
        (nthN outRef k ≠ UNB ∧ ∃ b,
          e.bind.get e.nd (Nat.shiftRight (nthN outRef k) 1) = some b ∧
          Nat.xor b (Nat.land (nthN outRef k) 1) = nthN aouts k)) := by
  induction outRef with
  | nil => intro _ _ k hk; simp at hk
  | cons r rs ih =>
    intro aouts h k hk
    unfold outOkMiter at h; dsimp only at h
    cases aouts with
    | nil => cases h
    | cons a ao =>
      dsimp only at h
      cases hru : Nat.beq r UNB
      · rw [hru] at h; simp only [brec_false] at h
        obtain ⟨-, h⟩ := band_true h
        obtain ⟨b, hb, h⟩ := orec_true h
        obtain ⟨hb2, h⟩ := band_true h
        cases k with
        | zero =>
          refine ⟨by simp, Or.inr ⟨Nat.ne_of_beq_eq_false hru, b, hb, beq_true.mp hb2⟩⟩
        | succ k =>
          obtain ⟨h1, h2⟩ := ih ao (by unfold outOkMiter; exact h) k (by simp at hk; omega)
          exact ⟨by simp; omega, h2⟩
      · rw [hru] at h; simp only [brec_true] at h
        obtain ⟨ha1, h⟩ := band_true h
        cases k with
        | zero =>
          exact ⟨by simp, Or.inl ⟨beq_true.mp hru, ble_true.mp ha1⟩⟩
        | succ k =>
          obtain ⟨h1, h2⟩ := ih ao (by unfold outOkMiter; exact h) k (by simp at hk; omega)
          exact ⟨by simp; omega, h2⟩

theorem miterTerm_eval {w : Nat} (g : Aig) (ρ : Nat → Bool) (e : Env) (hM : e.M = 2 ^ w)
    (neg : Bool) (rules : Tree Poly) (r a j : Nat)
    (hok : (r = UNB ∧ a ≤ 1) ∨ (r ≠ UNB ∧ ∃ b,
      e.bind.get e.nd (Nat.shiftRight r 1) = some b ∧ Nat.xor b (Nat.land r 1) = a)) :
    evalP w (sig g ρ e) (miterTerm e.M neg rules e.nd r a j) =
      (if neg then -BitVec.ofNat w (2 ^ j) else BitVec.ofNat w (2 ^ j)) *
        bv w (g.litVal ρ a) := by
  have hcw : BitVec.ofNat w (Bool.rec (Nat.pow 2 j) (negC e.M (Nat.pow 2 j)) neg) =
      if neg then -BitVec.ofNat w (2 ^ j) else BitVec.ofNat w (2 ^ j) := by
    cases neg
    · simp
    · simp only [brec_true, ↓reduceIte]; exact negC_ofNat e.M (Nat.pow 2 j) hM
  unfold miterTerm
  dsimp only
  have hcond : ∀ hc : (Bool.rec (Bool.rec false
      (Option.rec true (fun _ => false) (rules.get e.nd (Nat.shiftRight r 1)))
      (Nat.ble a 1)) true (Nat.beq r UNB) : Bool) = true, a ≤ 1 := by
    intro hc
    cases hr : Nat.beq r UNB
    · rw [hr] at hc; simp only [brec_false] at hc
      cases ha : Nat.ble a 1
      · rw [ha] at hc; cases hc
      · exact ble_true.mp ha
    · rcases hok with ⟨-, ha⟩ | ⟨hne, _⟩
      · exact ha
      · exact absurd (beq_true.mp hr) hne
  cases hc : (Bool.rec (Bool.rec false
      (Option.rec true (fun _ => false) (rules.get e.nd (Nat.shiftRight r 1)))
      (Nat.ble a 1)) true (Nat.beq r UNB) : Bool)
  · simp only [brec_false]
    rcases hok with ⟨hr, _⟩ | ⟨_, b, hb1, hb2⟩
    · rw [hr] at hc; cases hc
    · rw [scaleP_eval e.M hM, litP_eval e.M hM, hcw]
      have hdiv : Nat.mul 2 (Nat.shiftRight r 1) = 2 * (r / 2) := by
        show 2 * (r >>> 1) = 2 * (r / 2); rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
      have hmod : Nat.land r 1 = r % 2 := Nat.and_one_is_mod r
      have hb1' : e.bind.get e.nd (r / 2) = some b := by rw [← shiftRight_one]; exact hb1
      have hsig : (sig g ρ e (2 * (r / 2)) ^^ (r % 2 == 1)) = g.litVal ρ a := by
        rw [sig_bound g ρ e hb1', ← litVal_xor, hb2]
      rw [hdiv, hmod]
      rcases Nat.mod_two_eq_zero_or_one r with hrm | hrm
      · rw [hrm] at hsig ⊢
        have h0 : Nat.beq 0 1 = false := rfl
        have h0' : ((0 : Nat) == 1) = false := rfl
        rw [h0]; rw [h0', Bool.xor_false] at hsig
        simp only [brec_false, Bool.false_eq_true, ↓reduceIte, hsig]
      · rw [hrm] at hsig ⊢
        have h1 : Nat.beq 1 1 = true := rfl
        rw [h1]; simp only [brec_true]
        rw [← hsig]
        cases sig g ρ e (2 * (r / 2)) <;> simp [bv]
  · simp only [brec_true]
    have ha1 := hcond hc
    rw [litVal_const g ρ a ha1]
    have ha01 : a = 0 ∨ a = 1 := by omega
    rcases ha01 with rfl | rfl
    · have e01 : Nat.beq 0 1 = false := rfl
      rw [e01]; simp [bv]; rfl
    · have e11 : Nat.beq 1 1 = true := rfl
      rw [e11]; simp only [brec_true, beq_self_eq_true]
      rw [single_eval e.M hM, monoVal_zero, hcw]
      simp [bv]

theorem miterHalfGo_eval {w : Nat} (g : Aig) (ρ : Nat → Bool) (e : Env) (hM : e.M = 2 ^ w)
    (neg : Bool) (rules : Tree Poly) (off : Nat) (refs aouts : List Nat) :
    ∀ j, refs.length = aouts.length →
      (∀ k, k < refs.length → nthN aouts k = g.outs.getD (off + j + k) 0) →
      (∀ k, k < refs.length →
        (nthN refs k = UNB ∧ nthN aouts k ≤ 1) ∨
        (nthN refs k ≠ UNB ∧ ∃ b,
          e.bind.get e.nd (Nat.shiftRight (nthN refs k) 1) = some b ∧
          Nat.xor b (Nat.land (nthN refs k) 1) = nthN aouts k)) →
      evalL w (sig g ρ e) (miterHalfGo e.M neg rules e.nd refs aouts j) =
        (if neg then -1 else 1) *
          BitVec.ofNat w (outSliceL g ρ off (List.range' j refs.length)) := by
  induction refs generalizing aouts with
  | nil =>
    intro j hlen _ _
    cases aouts with
    | nil => simp [miterHalfGo, evalL_nil, outSliceL]
    | cons _ _ => simp at hlen
  | cons r rs ih =>
    intro j hlen haout hok
    cases aouts with
    | nil => simp at hlen
    | cons a ao =>
      have hlen' : rs.length = ao.length := by simp at hlen; exact hlen
      have ha0 : a = g.outs.getD (off + j) 0 := by
        have := haout 0 (by simp); simpa [nthN_zero] using this
      have hok0 := hok 0 (by simp)
      simp only [nthN_zero] at hok0
      have htail := ih ao (j + 1) hlen'
        (fun k hk => by
          have := haout (k + 1) (by simp; omega)
          rw [nthN_succ] at this
          rw [this, show off + (j + 1) + k = off + j + (k + 1) by omega])
        (fun k hk => by
          have := hok (k + 1) (by simp; omega)
          rw [nthN_succ, nthN_succ] at this
          exact this)
      have hcons : miterHalfGo e.M neg rules e.nd (r :: rs) (a :: ao) j =
          miterTerm e.M neg rules e.nd r a j ::
            miterHalfGo e.M neg rules e.nd rs ao (j + 1) := rfl
      rw [hcons, evalL_cons, miterTerm_eval g ρ e hM neg rules r a j hok0, htail]
      rw [List.length_cons, List.range'_succ, outSliceL, BitVec.ofNat_add, BitVec.ofNat_mul,
        bv_toNat, ← ha0]
      cases neg <;> grind

theorem initPMiter_eval {w nNets : Nat} (g : Aig) (ρ : Nat → Bool) (e : Env) (hM : e.M = 2 ^ w)
    (pr : Pairs) (hv : VanOk w (sig g ρ e) (van pr)) (rules : Tree Poly) (mw : Nat)
    (outRef : List Nat) (hlen : outRef.length = 2 * mw) (hg : g.outs.length = 2 * mw)
    (hok : outOkMiter e nNets outRef g.outs = true) :
    evalP w (sig g ρ e) (initPMiter e.M pr rules e.nd mw outRef g.outs) =
      BitVec.ofNat w (outSlice g ρ 0 mw) - BitVec.ofNat w (outSlice g ρ mw mw) := by
  have hob := outOkMiter_spec e nNets outRef g.outs hok
  obtain ⟨htr, htr_el⟩ := takeN_spec mw outRef (by omega)
  obtain ⟨hta, hta_el⟩ := takeN_spec mw g.outs (by omega)
  obtain ⟨hdr, hdr_el⟩ := dropN_spec mw outRef
  obtain ⟨hda, hda_el⟩ := dropN_spec mw g.outs
  have h1 : miterHalfTerms e.M false rules e.nd (takeN mw outRef) (takeN mw g.outs) =
      miterHalfGo e.M false rules e.nd (takeN mw outRef) (takeN mw g.outs) 0 := rfl
  have h2 : miterHalfTerms e.M true rules e.nd (dropN mw outRef) (dropN mw g.outs) =
      miterHalfGo e.M true rules e.nd (dropN mw outRef) (dropN mw g.outs) 0 := rfl
  have he1 := miterHalfGo_eval g ρ e hM false rules 0 (takeN mw outRef) (takeN mw g.outs) 0
    (by omega)
    (fun k hk => by rw [hta_el k (by omega), nthN_eq_getD]; simp)
    (fun k hk => by
      rw [htr_el k (by omega), hta_el k (by omega)]
      exact (hob k (by omega)).2)
  have he2 := miterHalfGo_eval g ρ e hM true rules mw (dropN mw outRef) (dropN mw g.outs) 0
    (by omega)
    (fun k hk => by rw [hda_el k, nthN_eq_getD]; simp)
    (fun k hk => by
      rw [hdr_el k, hda_el k]
      exact (hob (mw + k) (by omega)).2)
  unfold initPMiter
  rw [normP_eval _ hv, sumB_eval e.M hM, evalL_append, h1, h2, he1, he2]
  rw [htr, show (dropN mw outRef).length = mw by omega, ← List.range_eq_range']
  unfold outSlice
  grind

theorem checkWordsMiter_sound (g : Aig) (ws0 : List Nat) (h : checkWordsMiter g ws0 = true) :
    g.outs.length % 2 = 0 ∧ 2 ≤ g.outs.length ∧ g.outs.length ≤ 256 ∧
      ∀ ρ : Nat → Bool,
        BitVec.ofNat (g.outs.length / 2) (outSlice g ρ 0 (g.outs.length / 2)) =
          BitVec.ofNat (g.outs.length / 2)
            (outSlice g ρ (g.outs.length / 2) (g.outs.length / 2)) := by
  unfold checkWordsMiter at h
  obtain ⟨hd, ws1, -, h⟩ := rdN_true h
  obtain ⟨hhdr, h⟩ := band_true h
  obtain ⟨bindW, ws2, -, h⟩ := rdN_true h
  obtain ⟨bt, -, h⟩ := orec_true h
  unfold afterBindMiter at h
  obtain ⟨inNet, ws3, -, h⟩ := rdN_true h
  obtain ⟨outRef, ws4, houtl, h⟩ := rdN_true h
  obtain ⟨hio, h⟩ := band_true h
  obtain ⟨-, hout⟩ := band_true hio
  unfold headerMiterOk at hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨-, hhdr⟩ := band_true hhdr
  obtain ⟨hO, hhdr⟩ := band_true hhdr
  obtain ⟨hge2, hhdr⟩ := band_true hhdr
  obtain ⟨hevO, hhdr⟩ := band_true hhdr
  obtain ⟨hle128, -⟩ := band_true hhdr
  rw [beq_true] at hO hevO
  rw [ble_true] at hge2 hle128
  rw [len_eq] at hO
  have hO_even : g.outs.length % 2 = 0 := by
    rw [← hO, ← land_one]; exact hevO
  have hO_ge2 : 2 ≤ g.outs.length := by rw [← hO]; exact hge2
  have hO_le256 : g.outs.length ≤ 256 := by
    have hshr : Nat.shiftRight (nthN hd 4) 1 = nthN hd 4 / 2 := shiftRight_one _
    rw [hshr] at hle128; rw [← hO]; omega
  refine ⟨hO_even, hO_ge2, hO_le256, fun ρ => ?_⟩
  generalize hmw : g.outs.length / 2 = w
  have hmw' : Nat.shiftRight (nthN hd 4) 1 = w := by rw [shiftRight_one, hO, hmw]
  let e : Env := ⟨Nat.pow 2 (Nat.shiftRight (nthN hd 4) 1), g.M, g.I, bitLen g.M,
    andTree (bitLen g.M) g.I g.ands, bitLen (nthN hd 5), bt⟩
  have hM : e.M = 2 ^ w := by show Nat.pow 2 (Nat.shiftRight (nthN hd 4) 1) = 2 ^ w; rw [hmw']; rfl
  have hT : e.andT = andTree e.ad g.I g.ands := rfl
  unfold runPhasesMiter at h
  have hinit : GInv w (sig g ρ e) e ⟨Tree.empty, ⟨e.nd, Tree.empty, 0⟩⟩ :=
    ⟨fun v Q hv => by simp [Tree.get_empty] at hv, fun c s hcs => by simp [Tree.get_empty] at hcs⟩
  obtain ⟨st, ws5, hst, h⟩ := gates_ok g ρ e hM hT _ _ _ ws4 hinit h
  obtain ⟨st', ws6, hst', h⟩ := cones_ok e hM _ _ st ws5 hst h
  have hP := mainLoop_ok e hM (sig_flip g ρ e) st'.pr hst'.2 st'.rules hst'.1 _ _ _ _ 0 ws6 rfl h
  have hP' : evalP w (sig g ρ e) (initPMiter e.M st'.pr st'.rules e.nd w outRef g.outs) = 0 := by
    simpa only [e, hmw'] using hP
  rw [initPMiter_eval (nNets := nthN hd 5) g ρ e hM st'.pr (van_ok st'.pr hst'.2) st'.rules w
    outRef (by rw [houtl, hO]; omega) (by omega) hout] at hP'
  have := congrArg (· + BitVec.ofNat w (outSlice g ρ w w)) hP'
  simp only [BitVec.sub_add_cancel] at this
  rw [this]; exact BitVec.zero_add _

theorem checkArtMiter_sound (aigN aigLen artN artLen : Nat)
    (h : checkArtMiter aigN aigLen artN artLen = true) :
    ∃ g, parseAig (toBytes aigN aigLen) = some g ∧
      g.outs.length % 2 = 0 ∧ 2 ≤ g.outs.length ∧ g.outs.length ≤ 256 ∧
      ∀ ρ : Nat → Bool,
        BitVec.ofNat (g.outs.length / 2) (outSlice g ρ 0 (g.outs.length / 2)) =
          BitVec.ofNat (g.outs.length / 2)
            (outSlice g ρ (g.outs.length / 2) (g.outs.length / 2)) := by
  unfold checkArtMiter at h
  obtain ⟨g, hg, h⟩ := orec_true h
  obtain ⟨-, h⟩ := band_true h
  exact ⟨g, hg, checkWordsMiter_sound g _ h⟩

end

end LeanQbe.T.Examples.Arisca
