module

/-!
# Pure Prefix-Stable Left-Fold AIG Specification (`Bitblast.Ref.Aig`)

Defines the pure functional specification of the C0 append-only AIG:
- `Aig` (`A : Nat`, `nodes : Array (UInt32 × UInt32)`), where node `0` is `false`, nodes `1..A` are
  atoms, and node `A + 1 + i` (`i < nodes.size`) is the AND gate `(nodes[i].1, nodes[i].2)`.
- `Aig.Wf`, `Aig.Extends` (`≤`), `Aig.evalNode`, `Aig.evalLit`, `Aig.evalLit_extend`
- `SliceDenotes` for `BitVec w` slices of AIG literals.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Bitblast.Ref

/-- Append-only AIG with `A` atom nodes (`1..A`) and `nodes.size` AND gates (`A+1 .. A+nodes.size`).
Node `0` is constant `false`; literal `l` encodes `(node = l >>> 1, neg = (l &&& 1) != 0)`. -/
structure Aig where
  A : Nat
  nodes : Array (UInt32 × UInt32)

namespace Aig

/-- Well-formedness: every gate's operands refer strictly to earlier nodes `< A + 1 + i`. -/
@[expose] def Wf (g : Aig) : Prop :=
  ∀ i (_h : i < g.nodes.size),
    (g.nodes[i].1 >>> 1).toNat < g.A + 1 + i ∧ (g.nodes[i].2 >>> 1).toNat < g.A + 1 + i

/-- Prefix extension relation between two AIGs (`g ≤ g'`). -/
@[expose] def Extends (g g' : Aig) : Prop :=
  g.A = g'.A ∧ g.nodes.size ≤ g'.nodes.size ∧
    ∀ i (h : i < g.nodes.size), g'.nodes[i]? = some (g.nodes[i]'h)

instance : LE Aig := ⟨Extends⟩

theorem extends_rfl (g : Aig) : g ≤ g :=
  ⟨rfl, Nat.le_refl _, fun _i h => Array.getElem?_eq_getElem h⟩

theorem extends_trans {g₁ g₂ g₃ : Aig} (h12 : g₁ ≤ g₂) (h23 : g₂ ≤ g₃) : g₁ ≤ g₃ := by
  refine ⟨h12.1.trans h23.1, Nat.le_trans h12.2.1 h23.2.1, fun i hi => ?_⟩
  have hi2 : i < g₂.nodes.size := Nat.lt_of_lt_of_le hi h12.2.1
  rw [h23.2.2 i hi2]
  have h12i := h12.2.2 i hi
  rw [Array.getElem?_eq_getElem hi2] at h12i
  exact h12i

/-- Evaluate an AIG literal against an array of already-computed node values. -/
@[expose] def evalLitIn (vals : Array Bool) (l : UInt32) : Bool :=
  (vals.getD (l >>> 1).toNat false) ^^ ((l &&& 1) != 0)

/-- Initial node valuation array of length `A + 1` (`0 ↦ false`, `1..A ↦ ρ n`). -/
@[expose] def initVals (A : Nat) (ρ : Nat → Bool) : Array Bool :=
  Array.ofFn (n := A + 1) fun i => if i.val == 0 then false else ρ i.val

/-- Single fold step evaluating one AND gate and appending its Boolean value. -/
@[expose] def stepVal (vals : Array Bool) (gate : UInt32 × UInt32) : Array Bool :=
  vals.push (evalLitIn vals gate.1 && evalLitIn vals gate.2)

/-- Left-fold evaluation of all nodes `0 .. A + nodes.size`. -/
@[expose] def evalNodes (g : Aig) (ρ : Nat → Bool) : Array Bool :=
  g.nodes.foldl stepVal (initVals g.A ρ)

/-- Evaluate AIG node `n` under atom assignment `ρ : Nat → Bool`. -/
@[expose] def evalNode (g : Aig) (ρ : Nat → Bool) (n : Nat) : Bool :=
  (evalNodes g ρ).getD n false

/-- Evaluate AIG literal `l = 2*node + neg` under atom assignment `ρ`. -/
@[expose] def evalLit (g : Aig) (ρ : Nat → Bool) (l : UInt32) : Bool :=
  g.evalNode ρ (l >>> 1).toNat ^^ ((l &&& 1) != 0)

private theorem initVals_size (A : Nat) (ρ : Nat → Bool) : (initVals A ρ).size = A + 1 := by
  simp [initVals]

private theorem foldl_stepVal_size (gs : List (UInt32 × UInt32)) (acc : Array Bool) :
    (gs.foldl stepVal acc).size = acc.size + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, stepVal, Array.size_push]
    omega

theorem evalNodes_size (g : Aig) (ρ : Nat → Bool) :
    (evalNodes g ρ).size = g.A + 1 + g.nodes.size := by
  unfold evalNodes
  rw [← Array.foldl_toList, foldl_stepVal_size, initVals_size, Array.length_toList]

private theorem foldl_stepVal_getElem_lt (gs : List (UInt32 × UInt32)) (acc : Array Bool)
    {n : Nat} (hn : n < acc.size) :
    (gs.foldl stepVal acc)[n]'(by rw [foldl_stepVal_size]; omega) = acc[n]'hn := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hn' : n < (stepVal acc g).size := by simp [stepVal]; omega
    rw [ih (stepVal acc g) hn']
    simp [stepVal, Array.getElem_push, hn]

private theorem foldl_stepVal_prefix (gs1 gs2 : List (UInt32 × UInt32)) (acc1 acc2 : Array Bool)
    (hsz : acc1.size = acc2.size) (heq : ∀ k (hk : k < acc1.size), acc1[k] = acc2[k]'(by omega))
    (hle : gs1.length ≤ gs2.length)
    (hpref : ∀ i (hi : i < gs1.length), gs2[i]'(Nat.lt_of_lt_of_le hi hle) = gs1[i])
    {n : Nat} (hn : n < acc1.size + gs1.length) :
    (gs2.foldl stepVal acc2)[n]'(by rw [foldl_stepVal_size]; omega) =
      (gs1.foldl stepVal acc1)[n]'(by rw [foldl_stepVal_size]; omega) := by
  induction gs1 generalizing gs2 acc1 acc2 with
  | nil =>
    simp only [List.length_nil, Nat.add_zero] at hn
    simp only [List.foldl_nil]
    rw [foldl_stepVal_getElem_lt gs2 acc2 (by omega)]
    exact (heq n hn).symm
  | cons g1 gs1 ih =>
    cases gs2 with
    | nil => simp at hle
    | cons g2 gs2 =>
      have hg : g2 = g1 := hpref 0 (by simp)
      subst hg
      simp only [List.foldl_cons, List.length_cons] at hle hn ⊢
      have hstep_sz : (stepVal acc1 g2).size = (stepVal acc2 g2).size := by
        simp [stepVal, hsz]
      have hlit : ∀ l, evalLitIn acc1 l = evalLitIn acc2 l := by
        intro l
        simp only [evalLitIn, Array.getD_eq_getD_getElem?]
        congr 1
        by_cases hl : (l >>> 1).toNat < acc1.size
        · have hl2 : (l >>> 1).toNat < acc2.size := by omega
          rw [Array.getElem?_eq_getElem hl, Array.getElem?_eq_getElem hl2, heq _ hl]
        · have hl2 : acc2.size ≤ (l >>> 1).toNat := by omega
          rw [Array.getElem?_eq_none (Nat.le_of_not_lt hl), Array.getElem?_eq_none hl2]
      have hstep_eq : ∀ k (hk : k < (stepVal acc1 g2).size),
          (stepVal acc1 g2)[k] = (stepVal acc2 g2)[k]'(by omega) := by
        intro k hk
        simp only [stepVal, Array.size_push] at hk
        simp only [stepVal, Array.getElem_push]
        split
        · next hlt =>
          have hlt2 : k < acc2.size := by omega
          simp [hlt2, heq k hlt]
        · next hge =>
          have hge2 : ¬ k < acc2.size := by omega
          simp [hge2, hlit]
      exact ih gs2 (stepVal acc1 g2) (stepVal acc2 g2) hstep_sz hstep_eq
        (Nat.le_of_succ_le_succ hle)
        (fun i hi => hpref (i + 1) (Nat.succ_lt_succ hi))
        (by rw [stepVal, Array.size_push]; omega)

theorem evalNodes_extend {g g' : Aig} {ρ : Nat → Bool} (hext : g ≤ g')
    {n : Nat} (hn : n < g.A + 1 + g.nodes.size) :
    (evalNodes g' ρ)[n]'(by rw [evalNodes_size]; have := hext.1; have := hext.2.1; omega) =
      (evalNodes g ρ)[n]'(by rw [evalNodes_size]; omega) := by
  have h1 : (evalNodes g' ρ)[n]'(by rw [evalNodes_size]; have := hext.1; have := hext.2.1; omega) =
      (g'.nodes.toList.foldl stepVal (initVals g'.A ρ))[n]'(by
        rw [foldl_stepVal_size, initVals_size, Array.length_toList]
        have := hext.1; have := hext.2.1; omega) := by
    simp [evalNodes, ← Array.foldl_toList]
  have h2 : (evalNodes g ρ)[n]'(by rw [evalNodes_size]; omega) =
      (g.nodes.toList.foldl stepVal (initVals g.A ρ))[n]'(by
        rw [foldl_stepVal_size, initVals_size, Array.length_toList]; omega) := by
    simp [evalNodes, ← Array.foldl_toList]
  rw [h1, h2]
  refine foldl_stepVal_prefix g.nodes.toList g'.nodes.toList (initVals g.A ρ) (initVals g'.A ρ)
    (by simp [initVals_size, hext.1]) (fun k hk => by
      simp only [initVals, Array.getElem_ofFn])
    (by simpa using hext.2.1)
    (fun i hi => by
      have hi' : i < g.nodes.size := by simpa using hi
      have hi2 : i < g'.nodes.size := Nat.lt_of_lt_of_le hi' hext.2.1
      have hmem := hext.2.2 i hi'
      rw [Array.getElem?_eq_getElem hi2, Option.some.injEq] at hmem
      simpa using hmem)
    (by simpa [initVals_size] using hn)

theorem evalNode_extend {g g' : Aig} {ρ : Nat → Bool} (hext : g ≤ g')
    {n : Nat} (hn : n < g.A + 1 + g.nodes.size) :
    g'.evalNode ρ n = g.evalNode ρ n := by
  unfold evalNode
  have hn1 : n < (evalNodes g ρ).size := by rw [evalNodes_size]; exact hn
  have hn2 : n < (evalNodes g' ρ).size := by
    rw [evalNodes_size]; have := hext.1; have := hext.2.1; omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hn1,
    Array.getElem?_eq_getElem hn2, Option.getD_some]
  exact evalNodes_extend hext hn

private theorem lsr1_lt_of_lt_two_mul {l : UInt32} {N : Nat} (h : l.toNat < 2 * N) :
    (l >>> 1).toNat < N := by
  have : (l >>> 1).toNat = l.toNat / 2 := by
    rw [UInt32.toNat_shiftRight]
    simp [Nat.shiftRight_eq_div_pow]
  omega

theorem evalLit_extend_node {g g' : Aig} {ρ : Nat → Bool} {l : UInt32}
    (hext : g ≤ g') (hl : (l >>> 1).toNat < g.A + 1 + g.nodes.size) :
    g'.evalLit ρ l = g.evalLit ρ l := by
  unfold evalLit
  rw [evalNode_extend hext hl]

theorem evalLit_extend {g g' : Aig} {ρ : Nat → Bool} {l : UInt32}
    (hext : g ≤ g') (hl : l.toNat < 2 * (g.A + 1 + g.nodes.size)) :
    g'.evalLit ρ l = g.evalLit ρ l :=
  evalLit_extend_node hext (lsr1_lt_of_lt_two_mul hl)

theorem evalNode_zero (g : Aig) (ρ : Nat → Bool) : g.evalNode ρ 0 = false := by
  unfold evalNode evalNodes
  rw [← Array.foldl_toList]
  have h0 : 0 < (initVals g.A ρ).size := by rw [initVals_size]; omega
  have hsz : 0 < (g.nodes.toList.foldl stepVal (initVals g.A ρ)).size := by
    rw [foldl_stepVal_size]; omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz, Option.getD_some]
  rw [foldl_stepVal_getElem_lt g.nodes.toList (initVals g.A ρ) h0]
  simp [initVals]

theorem evalNode_atom (g : Aig) (ρ : Nat → Bool) {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ g.A) :
    g.evalNode ρ n = ρ n := by
  unfold evalNode evalNodes
  rw [← Array.foldl_toList]
  have hn : n < (initVals g.A ρ).size := by rw [initVals_size]; omega
  have hsz : n < (g.nodes.toList.foldl stepVal (initVals g.A ρ)).size := by
    rw [foldl_stepVal_size]; omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz, Option.getD_some]
  rw [foldl_stepVal_getElem_lt g.nodes.toList (initVals g.A ρ) hn]
  have hne : n ≠ 0 := by omega
  simp [initVals, hne]

private theorem arr_take_size {α : Type} (arr : Array α) (k : Nat) :
    (arr.take k).size = min k arr.size := by
  simp [Array.take, Array.size_extract]

private theorem arr_take_getElem {α : Type} (arr : Array α) {k i : Nat}
    (hi : i < (arr.take k).size) :
    (arr.take k)[i] = arr[i]'(by rw [arr_take_size] at hi; omega) := by
  simp [Array.take]

private theorem evalNode_take_eq {g : Aig} {ρ : Nat → Bool} {k n : Nat}
    (hk : k ≤ g.nodes.size) (hn : n < g.A + 1 + k) :
    let gk : Aig := { A := g.A, nodes := g.nodes.take k }
    g.evalNode ρ n = gk.evalNode ρ n := by
  intro gk
  have hext : gk ≤ g := by
    refine ⟨rfl, ?_, fun i hi => ?_⟩
    · simp [gk]; omega
    · have hi' : i < g.nodes.size := by simp [gk] at hi; omega
      rw [Array.getElem?_eq_getElem hi']
      simp [gk]
  have hnk : n < gk.A + 1 + gk.nodes.size := by
    simp [gk]; omega
  exact evalNode_extend (ρ := ρ) hext hnk

private theorem evalLit_take_eq {g : Aig} {ρ : Nat → Bool} {k : Nat} {l : UInt32}
    (hk : k ≤ g.nodes.size) (hl : (l >>> 1).toNat < g.A + 1 + k) :
    let gk : Aig := { A := g.A, nodes := g.nodes.take k }
    g.evalLit ρ l = gk.evalLit ρ l := by
  intro gk
  unfold evalLit
  rw [evalNode_take_eq hk hl]

private theorem take_succ_toList {α : Type} (arr : Array α) {i : Nat} (hi : i < arr.size) :
    (arr.take (i + 1)).toList = (arr.take i).toList ++ [arr[i]] := by
  simp only [Array.take, Array.toList_extract]
  exact List.take_succ_eq_append_getElem (by simpa using hi)

theorem evalNode_gate {g : Aig} (hwf : g.Wf) (ρ : Nat → Bool) {i : Nat} (hi : i < g.nodes.size) :
    g.evalNode ρ (g.A + 1 + i) = (g.evalLit ρ g.nodes[i].1 && g.evalLit ρ g.nodes[i].2) := by
  have htake : g.evalNode ρ (g.A + 1 + i) =
      ({ A := g.A, nodes := g.nodes.take (i + 1) } : Aig).evalNode ρ (g.A + 1 + i) :=
    evalNode_take_eq (Nat.succ_le_of_lt hi) (by omega)
  rw [htake]
  let gi : Aig := { A := g.A, nodes := g.nodes.take i }
  have h1 : (g.nodes[i].1 >>> 1).toNat < g.A + 1 + i := (hwf i hi).1
  have h2 : (g.nodes[i].2 >>> 1).toNat < g.A + 1 + i := (hwf i hi).2
  have hl1 : g.evalLit ρ g.nodes[i].1 = gi.evalLit ρ g.nodes[i].1 :=
    evalLit_take_eq (Nat.le_of_lt hi) h1
  have hl2 : g.evalLit ρ g.nodes[i].2 = gi.evalLit ρ g.nodes[i].2 :=
    evalLit_take_eq (Nat.le_of_lt hi) h2
  rw [hl1, hl2]
  have hsz_gi : (evalNodes gi ρ).size = g.A + 1 + i := by
    rw [evalNodes_size]; simp [gi]; omega
  have hfold : evalNodes { A := g.A, nodes := g.nodes.take (i + 1) } ρ =
      stepVal (evalNodes gi ρ) g.nodes[i] := by
    unfold evalNodes
    rw [← Array.foldl_toList, ← Array.foldl_toList, take_succ_toList g.nodes hi, List.foldl_append]
    rfl
  unfold evalNode
  rw [hfold, stepVal]
  have hlt : g.A + 1 + i <
      ((evalNodes gi ρ).push
        (evalLitIn (evalNodes gi ρ) g.nodes[i].1 &&
         evalLitIn (evalNodes gi ρ) g.nodes[i].2)).size := by
    rw [Array.size_push, hsz_gi]; omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some,
    Array.getElem_push]
  simp only [hsz_gi, Nat.lt_irrefl, ↓reduceDIte]
  rfl

@[simp] theorem evalLit_zero (g : Aig) (ρ : Nat → Bool) : g.evalLit ρ 0 = false := by
  simp [evalLit, evalNode_zero]

@[simp] theorem evalLit_one (g : Aig) (ρ : Nat → Bool) : g.evalLit ρ 1 = true := by
  simp [evalLit, evalNode_zero]

private theorem u32_xor1_lsr1 (l : UInt32) : ((l ^^^ 1) >>> 1) = (l >>> 1) := by
  have h : ((l ^^^ 1) >>> 1).toBitVec = (l >>> 1).toBitVec := by
    apply BitVec.eq_of_toNat_eq
    change ((l ^^^ 1) >>> 1).toNat = (l >>> 1).toNat
    rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftRight, UInt32.toNat_xor]
    rw [show (1 : UInt32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by decide : 1 < 32)]
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_shiftRight, Nat.testBit_xor]
    have hk : (1 : Nat).testBit (k + 1) = false := by
      have hpow : 1 < 2 ^ (k + 1) :=
        Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (by omega : 1 ≤ k + 1))
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt hpow]
      decide
    rw [Nat.add_comm 1 k, hk, Bool.xor_false]
  exact congrArg UInt32.ofBitVec h

private theorem u32_xor1_and1 (l : UInt32) :
    (((l ^^^ 1) &&& 1) != 0) = !((l &&& 1) != 0) := by
  have hb : ∀ x : UInt32, (x != 0) = (x.toNat != 0) := by
    intro x
    by_cases hx : x = 0
    · subst hx; decide
    · have hne : x.toNat ≠ 0 := fun h => by
        apply hx
        exact congrArg UInt32.ofBitVec (BitVec.eq_of_toNat_eq h)
      have h1 : (x != 0) = true := by simp [bne, hx]
      have h2 : (x.toNat != 0) = true := by simp [bne, hne]
      rw [h1, h2]
  rw [hb, hb, UInt32.toNat_and, UInt32.toNat_and, UInt32.toNat_xor]
  rw [show (1 : UInt32).toNat = 1 from rfl, Nat.and_one_is_mod, Nat.and_one_is_mod]
  have htb : ∀ n : Nat, (n % 2 != 0) = n.testBit 0 := by
    intro n
    rw [Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
  rw [htb, htb, Nat.testBit_xor]
  simp

theorem evalLit_xor_one (g : Aig) (ρ : Nat → Bool) (l : UInt32) :
    g.evalLit ρ (l ^^^ 1) = !(g.evalLit ρ l) := by
  unfold evalLit
  rw [u32_xor1_lsr1, u32_xor1_and1]
  cases g.evalNode ρ (l >>> 1).toNat <;> cases ((l &&& 1) != 0) <;> rfl

/-- Push a single AND gate `(lhs, rhs)` onto `g`, returning `(g', outLit)`. -/
@[expose] def pushNode (g : Aig) (lhs rhs : UInt32) : Aig × UInt32 :=
  let idx := g.A + 1 + g.nodes.size
  ({ g with nodes := g.nodes.push (lhs, rhs) }, UInt32.ofNat (2 * idx))

theorem pushNode_extends (g : Aig) (lhs rhs : UInt32) :
    g ≤ (g.pushNode lhs rhs).1 := by
  refine ⟨rfl, by simp [pushNode], fun i hi => ?_⟩
  have hi' : i < (g.nodes.push (lhs, rhs)).size := by simp; omega
  rw [pushNode, Array.getElem?_eq_getElem hi']
  simp [Array.getElem_push, hi]

theorem pushNode_wf {g : Aig} (hwf : g.Wf) {lhs rhs : UInt32}
    (hl : (lhs >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hr : (rhs >>> 1).toNat < g.A + 1 + g.nodes.size) :
    (g.pushNode lhs rhs).1.Wf := by
  intro i hi
  simp only [pushNode, Array.size_push] at hi
  simp only [pushNode, Array.getElem_push]
  split
  · next hlt => exact hwf i hlt
  · next hge =>
    have heq : i = g.nodes.size := by omega
    subst heq
    exact ⟨hl, hr⟩

theorem pushNode_evalLit {g : Aig} (hwf : g.Wf) (ρ : Nat → Bool) {lhs rhs : UInt32}
    (hl : (lhs >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hr : (rhs >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hbound : 2 * (g.A + 1 + g.nodes.size) < 4294967296) :
    let res := g.pushNode lhs rhs
    res.1.evalLit ρ res.2 = (g.evalLit ρ lhs && g.evalLit ρ rhs) := by
  intro res
  have hwf' := pushNode_wf hwf hl hr
  have hext := pushNode_extends g lhs rhs
  have h2 : res.2.toNat = 2 * (g.A + 1 + g.nodes.size) := by
    simp [res, pushNode, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hbound]
  have hlsr : (res.2 >>> 1).toNat = g.A + 1 + g.nodes.size := by
    rw [UInt32.toNat_shiftRight, h2, show (1 : UInt32).toNat = 1 from rfl]
    rw [show 1 % 32 = 1 from rfl, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  have hand : (res.2 &&& 1) = 0 := by
    have hbv : (res.2 &&& 1).toBitVec = (0 : UInt32).toBitVec := by
      apply BitVec.eq_of_toNat_eq
      change (res.2 &&& 1).toNat = (0 : UInt32).toNat
      rw [UInt32.toNat_and, show (1 : UInt32).toNat = 1 from rfl,
        show (0 : UInt32).toNat = 0 from rfl, Nat.and_one_is_mod, h2]
      omega
    exact congrArg UInt32.ofBitVec hbv
  have hgate := evalNode_gate hwf' ρ (i := g.nodes.size) (by simp [pushNode])
  simp only [pushNode, Array.getElem_push, Nat.lt_irrefl, ↓reduceDIte] at hgate
  conv => lhs; unfold evalLit; rw [hlsr, hand]
  have hres1 : res.1 = { A := g.A, nodes := g.nodes.push (lhs, rhs) } := rfl
  rw [hres1, hgate, ← hres1, evalLit_extend_node hext hl, evalLit_extend_node hext hr]
  simp

end Aig

/-- Slice correctness predicate: AIG literal list `ls` bitblasts `v : BitVec w` under `ρ`. -/
@[expose] def SliceDenotes (g : Aig) (ρ : Nat → Bool) (ls : List UInt32) {w : Nat}
    (v : BitVec w) : Prop :=
  ls.length = w ∧ ∀ i (_h : i < w), g.evalLit ρ (ls.getD i 0) = v.getLsbD i

theorem SliceDenotes.extend {g g' : Aig} {ρ : Nat → Bool} {ls : List UInt32} {w : Nat}
    {v : BitVec w} (hext : g ≤ g')
    (hbounds : ∀ l ∈ ls, (l >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hs : SliceDenotes g ρ ls v) :
    SliceDenotes g' ρ ls v := by
  refine ⟨hs.1, fun i hi => ?_⟩
  have hlen : i < ls.length := by rw [hs.1]; exact hi
  have hmem : ls.getD i 0 ∈ ls := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    exact List.getElem_mem hlen
  rw [Aig.evalLit_extend_node hext (hbounds _ hmem)]
  exact hs.2 i hi

end LeanQbe.T.Examples.Bitblast.Ref
