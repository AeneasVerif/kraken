module

public import Lean.ToExpr

/-!
# Structural `O(log n)` Binary `Nat`-Keyed Trie

Kernel-reducible (`rfl`-safe: no `WellFounded.fix`, structural `fuel := n + 1` on `insert`)
binary trie with `Lean.ToExpr` deriving and verified `find?`/`insert`/`erase` laws, shared by
`LeanQbe.T.Target` (`Hints`), `Rega` (`slots`, `defs`), and mid-end optimization passes.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Structural `O(log n)` binary trie (`rfl`-safe: no `WellFounded.fix`,
`fuel := n + 1` on `insert`). -/
inductive Trie (α : Type) where
  | empty
  | node (val : Option α) (even odd : Trie α)
  deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

def Trie.find? {α : Type} : Trie α → Nat → Option α
  | .empty, _ => none
  | .node v _ _, 0 => v
  | .node _ e o, n + 1 => if n % 2 == 0 then e.find? (n / 2) else o.find? (n / 2)

def Trie.getD {α : Type} (t : Trie α) (n : Nat) (d : α) : α :=
  (t.find? n).getD d

def Trie.insertAux {α : Type} : Nat → Trie α → Nat → α → Trie α
  | 0, t, _, _ => t
  | _ + 1, .empty, 0, v => .node (some v) .empty .empty
  | _ + 1, .node _ e o, 0, v => .node (some v) e o
  | fuel + 1, .empty, n + 1, v =>
    if n % 2 == 0 then .node none (Trie.insertAux fuel .empty (n / 2) v) .empty
    else .node none .empty (Trie.insertAux fuel .empty (n / 2) v)
  | fuel + 1, .node x e o, n + 1, v =>
    if n % 2 == 0 then .node x (Trie.insertAux fuel e (n / 2) v) o
    else .node x e (Trie.insertAux fuel o (n / 2) v)

def Trie.insert {α : Type} (t : Trie α) (n : Nat) (v : α) : Trie α :=
  Trie.insertAux (n + 1) t n v

def Trie.erase {α : Type} : Trie α → Nat → Trie α
  | .empty, _ => .empty
  | .node _ e o, 0 => .node none e o
  | .node x e o, n + 1 =>
    if n % 2 == 0 then .node x (e.erase (n / 2)) o else .node x e (o.erase (n / 2))

theorem trie_insert_rfl : ((Trie.empty : Trie Nat).insert 5 1).find? 5 = some 1 := rfl

private theorem div2_ne {m k : Nat} (hne : k ≠ m)
    (hp : (m % 2 == 0) = (k % 2 == 0)) : k / 2 ≠ m / 2 := by
  by_cases hm : m % 2 = 0 <;> by_cases hk : k % 2 = 0 <;> simp_all <;> omega

theorem Trie.find?_insertAux {α : Type} : ∀ (fuel : Nat) (t : Trie α) (i j : Nat) (v : α),
    i < fuel → (Trie.insertAux fuel t i v).find? j = if j = i then some v else t.find? j
  | 0, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ + 1, t, 0, j, _, _ => by cases t <;> cases j <;> simp [Trie.insertAux, Trie.find?]
  | _ + 1, t, m + 1, 0, _, _ => by
    cases t <;> by_cases h : m % 2 == 0 <;> simp [Trie.insertAux, Trie.find?, h]
  | fuel + 1, t, m + 1, k + 1, v, hi => by
    have hm : m / 2 < fuel := by omega
    by_cases hkm : k = m
    · subst hkm; cases t <;> by_cases h : k % 2 == 0 <;>
        simp [Trie.insertAux, Trie.find?, h, Trie.find?_insertAux fuel _ (k / 2) (k / 2) v hm]
    · cases t <;> by_cases hm2 : m % 2 == 0 <;> by_cases hk2 : k % 2 == 0 <;>
        simp [Trie.insertAux, Trie.find?, hm2, hk2, hkm,
          Trie.find?_insertAux fuel _ (m / 2) (k / 2) v hm]
      all_goals exact fun hd => absurd hd (div2_ne hkm (by simp [hm2, hk2]))

@[simp] theorem Trie.find?_empty {α : Type} (i : Nat) :
    (Trie.empty : Trie α).find? i = none := rfl

theorem Trie.find?_insert {α : Type} (t : Trie α) (i j : Nat) (v : α) :
    (t.insert i v).find? j = if j = i then some v else t.find? j :=
  Trie.find?_insertAux (i + 1) t i j v (Nat.lt_succ_self i)

@[simp] theorem Trie.find?_insert_self {α : Type} (t : Trie α) (i : Nat) (v : α) :
    (t.insert i v).find? i = some v := by
  simp [Trie.find?_insert]

theorem Trie.find?_insert_ne {α : Type} (t : Trie α) {i j : Nat} (v : α) (h : j ≠ i) :
    (t.insert i v).find? j = t.find? j := by
  simp [Trie.find?_insert, h]

theorem Trie.find?_erase {α : Type} : ∀ (t : Trie α) (i j : Nat),
    (t.erase i).find? j = if j = i then none else t.find? j
  | .empty, _, _ => by split <;> rfl
  | .node _ _ _, 0, j => by cases j <;> simp [Trie.erase, Trie.find?]
  | .node _ _ _, m + 1, 0 => by by_cases h : m % 2 == 0 <;> simp [Trie.erase, Trie.find?, h]
  | .node _ e o, m + 1, k + 1 => by
    by_cases hkm : k = m
    · subst hkm
      by_cases h : k % 2 == 0 <;>
        simp [Trie.erase, Trie.find?, h, e.find?_erase, o.find?_erase]
    · by_cases hm2 : m % 2 == 0 <;> by_cases hk2 : k % 2 == 0 <;>
        simp [Trie.erase, Trie.find?, hm2, hk2, hkm, e.find?_erase, o.find?_erase]
      all_goals exact fun hd => absurd hd (div2_ne hkm (by simp [hm2, hk2]))

@[simp] theorem Trie.find?_erase_self {α : Type} (t : Trie α) (i : Nat) :
    (t.erase i).find? i = none := by
  simp [Trie.find?_erase]

theorem Trie.find?_erase_ne {α : Type} (t : Trie α) {i j : Nat} (h : j ≠ i) :
    (t.erase i).find? j = t.find? j := by
  simp [Trie.find?_erase, h]

@[simp] theorem Trie.getD_empty {α : Type} (i : Nat) (d : α) :
    (Trie.empty : Trie α).getD i d = d := rfl

@[simp] theorem Trie.getD_insert_self {α : Type} (t : Trie α) (i : Nat) (v d : α) :
    (t.insert i v).getD i d = v := by
  simp [Trie.getD]

end LeanQbe.T
