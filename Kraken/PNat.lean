module

public import Lean.ToExpr

@[expose] public section

abbrev PNat := { n : Nat // 0 < n }
def PNat.ofNat (n : Nat) (h : 0 < n := by grind) : PNat := ⟨n, h⟩

instance : Hashable PNat where
  hash n := hash n.val

instance {n : Nat} : OfNat PNat (n + 1) where
  ofNat := .ofNat (n + 1)

open Lean ToExpr in
instance : Lean.ToExpr PNat where
  toTypeExpr := mkConst ``PNat
  toExpr n :=
    let proof := mkApp (mkConst ``Nat.zero_lt_succ) (mkRawNatLit (n.val - 1))
    mkApp2 (mkConst ``PNat.ofNat) (mkRawNatLit n.val) proof
