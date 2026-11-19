inductive RefTree where
  | leaf (v : Nat)
  | node (l r : RefTree)

def refSumToAcc (n acc : Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => refSumToAcc k (acc + k + 1)

def refSumTo (n : Nat) : Nat := refSumToAcc n 0

def refListBuild (n : Nat) (acc : List Nat) : List Nat :=
  match n with
  | 0 => acc
  | k + 1 => refListBuild k ((k + 1) :: acc)

def refListMap (f : Nat → Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => f x :: refListMap f xs

def refListSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + refListSum xs

def refMapAdd (n k : Nat) : Nat :=
  refListSum (refListMap (fun x => x + k) (refListBuild n []))

def refMkTree (depth base : Nat) : RefTree :=
  match depth with
  | 0 => .leaf base
  | d + 1 => .node (refMkTree d base) (refMkTree d (base + 1))

def refTreeSum : RefTree → Nat
  | .leaf v => v
  | .node l r => refTreeSum l + refTreeSum r

def refTree2 (depth : Nat) : Nat :=
  refTreeSum (refMkTree depth 1)

def refListFoldl (f : Nat → Nat → Nat) (acc : Nat) : List Nat → Nat
  | [] => acc
  | x :: xs => refListFoldl f (f acc x) xs

def refFoldMap (n k : Nat) : Nat :=
  refListFoldl (fun a b => a + b + (k + 1)) 0 (refListBuild n [])

def main : IO Unit := do
  for n in [0, 1, 5, 10, 12] do
    IO.println s!"CASE n={n} sumTo={refSumTo n} mapAdd={refMapAdd n 3} foldMap={refFoldMap n 4}"
  for d in [0, 1, 2, 3, 4, 5, 6] do
    IO.println s!"TREE d={d} tree2={refTree2 d}"
