module

public import LeanQbe.T.Ops
public import Std.Data.HashMap
public import Std.Data.HashSet

/-!
# Shared Backend Printer Utilities (`#049-B1`)

Common pure helpers shared by `LeanQbe.T.PrintCpp` and `LeanQbe.T.PrintQbe`:
comparison mnemonics (`cmpOpName`), monotonic group-label allocation (`allocLabelsWith`),
and `O(|V| + |E|)` BFS dead-block pruning (`liveBlockSet` / `liveSortedBlocks`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.PrintUtil

open LeanQbe.T

/-- Render an integer comparison predicate to its lowercase mnemonic (`eq`, `slt`, ...). -/
def cmpOpName : CmpOp → String
  | .eq  => "eq"  | .ne  => "ne"
  | .ult => "ult" | .ule => "ule" | .ugt => "ugt" | .uge => "uge"
  | .slt => "slt" | .sle => "sle" | .sgt => "sgt" | .sge => "sge"

/-- Allocate block-parameter variable names for block `lid` via `allocParam`. -/
def allocBlockParamsWith {m : Type → Type} [Monad m]
    (allocParam : Nat → Nat → Ty → m String) (lid : Nat) :
    (idx : Nat) → (ts : List Ty) → m (Tup (fun _ => String) ts)
  | _, [] => pure PUnit.unit
  | idx, t :: ts => do
    let name ← allocParam lid idx t
    let rest ← allocBlockParamsWith allocParam lid (idx + 1) ts
    pure (name, rest)

/-- Allocate monotonic labels and block parameters for a group signature `sig`. -/
def allocLabelsWith {m : Type → Type} [Monad m] {L : List Ty → Type}
    (nextLid : m Nat) (allocParam : Nat → Nat → Ty → m String)
    (mkLabel : {ts : List Ty} → Nat → Tup (fun _ => String) ts → L ts) :
    (sig : List (List Ty)) → m (Tup L sig)
  | [] => pure PUnit.unit
  | ts :: sig => do
    let lid ← nextLid
    let ps ← allocBlockParamsWith allocParam lid 0 ts
    let ls ← allocLabelsWith nextLid allocParam mkLabel sig
    pure (mkLabel lid ps, ls)

/-- Compute the `Std.HashSet` of block IDs reachable from `seeds` in `O(|V| + |E|)`. -/
def liveBlockSet {β : Type} (idOf : β → Nat) (jumpsOf : β → Array Nat)
    (blocks : Array β) (seeds : Array Nat) : Std.HashSet Nat :=
  Id.run do
    let mut adj : Std.HashMap Nat (Array Nat) := {}
    for blk in blocks do
      let id := idOf blk
      if !adj.contains id then adj := adj.insert id (jumpsOf blk)
    let mut visited : Std.HashSet Nat := {}
    let mut queue : List Nat := []
    let enqueue (acc : Std.HashSet Nat × List Nat) (x : Nat) :=
      if adj.contains x && !acc.1.contains x then (acc.1.insert x, x :: acc.2) else acc
    for s in seeds do
      (visited, queue) := enqueue (visited, queue) s
    for _ in [:adj.size] do
      match queue with
      | [] => break
      | id :: rest =>
        queue := rest
        if let some outs := adj[id]? then
          for dst in outs do
            (visited, queue) := enqueue (visited, queue) dst
    pure visited

/-- Filter `blocks` to IDs reachable from `seeds` and sort deterministically by `idOf`. -/
def liveSortedBlocks {β : Type} (idOf : β → Nat) (jumpsOf : β → Array Nat)
    (blocks : Array β) (seeds : Array Nat) : List β :=
  let live := liveBlockSet idOf jumpsOf blocks seeds
  (blocks.toList.filter fun b => live.contains (idOf b)).mergeSort
    (fun a b => idOf a ≤ idOf b)

end LeanQbe.T.PrintUtil

end
