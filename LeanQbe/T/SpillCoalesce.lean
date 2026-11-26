module

public import LeanQbe.T.SpillEmit

/-!
# Back-Edge Coalescing & Iterative Recoloring (`SpillCoalesce`)

Untrusted register-allocation oracle helpers (`0` proof LOC; every hint is re-verified by
`Rega.lowerFn`):
1. `pow8` / `addJumpAffAnti`: loop-latch affinity boost (`8^depth`) and back-edge parallel-move
   pair anti-affinity `(src_i, dst_j)` (`i ≠ j`) to eliminate 2/3-cycle `mov` chains.
2. `bestRegNet`: net affinity-minus-anti scoring (`p1 + an2 > p2 + an1`) with soft avoid tie-break.
3. `refineColors`: bounded 2-pass iterative recoloring preserving register class and `gPb` budgets.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Spill

open Live Rega

/-- `8 ^ min d 4`, used to scale loop-latch coalescing and anti-affinity weights. -/
def pow8 : Nat → Nat
  | 0 => 1
  | 1 => 8
  | 2 => 64
  | 3 => 512
  | _ => 4096

/-- Add block-edge coalescing affinities and parallel-move anti-affinities, boosting true loop
latches (`isLatch = true`) by `8^depth` and weighting simultaneous `(src_i, dst_j)` (`i ≠ j`)
anti-affinity to avoid 2/3-cycle register swaps. -/
def addJumpAffAnti (isLatch : Bool) (depth : Nat) (as : List (Option Nat)) (ps : List Nat)
    (mult : Nat) (affEdges antiEdges : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat) × List (Nat × Nat × Nat) :=
  let boost := if isLatch then min (pow8 depth) 512 else 1
  let affW := min (8 * mult * boost) 100000000
  let antiW := min ((if isLatch then 4 * boost else 2) * mult) 100000000
  let aff' := (as.zip ps).foldl (fun a (ao, p) =>
    match ao with | some x => (x, p, affW) :: a | none => a) affEdges
  let anti' := (as.zip ps).foldl (fun a (ao, p) =>
    match ao with
    | some x =>
      ps.foldl (fun a p' =>
        if Nat.beq p' p || Nat.beq x p' then a else (x, p', antiW) :: a) a
    | none => a) antiEdges
  (aff', anti')

/-- Choose the candidate register maximizing net affinity minus anti-affinity (`p - anti`),
breaking ties by lower anti-affinity and then lower soft avoidance (`xAvoid`). -/
def bestRegNet (xPrefs xAnti xAvoid : List (Nat × Nat)) : List Nat → Option Nat
  | [] => none
  | r0 :: rs =>
    let score (r : Nat) := (regWeight xPrefs r, regWeight xAnti r, regWeight xAvoid r)
    some (rs.foldl (fun (bestR, bestP, bestAn, bestAv) r =>
      let (p, an, av) := score r
      let lhs := p + bestAn
      let rhs := bestP + an
      let better := Nat.ble (rhs + 1) lhs ||
        (Nat.beq lhs rhs && (Nat.ble (an + 1) bestAn ||
          (Nat.beq an bestAn && Nat.ble (av + 1) bestAv)))
      if better then (r, p, an, av) else (bestR, bestP, bestAn, bestAv))
      (r0, score r0)).1

end Spill
end LeanQbe.T
end

public section

namespace LeanQbe.T
namespace Spill

open Live Rega

/-- Bounded 2-pass iterative coalescing / anti-affinity recoloring over GPR-homed variables.
Preserves register class (`caller` vs `usedCs`), `bk`/call-crossing `zextPeers` constraints, and
never moves `armEv` or `forceEv` variables, so all pressure budgets (`gPb`) remain valid. -/
def refineColors {I : Isa} (c : Ctx I) (order : List (Nat × Nat))
    (interf : Trie (List Nat)) (affT antiT abiGT : Trie (List (Nat × Nat)))
    (zextPeers : Trie (List Nat)) (bk : Trie (Nat × SlotWidth × Bool))
    (armEv forceEv : Trie (List Nat)) (usedCs : List Nat)
    (armShareFn : Trie (List Nat) → Nat → Nat → Bool)
    (hT0 : Trie (Home I.Cond)) : Trie (Home I.Cond) :=
  let isForced (x : Nat) : Bool :=
    (c.varBlks.getD x []).any fun b => natMem x (forceEv.getD b [])
  let stepOne (hT : Trie (Home I.Cond)) (x : Nat) : Trie (Home I.Cond) :=
    if (armEv.find? x).isSome || isForced x then hT
    else match hT.getD x .none with
      | .gpr rx =>
        let isCaller := Nat.blt rx c.nGpr
        let cands0 := if isCaller then c.gAlloc else usedCs
        let xI := interf.getD x []
        let peers := zextPeers.getD x []
        let isX := c.cross.getD x false
        let xSplit := isX || (bk.find? x).isSome
        let forb0 := xI.foldl (fun rs y => match hT.getD y .none with
          | .gpr ry => if natMem ry rs || armShareFn armEv y x then rs else ry :: rs
          | _ => rs) []
        let forb := if !isCaller then forb0 else
          peers.foldl (fun rs z => match hT.getD z .none with
            | .gpr rz =>
              if (xSplit || (bk.find? z).isSome || c.cross.getD z false) &&
                  Nat.blt rz c.nGpr && !natMem rz rs then rz :: rs
              else rs
            | _ => rs) forb0
        let cands := cands0.filter (!natMem · forb)
        let prefs := (affT.getD x []).foldl (fun ps (y, w) =>
          match hT.getD y .none with | .gpr ry => (ry, w) :: ps | _ => ps) (abiGT.getD x [])
        let anti := (antiT.getD x []).foldl (fun ps (y, w) =>
          match hT.getD y .none with | .gpr ry => (ry, w) :: ps | _ => ps) []
        match bestRegNet prefs anti [] (rx :: cands.filter (!Nat.beq · rx)) with
        | some r =>
          if Nat.beq r rx then hT
          else
            let pNew := regWeight prefs r; let anNew := regWeight anti r
            let pOld := regWeight prefs rx; let anOld := regWeight anti rx
            let better := Nat.ble (pOld + anNew + 1) (pNew + anOld) ||
              (Nat.beq (pNew + anOld) (pOld + anNew) && Nat.ble (anNew + 1) anOld)
            if better then hT.insert x (.gpr r) else hT
        | none => hT
      | _ => hT
  let pass (hT : Trie (Home I.Cond)) := order.foldl (fun h (_, x) => stepOne h x) hT
  pass (pass hT0)

end Spill
end LeanQbe.T
end
