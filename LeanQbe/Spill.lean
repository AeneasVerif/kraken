module

public import LeanQbe.Live
public import LeanQbe.Rega

/-!
# Priority-graph-coloring register allocator and spilling oracle (untrusted)

Produces `Rega.Hints` for `Rega.lower`; `Rega.lower` checks every move, location, and
register class, so any bug in the heuristic can at worst cause a compile error, never wrong code.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Spill

open Live Rega

def dedupOrd {α : Type} [BEq α] : List α → List α → List α
  | [], acc => acc.reverse
  | x :: xs, acc => dedupOrd xs (if acc.contains x then acc else x :: acc)

def mergePairs (a b : List (Nat × Nat)) : List (Nat × Nat) :=
  match a, b with
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x.1 > y.1 || (x.1 == y.1 && x.2 < y.2) then x :: mergePairs xs (y :: ys)
    else y :: mergePairs (x :: xs) ys
termination_by a.length + b.length

def sortByWeightAux : Nat → List (Nat × Nat) → List (Nat × Nat)
  | 0, xs => xs
  | _, [] => []
  | _, [x] => [x]
  | fuel + 1, xs =>
    let half := xs.length / 2
    mergePairs (sortByWeightAux fuel (xs.take half)) (sortByWeightAux fuel (xs.drop half))

def sortByWeight (xs : List (Nat × Nat)) : List Nat :=
  (sortByWeightAux (xs.length + 1) xs).map (·.2)

def isAlloc {I : Isa} (r : I.Reg) : Bool := I.allocatable.contains r

def opUseVars : Op Nat → List Nat
  | .bin _ _ a b | .cmp _ _ a b => dedupOrd (argVars [a, b]) []
  | .ext _ _ _ a | .copy _ a => argVars [a]

structure GatherAcc (I : Isa) where
  weights : List (Nat × List Nat)
  defInterf : List (Nat × List Nat)
  pts : List (Nat × List Nat)
  abiPref : List (Nat × I.Reg × Nat)
  affEdges : List (Nat × Nat × Nat)

def addAbiList {I : Isa} (as : List (Arg Nat)) (regs : List I.Reg) (mult : Nat)
    (acc : List (Nat × I.Reg × Nat)) : List (Nat × I.Reg × Nat) :=
  (as.zip regs).foldl (fun l (a, r) =>
    match a with | .var x => (x, r, mult) :: l | .imm _ => l) acc

def addParamAbi {I : Isa} (ps : List Nat) (regs : List I.Reg) (mult : Nat)
    (acc : List (Nat × I.Reg × Nat)) : List (Nat × I.Reg × Nat) :=
  (ps.zip regs).foldl (fun l (x, r) => (x, r, mult) :: l) acc

def gatherParams {I : Isa} (L : LiveMap) (mult : Nat) (ps : List Nat) (body : Tree)
    (acc : GatherAcc I) : GatherAcc I :=
  let le := liveIn L body
  let ws := if ps.isEmpty then acc.weights else (mult, ps) :: acc.weights
  let di := ps.foldl (fun d p => if le.contains p then (p, le) :: d else d) acc.defInterf
  { acc with weights := ws, defInterf := di }

def addPt {I : Isa} (need : Nat) (vars : List Nat) (acc : GatherAcc I) : GatherAcc I :=
  if need > 0 && vars.length > I.allocatable.length - need then
    { acc with pts := (I.allocatable.length - need, vars) :: acc.pts }
  else acc

theorem params_sizeOf_le (t : Tree) : sizeOf t.params.2 ≤ sizeOf t := by
  induction t with
  | param _ k ih =>
    simp only [Tree.params]
    exact Nat.le_trans ih (by simp [Tree.param.sizeOf_spec])
  | _ => simp [Tree.params]

def gather {I : Isa} (L : LiveMap) (loops : List Nat) (bparamsMap : List (Nat × List Nat))
    (inLoop : Bool) (t : Tree) (acc : GatherAcc I) : GatherAcc I :=
  match t with
  | .param x k =>
    let ps := x :: k.params.1
    let body := k.params.2
    let acc := gatherParams L (if inLoop then 10 else 1) ps body acc
    have : sizeOf body < sizeOf (Tree.param x k) :=
      Nat.lt_of_le_of_lt (params_sizeOf_le k) (by simp [Tree.param.sizeOf_spec]; omega)
    gather L loops bparamsMap inLoop body acc
  | node@(.let_ _ x op k) =>
    let mult := if inLoop then 10 else 1
    let la := liveIn L k
    let uses := opUseVars op
    let insnLive := liveIn L node
    let need := max uses.length 1
    let acc := addPt need insnLive acc
    let acc := { acc with
      weights := (mult, x :: uses) :: acc.weights
      defInterf := if la.contains x then (x, la) :: acc.defInterf else acc.defInterf
      affEdges := match op with
        | .copy _ (.var a) | .ext _ _ _ (.var a) => (x, a, 6 * mult) :: acc.affEdges
        | .bin _ _ (.var a) _ =>
          if !la.contains a then (x, a, 5 * mult) :: acc.affEdges else acc.affEdges
        | _ => acc.affEdges }
    gather L loops bparamsMap inLoop k acc
  | node@(.load _ x a k) =>
    let mult := if inLoop then 10 else 1
    let la := liveIn L k
    let uses := argVars [a]
    let insnLive := liveIn L node
    let acc := addPt 1 insnLive acc
    let acc := { acc with
      weights := (mult, x :: uses) :: acc.weights
      defInterf := if la.contains x then (x, la) :: acc.defInterf else acc.defInterf }
    gather L loops bparamsMap inLoop k acc
  | node@(.store _ v a k) =>
    let mult := if inLoop then 10 else 1
    let uses := dedupOrd (argVars [v, a]) []
    let insnLive := liveIn L node
    let acc := addPt uses.length insnLive acc
    let acc := { acc with
      weights := if uses.isEmpty then acc.weights else (mult, uses) :: acc.weights }
    gather L loops bparamsMap inLoop k acc
  | .call ip g as k =>
    let mult := if inLoop then 10 else 1
    let ps := k.params.1
    let body := k.params.2
    let uses := argVars as
    let acc := { acc with
      weights := if uses.isEmpty then acc.weights else (mult, uses) :: acc.weights
      abiPref := addParamAbi ps I.retRegs (4 * mult)
        (addAbiList as I.argRegs (4 * mult) acc.abiPref) }
    let acc := gatherParams L mult ps body acc
    have : sizeOf body < sizeOf (Tree.call ip g as k) :=
      Nat.lt_of_le_of_lt (params_sizeOf_le k) (by simp [Tree.call.sizeOf_spec]; omega)
    gather L loops bparamsMap inLoop body acc
  | node@(.jnz _ c _ t e) =>
    let mult := if inLoop then 10 else 1
    let insnLive := liveIn L node
    let acc := addPt 1 insnLive acc
    let acc := { acc with weights := (mult, [c]) :: acc.weights }
    let acc := gather L loops bparamsMap inLoop e acc
    gather L loops bparamsMap inLoop t acc
  | .skip _ k =>
    gather L loops bparamsMap inLoop k acc
  | .jump _ j as =>
    let mult := if inLoop then 10 else 1
    let uses := argVars as
    let ps := ((bparamsMap.find? (·.1 == j)).map (·.2)).getD []
    let affs := (as.zip ps).foldl (fun l (a, p) =>
      match a with | .var u => (u, p, 8 * mult) :: l | .imm _ => l) acc.affEdges
    { acc with
      weights := if uses.isEmpty then acc.weights else (mult, uses) :: acc.weights
      affEdges := affs }
  | .ret _ vs =>
    let mult := if inLoop then 10 else 1
    let uses := argVars vs
    { acc with
      weights := if uses.isEmpty then acc.weights else (mult, uses) :: acc.weights
      abiPref := addAbiList vs I.retRegs (4 * mult) acc.abiPref }
  | .exit _ _ as =>
    let mult := if inLoop then 10 else 1
    let uses := argVars as
    { acc with
      weights := if uses.isEmpty then acc.weights else (mult, uses) :: acc.weights
      abiPref := addAbiList as I.argRegs (4 * mult) acc.abiPref }
  | .stop => acc
  | .label _ k =>
    gather L loops bparamsMap inLoop k acc
  | .block l b rest =>
    let acc := gather L loops bparamsMap inLoop rest acc
    let bLoop := loops.contains l
    let bMult := if bLoop then 10 else 1
    let ps := b.params.1
    let body := b.params.2
    let acc := gatherParams L bMult ps body acc
    have : sizeOf body < sizeOf (Tree.block l b rest) :=
      Nat.lt_of_le_of_lt (params_sizeOf_le b) (by simp [Tree.block.sizeOf_spec]; omega)
    gather L loops bparamsMap bLoop body acc
termination_by sizeOf t

def bestRegBy {I : Isa} (score : I.Reg → Nat × Bool) :
    List I.Reg → Option I.Reg
  | [] => none
  | r0 :: rs =>
    some <| (rs.foldl (fun (best : I.Reg × (Nat × Bool)) r =>
      let sc := score r
      if sc.1 > best.2.1 || (sc.1 == best.2.1 && sc.2 && !best.2.2) then (r, sc) else best)
      (r0, score r0)).1

def firstFreeSlotAux : Nat → Nat → List Nat → Nat
  | 0, s, _ => s
  | fuel + 1, s, forb => if forb.contains s then firstFreeSlotAux fuel (s + 1) forb else s

def assocGet? {α : Type} (l : List (Nat × α)) (k : Nat) : Option α :=
  (l.find? (·.1 == k)).map (·.2)

def varWeight (x : Nat) (weights : List (Nat × List Nat)) : Nat :=
  weights.foldl (fun s (w, vs) => if vs.contains x then s + w else s) 0

def addForbLoc {I : Isa} (acc : List I.Reg × List Nat) : Option (Loc I) → List I.Reg × List Nat
  | some (.reg r) => (if acc.1.contains r then acc.1 else r :: acc.1, acc.2)
  | some (.slot s) => (acc.1, if acc.2.contains s then acc.2 else s :: acc.2)
  | none => acc

def colorVars {I : Isa} (crossList : List Nat) (acc : GatherAcc I)
    (fnParams : List Nat) : List (Nat × Loc I) × List I.Reg × Nat :=
  let abiPref : List (Nat × I.Reg × Nat) := addParamAbi fnParams I.argRegs 4 acc.abiPref
  let active := dedupOrd (acc.defInterf.map (·.1)) []
  let activePairs := active.map fun x => (varWeight x acc.weights, x)
  let order := sortByWeight activePairs
  let initPts := acc.pts.reverse
  let (home, usedCs, nslots, _) :=
    order.foldl (fun (st : List (Nat × Loc I) × List I.Reg × Nat × List (Nat × List Nat)) x =>
      let (home, usedCs, nslots, ptsState) := st
      let (forbRegs, forbSlots) :=
        acc.defInterf.foldl (fun (fb : List I.Reg × List Nat) (z, ys) =>
          if z == x then
            ys.foldl (fun fb' y =>
              if y == x then fb' else addForbLoc fb' (assocGet? home y)) fb
          else if ys.contains x then
            addForbLoc fb (assocGet? home z)
          else fb) ([], [])
      let canCaller := !(crossList.contains x) &&
        ptsState.all fun (b, vs) => !vs.contains x || b > 0
      let callerCands :=
        if canCaller then I.allocatable.filter fun r => !forbRegs.contains r else []
      let reuseCsCands := usedCs.filter fun r => !forbRegs.contains r
      let freeCands := callerCands ++ reuseCsCands
      let xAbi := abiPref.filterMap fun (u, r, w) => if u == x then some (r, w) else none
      let xAff := acc.affEdges.filterMap fun (u, v, w) =>
        if u == x && v != x then some (v, w)
        else if v == x && u != x then some (u, w)
        else none
      let prefScore (r : I.Reg) : Nat :=
        let s1 := xAbi.foldl (fun s (r', w) => if r == r' then s + w else s) 0
        xAff.foldl (fun s (y, w) =>
          match assocGet? home y with
          | some (.reg ry) => if ry == r then s + w else s
          | _ => s) s1
      match bestRegBy (fun r => (prefScore r, isAlloc r)) freeCands with
      | some bestR =>
        let home' := (x, .reg bestR) :: home
        let ptsState' :=
          if isAlloc bestR then
            ptsState.map fun (b, vs) => if vs.contains x then (b - 1, vs) else (b, vs)
          else ptsState
        (home', usedCs, nslots, ptsState')
      | none =>
        let wx := varWeight x acc.weights
        let newCsCands :=
          if wx ≥ 3 then I.calleeSaved.filter fun r => !usedCs.contains r && !forbRegs.contains r
          else []
        match bestRegBy (fun r => (prefScore r, false)) newCsCands with
        | some bestR =>
          ((x, .reg bestR) :: home, usedCs ++ [bestR], nslots, ptsState)
        | none =>
          let s := firstFreeSlotAux (forbSlots.length + 1) 0 forbSlots
          ((x, .slot s) :: home, usedCs, max nslots (s + 1), ptsState))
      ([], [], 0, initPts)
  (home, usedCs, nslots)

def emitParRegMovesAux {I : Isa} (tmp : I.Reg) :
    Nat → List (I.Reg × I.Reg) → List (Move I) → List (Move I)
  | 0, _, acc => acc.reverse
  | _, [], acc => acc.reverse
  | fuel + 1, pend, acc =>
    match pend.find? fun (d, _) => pend.all fun (_, s) => s != d with
    | some (d, s) =>
      let pend' := pend.filter fun p => !(p.1 == d && p.2 == s)
      let acc' := if d == s then acc else .mov d s :: acc
      emitParRegMovesAux tmp fuel pend' acc'
    | none =>
      match pend with
      | [] => acc.reverse
      | (d, s) :: rest =>
        if d == s then emitParRegMovesAux tmp fuel rest acc
        else
          let rest' := rest.map fun (d', s') => (d', if s' == d then tmp else s')
          emitParRegMovesAux tmp fuel ((d, s) :: rest') (.mov tmp d :: acc)

def emitParRegMoves {I : Isa} (pend : List (I.Reg × I.Reg)) : List (Move I) :=
  let pend := pend.filter fun (d, s) => d != s
  match I.scratch.head? with
  | some tmp => emitParRegMovesAux tmp (2 * pend.length + 2) pend []
  | none => pend.map fun (d, s) => .mov d s

def homeReg {I : Isa} (home : List (Nat × Loc I)) (x : Nat) : Option I.Reg :=
  match assocGet? home x with | some (.reg r) => some r | _ => none

def regHomes {I : Isa} (home : List (Nat × Loc I)) (xs : List Nat) : List I.Reg :=
  xs.filterMap (homeReg home)

def freshAlloc? {I : Isa} (busy : List I.Reg) : Option I.Reg :=
  I.allocatable.find? fun r => !busy.contains r

def pickPloc {I : Isa} (home : List (Nat × Loc I)) (liveL : List Nat)
    (ps : List Nat) (usedCs : List I.Reg) : List I.Reg × List I.Reg :=
  let liveRegs := regHomes home liveL
  let reserved := ps.filterMap (homeReg home)
  let initBusy := liveRegs ++ reserved
  let (outRev, _, cs') :=
    ps.foldl (fun (acc : List I.Reg × List I.Reg × List I.Reg) p =>
      let (out, busy, cs) := acc
      match homeReg home p with
      | some r => (r :: out, busy, cs)
      | none =>
        match (I.allocatable ++ cs).find? fun r => !busy.contains r with
        | some r => (r :: out, r :: busy, cs)
        | none =>
          match I.calleeSaved.find? fun r => !busy.contains r && !cs.contains r with
          | some r => (r :: out, r :: busy, cs ++ [r])
          | none =>
            match I.allocatable.head? with
            | some r => (r :: out, r :: busy, cs)
            | none => (out, busy, cs)) ([], initBusy, usedCs)
  (outRev.reverse, cs')

structure EmitSt (I : Isa) where
  dest : List (Nat × I.Reg)
  ploc : List (Nat × List I.Reg)
  pre : List (Nat × List (Move I))
  usedCs : List I.Reg

def buildPre {I : Isa} (home : List (Nat × Loc I)) (ipLive : List Nat)
    (ops : List Nat) (pendSt : List (Nat × Nat × I.Reg))
    (pendReg : List (Nat × I.Reg × I.Reg)) : List (Move I) :=
  let stMvs : List (Move I) := pendSt.map fun (_, s, r) => .st s r
  let regMvs : List (Move I) := emitParRegMoves (pendReg.map fun (_, d, s) => (d, s))
  let writtenByReg := pendReg.map fun (_, d, _) => d
  let inRegFromSt : List (Nat × I.Reg) :=
    pendSt.filterMap fun (x, _, r) =>
      if !writtenByReg.contains r then some (x, r) else none
  let initBusy := regHomes home ipLive ++ inRegFromSt.filterMap fun (x, r) =>
    if ops.contains x then some r else none
  let (_, ldMvs) := ops.foldl (fun (acc : List I.Reg × List (Move I)) v =>
    let (busy, mvs) := acc
    match assocGet? home v with
    | some (.reg _) => (busy, mvs)
    | some (.slot s) =>
      if inRegFromSt.any (fun (x, _) => x == v) then (busy, mvs)
      else
        match freshAlloc? busy with
        | some r => (r :: busy, mvs ++ [.ld r s])
        | none => (busy, mvs)
    | none => (busy, mvs)) (initBusy, [])
  stMvs ++ regMvs ++ ldMvs

def emitAlloc {I : Isa} (L : LiveMap) (home : List (Nat × Loc I)) :
    Tree → List I.Reg → List (Nat × Nat × I.Reg) → List (Nat × I.Reg × I.Reg) →
    EmitSt I → EmitSt I
  | .param x k, pl, pSt, pReg, st =>
    match pl with
    | [] => emitAlloc L home k [] pSt pReg st
    | rArr :: pl' =>
      let (pSt', pReg') :=
        match assocGet? home x with
        | some (.reg rHome) =>
          if rHome == rArr then (pSt, pReg) else (pSt, (x, rHome, rArr) :: pReg)
        | some (.slot s) => ((x, s, rArr) :: pSt, pReg)
        | none => (pSt, pReg)
      emitAlloc L home k pl' pSt' pReg' st
  | node@(.let_ ip x op k), _, pSt, pReg, st =>
    let ops := opUseVars op
    let preMvs := buildPre home (liveIn L node) ops pSt pReg
    let la := liveIn L k
    let (dOpt, pStNext) : Option I.Reg × List (Nat × Nat × I.Reg) :=
      match assocGet? home x with
      | some (.reg r) => (some r, [])
      | some (.slot s) =>
        let busy := regHomes home (la.filter (· != x))
        let pref : Option I.Reg := match op with
          | .bin _ _ (.var a) _ | .copy _ (.var a) | .ext _ _ _ (.var a) =>
            match homeReg home a with
            | some ra => if isAlloc ra && !busy.contains ra then some ra else none
            | none => none
          | _ => none
        match pref <|> freshAlloc? busy with
        | some d => (some d, [(x, s, d)])
        | none => (none, [])
      | none => (freshAlloc? (regHomes home la), [])
    let st := match dOpt with
      | some d => { st with dest := (x, d) :: st.dest, pre := (ip, preMvs) :: st.pre }
      | none => { st with pre := (ip, preMvs) :: st.pre }
    emitAlloc L home k [] pStNext [] st
  | node@(.load ip x a k), _, pSt, pReg, st =>
    let ops := argVars [a]
    let preMvs := buildPre home (liveIn L node) ops pSt pReg
    let la := liveIn L k
    let (dOpt, pStNext) : Option I.Reg × List (Nat × Nat × I.Reg) :=
      match assocGet? home x with
      | some (.reg r) => (some r, [])
      | some (.slot s) =>
        match freshAlloc? (regHomes home (la.filter (· != x))) with
        | some d => (some d, [(x, s, d)])
        | none => (none, [])
      | none => (freshAlloc? (regHomes home la), [])
    let st := match dOpt with
      | some d => { st with dest := (x, d) :: st.dest, pre := (ip, preMvs) :: st.pre }
      | none => { st with pre := (ip, preMvs) :: st.pre }
    emitAlloc L home k [] pStNext [] st
  | node@(.store ip v a k), _, pSt, pReg, st =>
    let ops := dedupOrd (argVars [v, a]) []
    let preMvs := buildPre home (liveIn L node) ops pSt pReg
    let st := { st with pre := (ip, preMvs) :: st.pre }
    emitAlloc L home k [] [] [] st
  | node@(.call ip _ _ k), _, pSt, pReg, st =>
    let preMvs := buildPre home (liveIn L node) [] pSt pReg
    let st := { st with pre := (ip, preMvs) :: st.pre }
    emitAlloc L home k I.retRegs [] [] st
  | node@(.jnz ip c _ t e), _, pSt, pReg, st =>
    let preMvs := buildPre home (liveIn L node) [c] pSt pReg
    let st := { st with pre := (ip, preMvs) :: st.pre }
    let st := emitAlloc L home e [] [] [] st
    emitAlloc L home t [] [] [] st
  | node@(.skip ip k), _, pSt, pReg, st =>
    let preMvs := buildPre home (liveIn L node) [] pSt pReg
    let st := { st with pre := (ip, preMvs) :: st.pre }
    emitAlloc L home k [] [] [] st
  | node@(.jump ip _ _), _, pSt, pReg, st
  | node@(.ret ip _), _, pSt, pReg, st
  | node@(.exit ip _ _), _, pSt, pReg, st =>
    let preMvs := buildPre home (liveIn L node) [] pSt pReg
    { st with pre := (ip, preMvs) :: st.pre }
  | .stop, _, _, _, st => st
  | .label _ k, pl, pSt, pReg, st =>
    emitAlloc L home k pl pSt pReg st
  | .block l b rest, pl, pSt, pReg, st =>
    let st := emitAlloc L home rest pl pSt pReg st
    let (ps, _) := b.params
    let (regs, cs') := pickPloc home (L.get l) ps st.usedCs
    let st := { st with ploc := (l, regs) :: st.ploc, usedCs := cs' }
    emitAlloc L home b regs [] [] st

/-- Hints for `Rega.lower` from the graph-coloring register allocator. -/
def hints (I : Isa) (f : Fn) : Rega.Hints I :=
  let t := Tree.ofFn f
  let L := liveLabels t
  let loops := loopBlocks t
  let bparamsMap := t.blocks.map fun (l, b) => (l, b.params.1)
  let initAcc : GatherAcc I :=
    { weights := []
      defInterf := []
      pts := []
      abiPref := []
      affEdges := [] }
  let acc := gather L loops bparamsMap false t initAcc
  let crossList := acrossCalls L t
  let (fnParams, _) := t.params
  let (home, usedCs, nslots) := colorVars crossList acc fnParams
  let est := emitAlloc L home t I.argRegs [] [] ⟨[], [], [], usedCs⟩
  { dest := fun x => assocGet? est.dest x
    entry := fun l =>
      { live := (L.get l).filterMap fun x => (assocGet? home x).map fun loc => (.var x, loc)
        ploc := (assocGet? est.ploc l).getD [] }
    pre := fun ip => (assocGet? est.pre ip).getD []
    nslots := nslots
    saved := est.usedCs }

end Spill
end LeanQbe
