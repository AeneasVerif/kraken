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

inductive Home
  | none
  | reg (r : Nat)
  | slot (s : Nat)

def mergeSorted : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | 0, _, _, acc => acc.reverse
  | _, [], ys, acc => acc.reverseAux ys
  | _, xs, [], acc => acc.reverseAux xs
  | fuel + 1, x :: xs, y :: ys, acc =>
    if Nat.ble (y.1 + 1) x.1 || (Nat.beq x.1 y.1 && Nat.ble (x.2 + 1) y.2) then
      mergeSorted fuel xs (y :: ys) (x :: acc)
    else mergeSorted fuel (x :: xs) ys (y :: acc)

def sortByWeight (nv : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec pass : List (List (Nat × Nat)) → List (List (Nat × Nat))
    | xs :: ys :: rest => mergeSorted (nv + 2) xs ys [] :: pass rest
    | xss => xss
  let rec go : Nat → List (List (Nat × Nat)) → List (Nat × Nat)
    | _, [xs] => xs
    | fuel + 1, xss@(_ :: _ :: _) => go fuel (pass xss)
    | _, xss => xss.headD []
  go (nv + 2) (xs.map (· :: []))

structure GatherAcc where
  weights : List (Nat × List Nat)
  defInterf : List (Nat × List Nat)
  pts : List (Nat × List Nat)
  abiPref : List (Nat × Nat × Nat)
  affEdges : List (Nat × Nat × Nat)

def addAbiList : List (Arg Nat) → List Nat → Nat →
    List (Nat × Nat × Nat) → List (Nat × Nat × Nat)
  | .var x :: as, r :: rs, mult, acc => addAbiList as rs mult ((x, r, mult) :: acc)
  | .imm _ :: as, _ :: rs, mult, acc => addAbiList as rs mult acc
  | _, _, _, acc => acc

def addParamAbi (ps rs : List Nat) (mult : Nat) (acc : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat) :=
  (ps.zip rs).foldl (fun l (x, r) => (x, r, mult) :: l) acc

def addWeight (mult : Nat) (uses : List Nat) (ws : List (Nat × List Nat)) : List (Nat × List Nat) :=
  if uses.isEmpty then ws else (mult, uses) :: ws

def addPt (allocLen : Nat) (hasCalls : Bool) (crossTree : Arr Bool)
    (need : Nat) (vars : List Nat) (pts : List (Nat × List Nat)) : List (Nat × List Nat) :=
  let b := allocLen - need
  if Nat.ble 1 need && Nat.ble (b + 1) vars.length then
    let cVars := if hasCalls then vars.filter (!crossTree.get ·) else vars
    if Nat.ble (b + 1) cVars.length then
      match pts with
      | (b0, vs0) :: pts' =>
        if cVars == vs0 then (if Nat.ble (b + 1) b0 then (b, vs0) :: pts' else pts)
        else (b, cVars) :: pts
      | [] => [(b, cVars)]
    else pts
  else pts

def gather (allocLen : Nat) (hasCalls : Bool) (argRegs retRegs : List Nat)
    (crossTree loops : Arr Bool) (bparamsTree : Arr (List Nat)) :
    Nat → List Nat → Tree → GatherAcc → GatherAcc :=
  let rec go : Nat → List Nat → Tree → GatherAcc → GatherAcc
    | mult, psRev, .param _ x k, ⟨ws, di, pts, abi, aff⟩ =>
      match k with
      | .param .. => go mult (x :: psRev) k ⟨ws, di, pts, abi, aff⟩
      | _ =>
        let ps := (x :: psRev).reverse
        let le := k.lv
        let di := ps.foldl (fun d p => if natMem p le then (p, le) :: d else d) di
        go mult [] k ⟨addWeight mult ps ws, di, pts, abi, aff⟩
    | mult, _, .let_ lv _ x op k, ⟨ws, di, pts, abi, aff⟩ =>
      let la := k.lv
      let uses := opVars op
      let aff := match op with
        | .copy _ (.var a) | .ext _ _ _ (.var a) => (x, a, 6 * mult) :: aff
        | .bin _ _ (.var a) _ => if !natMem a la then (x, a, 5 * mult) :: aff else aff
        | _ => aff
      let di := if natMem x la then (x, la) :: di else di
      let pts := addPt allocLen hasCalls crossTree (max uses.length 1) lv pts
      go mult [] k ⟨(mult, x :: uses) :: ws, di, pts, abi, aff⟩
    | mult, _, .load lv _ x a k, ⟨ws, di, pts, abi, aff⟩ =>
      let la := k.lv
      let di := if natMem x la then (x, la) :: di else di
      let pts := addPt allocLen hasCalls crossTree 1 lv pts
      go mult [] k ⟨(mult, x :: argVars [a]) :: ws, di, pts, abi, aff⟩
    | mult, _, .store lv _ v a k, ⟨ws, di, pts, abi, aff⟩ =>
      let uses := dedup (argVars [v, a])
      let pts := addPt allocLen hasCalls crossTree uses.length lv pts
      go mult [] k ⟨addWeight mult uses ws, di, pts, abi, aff⟩
    | mult, _, .call _ _ _ as k, ⟨ws, di, pts, abi, aff⟩ =>
      let uses := dedup (argVars as)
      let abi := addParamAbi k.paramVars retRegs (4 * mult) (addAbiList as argRegs (4 * mult) abi)
      go mult [] k ⟨addWeight mult uses ws, di, pts, abi, aff⟩
    | mult, _, .jnz lv _ c _ t e, ⟨ws, di, pts, abi, aff⟩ =>
      let pts := addPt allocLen hasCalls crossTree 1 lv pts
      go mult [] t (go mult [] e ⟨(mult, [c]) :: ws, di, pts, abi, aff⟩)
    | mult, _, .skip _ _ k, acc | mult, _, .label _ _ k, acc => go mult [] k acc
    | mult, _, .jump _ _ j as, ⟨ws, di, pts, abi, aff⟩ =>
      ⟨addWeight mult (dedup (argVars as)) ws, di, pts, abi,
        addAbiList as (bparamsTree.get j) (8 * mult) aff⟩
    | mult, _, .ret _ _ vs, ⟨ws, di, pts, abi, aff⟩ =>
      ⟨addWeight mult (dedup (argVars vs)) ws, di, pts, addAbiList vs retRegs (4 * mult) abi, aff⟩
    | mult, _, .exit _ _ _ as, ⟨ws, di, pts, abi, aff⟩ =>
      ⟨addWeight mult (dedup (argVars as)) ws, di, pts, addAbiList as argRegs (4 * mult) abi, aff⟩
    | _, _, .stop, acc => acc
    | mult, _, .block _ l b rest, acc =>
      go (if loops.get l then 10 else 1) [] b (go mult [] rest acc)
  go

def firstFreeSlotAux : Nat → Nat → List Nat → Nat
  | 0, s, _ => s
  | fuel + 1, s, forb => if natMem s forb then firstFreeSlotAux fuel (s + 1) forb else s

def regHomes (home : Arr Home) (xs : List Nat) : List Nat :=
  xs.filterMap fun x => match home.get x with | .reg r => some r | _ => none

def bestRegPref (xPrefs : List (Nat × Nat)) : List Nat → Option Nat
  | [] => none
  | r0 :: rs =>
    let score (r : Nat) : Nat :=
      xPrefs.foldl (fun s (r', w) => if Nat.beq r r' then s + w else s) 0
    some (rs.foldl (fun (bestR, bestSc) r =>
      let sc := score r
      if Nat.ble (bestSc + 1) sc then (r, sc) else (bestR, bestSc)) (r0, score r0)).1

def colorVars (nAlloc : Nat) (allocatable calleeSaved argRegs : List Nat)
    (nv : Nat) (crossTree : Arr Bool) (acc : GatherAcc)
    (fnParams : List Nat) : Arr Home × List Nat × Nat :=
  let ⟨weights, defInterf, pts, abiPref0, affEdges⟩ := acc
  let abiPref := addParamAbi fnParams argRegs 4 abiPref0
  let wTree := weights.foldl (fun t (w, vs) =>
    vs.foldl (fun t x => t.mod x (· + w)) t) (Arr.ofSize nv 0)
  let order := sortByWeight nv (defInterf.map fun (x, _) => (wTree.get x, x))
  let interfTree := defInterf.foldl (fun t (z, ys) =>
    let (zList, t) := ys.foldl (fun (zAcc, t) y =>
      if Nat.beq y z then (zAcc, t) else (y :: zAcc, t.push y z)) (t.get z, t)
    t.set z zList) (Arr.ofSize nv [])
  let (ptBudget0, varPts, _) := pts.foldl (fun (pb, vp, pid) (b, vs) =>
    (pb.set pid b, vs.foldl (fun vp x => vp.push x pid) vp, pid + 1))
    (Arr.ofSize pts.length 0, Arr.ofSize nv [], 0)
  let abiTree := abiPref.foldl (fun t (u, r, w) => t.push u (r, w)) (Arr.ofSize nv [])
  let affTree := affEdges.foldl (fun t (u, v, w) =>
    if Nat.beq u v then t else (t.push u (v, w)).push v (u, w)) (Arr.ofSize nv [])
  let (home, usedCs, nslots, _) := order.foldl (fun (homeTree, usedCs, nslots, ptBudget) (wx, x) =>
    let xInterf := interfTree.get x
    let forbRegs := xInterf.foldl (fun rs y =>
      match homeTree.get y with | .reg r => if natMem r rs then rs else r :: rs | _ => rs) []
    let xPids := varPts.get x
    let callerCands :=
      if !crossTree.get x && xPids.all (fun pid => Nat.ble 1 (ptBudget.get pid)) then
        allocatable.filter (!natMem · forbRegs)
      else []
    let freeCands := callerCands ++ usedCs.filter (!natMem · forbRegs)
    let xPrefs := (affTree.get x).foldl (fun prefs (y, w) =>
      match homeTree.get y with | .reg ry => (ry, w) :: prefs | _ => prefs) (abiTree.get x)
    match bestRegPref xPrefs freeCands with
    | some bestR =>
      let ptBudget' :=
        if Nat.ble (bestR + 1) nAlloc then xPids.foldl (fun pb pid => pb.mod pid (· - 1)) ptBudget
        else ptBudget
      (homeTree.set x (.reg bestR), usedCs, nslots, ptBudget')
    | none =>
      let newCsCands :=
        if Nat.ble 3 wx then calleeSaved.filter fun r => !natMem r usedCs && !natMem r forbRegs
        else []
      match bestRegPref xPrefs newCsCands with
      | some bestR => (homeTree.set x (.reg bestR), usedCs ++ [bestR], nslots, ptBudget)
      | none =>
        let forbSlots := xInterf.foldl (fun ss y =>
          match homeTree.get y with | .slot s => if natMem s ss then ss else s :: ss | _ => ss) []
        let s := firstFreeSlotAux (forbSlots.length + 1) 0 forbSlots
        (homeTree.set x (.slot s), usedCs, max nslots (s + 1), ptBudget))
    (Arr.ofSize nv .none, [], 0, ptBudget0)
  (home, usedCs, nslots)

def emitParRegMovesAux {I : Isa} (regArr : Arr I.Reg) (tmp : Nat) :
    Nat → List (Nat × Nat) → List (Move I) → List (Move I)
  | 0, _, acc | _, [], acc => acc.reverse
  | fuel + 1, pend, acc =>
    match pend.find? fun (d, _) => pend.all fun (_, s) => s != d with
    | some (d, s) =>
      let pend' := pend.filter fun p => !(p.1 == d && p.2 == s)
      let acc' := if d == s then acc else .mov (regArr.get d) (regArr.get s) :: acc
      emitParRegMovesAux regArr tmp fuel pend' acc'
    | none =>
      match pend with
      | [] => acc.reverse
      | (d, s) :: rest =>
        if d == s then emitParRegMovesAux regArr tmp fuel rest acc
        else
          let rest' := rest.map fun (d', s') => (d', if s' == d then tmp else s')
          emitParRegMovesAux regArr tmp fuel ((d, s) :: rest')
            (.mov (regArr.get tmp) (regArr.get d) :: acc)

def emitParRegMoves {I : Isa} (regArr : Arr I.Reg) (scrOpt : Option Nat)
    (pend : List (Nat × Nat)) : List (Move I) :=
  let pend := pend.filter fun (d, s) => d != s
  match scrOpt with
  | some tmp => emitParRegMovesAux regArr tmp (2 * pend.length + 2) pend []
  | none => pend.map fun (d, s) => .mov (regArr.get d) (regArr.get s)

def freshAlloc? (allocatable : List Nat) (busy : List Nat) : Option Nat :=
  allocatable.find? (!natMem · busy)

def pickPloc (allocatable calleeSaved : List Nat) (home : Arr Home)
    (liveL : List Nat) (ps : List Nat) (usedCs : List Nat) : List Nat × List Nat :=
  let initBusy := regHomes home liveL ++ regHomes home ps
  let (outRev, _, cs') := ps.foldl (fun (out, busy, cs) p =>
    match home.get p with
    | .reg r => (r :: out, busy, cs)
    | _ =>
      match (allocatable ++ cs).find? (!natMem · busy) with
      | some r => (r :: out, r :: busy, cs)
      | none =>
        match calleeSaved.find? fun r => !natMem r busy && !natMem r cs with
        | some r => (r :: out, r :: busy, cs ++ [r])
        | none =>
          match allocatable.head? with
          | some r => (r :: out, r :: busy, cs)
          | none => (out, busy, cs)) ([], initBusy, usedCs)
  (outRev.reverse, cs')

structure EmitSt (I : Isa) where
  dest : Arr (Option I.Reg)
  entry : Arr (Entry I)
  pre : Arr (List (Move I))
  usedCs : List Nat

def buildPre {I : Isa} (regArr : Arr I.Reg) (allocatable : List Nat) (scrOpt : Option Nat)
    (home : Arr Home) (ipLive : List Nat) (ops : List Nat) (pendSt : List (Nat × Nat × Nat))
    (pendReg : List (Nat × Nat × Nat)) : List (Move I) :=
  let stMvs : List (Move I) := pendSt.map fun (_, s, r) => .st s (regArr.get r)
  let regMvs : List (Move I) :=
    emitParRegMoves regArr scrOpt (pendReg.map fun (_, d, s) => (d, s))
  if !ops.any (fun v => match home.get v with | .slot _ => true | _ => false) then
    stMvs ++ regMvs
  else
    let writtenByReg := pendReg.map fun (_, d, _) => d
    let inRegFromSt : List (Nat × Nat) :=
      pendSt.filterMap fun (x, _, r) => if !natMem r writtenByReg then some (x, r) else none
    let initBusy := regHomes home ipLive ++ inRegFromSt.filterMap fun (x, r) =>
      if natMem x ops then some r else none
    let (_, ldMvsRev) := ops.foldl (fun (busy, mvs) v =>
      match home.get v with
      | .slot s =>
        if inRegFromSt.any (fun (x, _) => Nat.beq x v) then (busy, mvs)
        else
          match freshAlloc? allocatable busy with
          | some r => (r :: busy, .ld (regArr.get r) s :: mvs)
          | none => (busy, mvs)
      | _ => (busy, mvs)) (initBusy, [])
    stMvs ++ regMvs ++ ldMvsRev.reverse

def recordPre {I : Isa} (ip : Nat) (mvs : List (Move I))
    (pre : Arr (List (Move I))) : Arr (List (Move I)) :=
  if mvs.isEmpty then pre else pre.set ip mvs

def canFuseCmp {I : Isa} (home : Arr Home) (x : Nat) (op : Op Nat) (k : Tree) : Bool :=
  match op, k with
  | .cmp cls co _ _, .jnz _ _ c _ t e =>
    Nat.beq c x && !natMem x t.lv && !natMem x e.lv &&
      (match home.get x with
       | .slot _ => false
       | _ => (I.jnzCmp cls co (.imm 0) (.imm 0) "").isSome)
  | _, _ => false

def allocDef {I : Isa} (regArr : Arr I.Reg) (nAlloc : Nat) (allocatable : List Nat)
    (home : Arr Home) (x : Nat) (la : List Nat) (op? : Option (Op Nat))
    (dest : Arr (Option I.Reg)) : Arr (Option I.Reg) × List (Nat × Nat × Nat) :=
  let (dOpt, pStNext) : Option Nat × List (Nat × Nat × Nat) := match home.get x with
    | .reg r => (some r, [])
    | .slot s =>
      let busy := regHomes home (erase x la)
      let pref : Option Nat := match op? with
        | some (.bin _ _ (.var a) _) | some (.copy _ (.var a)) | some (.ext _ _ _ (.var a)) =>
          match home.get a with
          | .reg ra => if Nat.ble (ra + 1) nAlloc && !natMem ra busy then some ra else none
          | _ => none
        | _ => none
      match pref <|> freshAlloc? allocatable busy with
      | some d => (some d, [(x, s, d)])
      | none => (none, [])
    | .none => (freshAlloc? allocatable (regHomes home la), [])
  (match dOpt with | some d => dest.set x (some (regArr.get d)) | none => dest, pStNext)

def emitAlloc {I : Isa} (regArr : Arr I.Reg) (nAlloc : Nat)
    (allocatable calleeSaved retRegs : List Nat) (scrOpt : Option Nat)
    (lTree : Arr (List Nat)) (home : Arr Home) :
    Tree → List Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat) →
    EmitSt I → EmitSt I :=
  let rec go : Tree → List Nat → List (Nat × Nat × Nat) → List (Nat × Nat × Nat) →
      EmitSt I → EmitSt I
    | .param _ x k, pl, pSt, pReg, st =>
      match pl with
      | [] => go k [] pSt pReg st
      | rArr :: pl' =>
        let (pSt', pReg') := match home.get x with
          | .reg rHome =>
            if Nat.beq rHome rArr then (pSt, pReg) else (pSt, (x, rHome, rArr) :: pReg)
          | .slot s => ((x, s, rArr) :: pSt, pReg)
          | .none => (pSt, pReg)
        go k pl' pSt' pReg' st
    | .let_ lv ip x op k, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩ =>
      let pre := recordPre ip (buildPre regArr allocatable scrOpt home lv (opVars op) pSt pReg) pre
      if canFuseCmp (I := I) home x op k then
        go k [] [] [] ⟨dest, entry, pre, usedCs⟩
      else
        let (dest, pStNext) := allocDef regArr nAlloc allocatable home x k.lv (some op) dest
        go k [] pStNext [] ⟨dest, entry, pre, usedCs⟩
    | .load lv ip x a k, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩ =>
      let pre :=
        recordPre ip (buildPre regArr allocatable scrOpt home lv (argVars [a]) pSt pReg) pre
      let (dest, pStNext) := allocDef regArr nAlloc allocatable home x k.lv none dest
      go k [] pStNext [] ⟨dest, entry, pre, usedCs⟩
    | .store lv ip v a k, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩ =>
      let pre := recordPre ip
        (buildPre regArr allocatable scrOpt home lv (dedup (argVars [v, a])) pSt pReg) pre
      go k [] [] [] ⟨dest, entry, pre, usedCs⟩
    | .call lv ip _ _ k, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩ =>
      let pre := recordPre ip (buildPre regArr allocatable scrOpt home lv [] pSt pReg) pre
      go k retRegs [] [] ⟨dest, entry, pre, usedCs⟩
    | .jnz lv ip c _ t e, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩ =>
      let pre := recordPre ip (buildPre regArr allocatable scrOpt home lv [c] pSt pReg) pre
      go t [] [] [] (go e [] [] [] ⟨dest, entry, pre, usedCs⟩)
    | .skip lv ip k, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩ =>
      let pre := recordPre ip (buildPre regArr allocatable scrOpt home lv [] pSt pReg) pre
      go k [] [] [] ⟨dest, entry, pre, usedCs⟩
    | .jump lv ip _ _, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩
    | .ret lv ip _, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩
    | .exit lv ip _ _, _, pSt, pReg, ⟨dest, entry, pre, usedCs⟩ =>
      ⟨dest, entry,
        recordPre ip (buildPre regArr allocatable scrOpt home lv [] pSt pReg) pre, usedCs⟩
    | .stop, _, _, _, st => st
    | .label _ _ k, pl, pSt, pReg, st => go k pl pSt pReg st
    | .block _ l b rest, pl, pSt, pReg, st =>
      let ⟨dest, entry, pre, usedCs⟩ := go rest pl pSt pReg st
      let lv := lTree.get l
      let (regs, cs') := pickPloc allocatable calleeSaved home lv b.paramVars usedCs
      let liveL := lv.filterMap fun x => match home.get x with
        | .reg r => some (.var x, .reg (regArr.get r))
        | .slot s => some (.var x, .slot s)
        | .none => none
      go b regs [] [] ⟨dest, entry.set l ⟨liveL, regs.map regArr.get⟩, pre, cs'⟩
  go

/-- Hints for `Rega.lower` from the graph-coloring register allocator. -/
def hints (I : Isa) (f : Fn) : Rega.Hints I :=
  let nAlloc := I.allocatable.length
  let nCs := I.calleeSaved.length
  let allRegs := I.allocatable ++ I.calleeSaved ++ I.scratch
  let (regArr, _) := allRegs.foldl (fun (a, i) r => (a.set i r, i + 1))
    (Arr.ofSize allRegs.length I.sp, 0)
  let allocIds := List.range nAlloc
  let csIds := (List.range nCs).map (· + nAlloc)
  let argIds := I.argRegs.map allRegs.idxOf
  let retIds := I.retRegs.map allRegs.idxOf
  let scrOpt : Option Nat := if I.scratch.isEmpty then none else some (nAlloc + nCs)
  let (t0, nv, nl, nip) := Tree.ofFnWithSizes f
  let bs0 := t0.blocks
  let lTree := liveLabelsArr nl bs0
  let (_, t) := fillLive lTree t0
  let crossList := acrossCalls t
  let crossTree := crossList.foldl (fun a x => a.set x true) (Arr.ofSize nv false)
  let loops := (loopBlocksWithSize nl bs0).foldl (fun a l => a.set l true) (Arr.ofSize nl false)
  let bparamsTree := bs0.foldl (fun a (l, b) => a.set l b.paramVars) (Arr.ofSize nl [])
  let acc := gather nAlloc (!crossList.isEmpty) argIds retIds crossTree loops bparamsTree
    1 [] t ⟨[], [], [], [], []⟩
  let (home, usedCs, nslots) := colorVars nAlloc allocIds csIds argIds nv crossTree acc t0.paramVars
  let ⟨dest, entries, pre, savedIds⟩ :=
    emitAlloc regArr nAlloc allocIds csIds retIds scrOpt lTree home t argIds [] []
      ⟨Arr.ofSize nv none, Arr.ofSize nl ⟨[], []⟩, Arr.ofSize nip [], usedCs⟩
  { dest := dest.get
    entry := entries.get
    pre := pre.get
    nslots := nslots
    saved := savedIds.map regArr.get }

end Spill
end LeanQbe
