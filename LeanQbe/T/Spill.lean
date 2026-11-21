module

public import LeanQbe.T.Live
public import LeanQbe.T.SpillFlags

/-!
# Priority Graph-Coloring Register Allocator & Spilling Oracle (`T7a`, `L-E1.2`, untrusted)

Full port of E1's priority graph-coloring allocator extended to typed banks (`GPR` + `Vec` + local
flag hints): cross-call spilling, `calleeSaved` promotion, `abiPref`, `affEdges`, `ptBudget`,
`10 * mult` loop depth weights, destructive `allocDef`, unified multi-granule spill slots, and
GPR/Vec parallel-move cycle breaking via `scratch`/`vecScratch`.

## Per-call live-range splitting

A call-crossing variable is no longer banned from caller-saved registers function-wide. When its
call-crossing weight (`callW`, the loop-weighted number of calls it is live across) is cheap
relative to its use weight, it is *split*: it keeps a caller-saved GPR (or vector register) home
plus a private backup slot. The `PreStep` of every `.call` it crosses stores it (once per
straight-line path), and it is reloaded lazily, right before its next use or before a `.jump`
whose target expects it in its home register. Paths without calls never touch its backup slot,
so cold-branch calls no longer cost the hot path any spills (automatic shrink-wrapping).

The emitted hints obey the `Rega` checker's rules: definitions always land in registers
(`resolveDsts`), slot-to-register reloads before a `.jump` are explicit `PreStep` loads (never a
`.slot` source in the `shuffle`, which `locBlocked` cannot see), vectors cross calls only via
`.vst`/`.vld` (`afterCallState` drops vector and flag registers), call-crossing booleans are
never flag-allocated (`SpillFlags`), and every `PreStep` lists its moves in execution order.

Untrusted: `Rega.lowerFn` checks every hint, so any heuristic bug can only fail lowering.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Spill

open Live Rega SpillFlags

inductive Home (Cond : Type) where
  | none | gpr (r : Nat) | vec (v : Nat) | flag (c : Cond) | slot (s : Nat) (w : SlotWidth)
  deriving Inhabited

/-! ## Sorting, Intervals, and Preferences -/

def mergeSorted : Nat → List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat) →
    List (Nat × Nat)
  | 0, _, _, acc => acc.reverse
  | _, [], ys, acc => acc.reverseAux ys
  | _, xs, [], acc => acc.reverseAux xs
  | fuel + 1, x :: xs, y :: ys, acc =>
    if Nat.ble (y.1 + 1) x.1 || (Nat.beq x.1 y.1 && Nat.ble (x.2 + 1) y.2) then
      mergeSorted fuel xs (y :: ys) (x :: acc)
    else mergeSorted fuel (x :: xs) ys (y :: acc)

def sortByWeight (nv : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec pass : List (List (Nat × Nat)) → List (List (Nat × Nat))
    | a :: b :: rest => mergeSorted (nv + 2) a b [] :: pass rest
    | xss => xss
  let rec go : Nat → List (List (Nat × Nat)) → List (Nat × Nat)
    | _, [xs] => xs
    | fuel + 1, xss@(_ :: _ :: _) => go fuel (pass xss)
    | _, xss => xss.headD []
  go (nv + 2) (xs.map (· :: []))

def firstFreeSlotRange (k : Nat) (forb : List (Nat × Nat)) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, s => s
    | f + 1, s => if forb.any fun (s', k') => rangesOverlap s k s' k' then go f (s + 1) else s
  go (forb.length * 8 + 2) 0

def bestRegPref (xPrefs : List (Nat × Nat)) : List Nat → Option Nat
  | [] => none
  | r0 :: rs =>
    let score (r : Nat) : Nat :=
      xPrefs.foldl (fun s (r', w) => if Nat.beq r r' then s + w else s) 0
    some (rs.foldl (fun (bestR, bestSc) r =>
      let sc := score r
      if Nat.ble (bestSc + 1) sc then (r, sc) else (bestR, bestSc)) (r0, score r0)).1

def abiIdList {I : Isa} (allGpr : List I.Reg) (allVec : List I.VReg) :
    {ts : List Ty} → Tup (AbiReg I.Reg I.VReg) ts → List (Option (Sum Nat Nat))
  | [], () => []
  | _ :: _, (.gpr r, locs) => some (.inl (allGpr.idxOf r)) :: abiIdList allGpr allVec locs
  | _ :: _, (.vec v, locs) => some (.inr (allVec.idxOf v)) :: abiIdList allGpr allVec locs

def tupArgsToList : {ts : List Ty} → Tup (Arg VNat) ts → List (Option Nat)
  | [], () => []
  | _ :: _, (.var x, as) => some x :: tupArgsToList as
  | _ :: _, (.imm _, as) => none :: tupArgsToList as

def addAbiArgs (as : List (Option Nat)) (ids : List (Option (Sum Nat Nat))) (mult : Nat)
    (gAcc vAcc : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) × List (Nat × Nat × Nat) :=
  (as.zip ids).foldl (fun (ga, va) (ao, ido) =>
    match ao, ido with
    | some x, some (.inl r) => ((x, r, mult) :: ga, va)
    | some x, some (.inr v) => (ga, (x, v, mult) :: va)
    | _, _ => (ga, va)) (gAcc, vAcc)

def addAffZip (as : List (Option Nat)) (ps : List Nat) (mult : Nat)
    (acc : List (Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  (as.zip ps).foldl (fun a (ao, p) => match ao with | some x => (x, p, mult) :: a | none => a) acc

/-! ## Local Flag & Variant Probing (`L3`, `L7`) -/

def firstOpVar {ts : List Ty} (op : Op VNat ts) : Option Nat × Bool :=
  let { sig := _, code, args } := op
  match code, args with
  | .copy _, (.var a, ()) | .zext _ _, (.var a, ()) | .sext _ _, (.var a, ())
  | .trunc _ _, (.var a, ()) | .bitcast _ _ _, (.var a, ()) => (some a, true)
  | .add _, (.var a, _, ()) | .sub _, (.var a, _, ()) | .mul _, (.var a, _, ())
  | .and _, (.var a, _, ()) | .or _, (.var a, _, ()) | .xor _, (.var a, _, ())
  | .shl _, (.var a, _, ()) | .lshr _, (.var a, _, ()) | .ashr _, (.var a, _, ())
  | .rotl _, (.var a, _, ()) | .rotr _, (.var a, _, ())
  | .addc _, (.var a, _, _, ()) | .subb _, (.var a, _, _, ()) => (some a, false)
  | _, _ => (none, false)

/-! ## Interference, Weights, Pressure Points, and Priority Coloring -/

structure Ctx (I : Isa) where
  (allGpr : List I.Reg) (allVec : List I.VReg) (gReg : Trie I.Reg) (vReg : Trie I.VReg)
  (nGpr nVec : Nat) (gAlloc csIds vAlloc : List Nat) (gScr vScr : Option Nat)
  (cross loops : Trie Bool) (banks : Trie Bank)
  (bparams lTrie : Trie (List Nat))

/-- Gathered weights; `callW` records `(mult, vars live across a call at that weight)`. -/
structure GatherAcc where
  (weights defInterf gprPts vecPts callW : List (Nat × List Nat) := [])
  (abiGpr abiVec affEdges : List (Nat × Nat × Nat) := [])

def addWeight (mult : Nat) (uses : List Nat) (ws : List (Nat × List Nat)) :
    List (Nat × List Nat) :=
  if uses.isEmpty then ws else (mult, uses) :: ws

/-- Pressure point: at most `allocLen - need` of `vars` may sit in caller-saved registers.
Call-crossing variables count too, since splitting lets them use caller-saved registers. -/
def addPt (allocLen need : Nat) (vars : List Nat) (pts : List (Nat × List Nat)) :
    List (Nat × List Nat) :=
  let b := allocLen - need
  if Nat.ble 1 need && Nat.ble (b + 1) vars.length then
    match pts with
    | (b0, vs0) :: pts' =>
      if vars == vs0 then (if Nat.ble (b + 1) b0 then (b, vs0) :: pts' else pts)
      else (b, vars) :: pts
    | [] => [(b, vars)]
  else pts

def splitBank (banks : Trie Bank) (vs : List Nat) : List Nat × List Nat :=
  vs.foldl (fun (gs, vcs) x =>
    if (banks.getD x .gpr).isVec then (gs, x :: vcs) else (x :: gs, vcs)) ([], [])

mutual
def gather {I : Isa} (c : Ctx I) : Nat → Tree → GatherAcc → GatherAcc
  | mult, .let_ lv _ nv0 ts op k, acc =>
    let la := k.lv
    let defs := (List.range ts.length).map (nv0 + ·)
    let uses := opVarIds op
    let (aOpt, isCp) := firstOpVar op
    let aff := match aOpt, defs with
      | some a, d0 :: _ =>
        if isCp then (d0, a, 6 * mult) :: acc.affEdges
        else if !natMem a la then (d0, a, 5 * mult) :: acc.affEdges else acc.affEdges
      | _, _ => acc.affEdges
    let di := defs.foldl (fun d x =>
      if natMem x la || Nat.ble 2 defs.length then (x, union defs la) :: d else d) acc.defInterf
    let (gLv, vLv) := splitBank c.banks lv
    let (gUse, vUse) := splitBank c.banks uses
    let (gDef, vDef) := splitBank c.banks defs
    gather c mult k { acc with
      weights := (mult, defs ++ uses) :: acc.weights, defInterf := di, affEdges := aff,
      gprPts := addPt c.nGpr (max gUse.length gDef.length) gLv acc.gprPts,
      vecPts := addPt c.nVec (max vUse.length vDef.length) vLv acc.vecPts }
  | mult, .load lv _ x _ a k, acc =>
    let la := k.lv
    let di := if natMem x la then (x, la) :: acc.defInterf else acc.defInterf
    let (gLv, vLv) := splitBank c.banks lv
    gather c mult k { acc with
      weights := (mult, x :: argVarIds a) :: acc.weights, defInterf := di,
      gprPts := addPt c.nGpr 1 gLv acc.gprPts,
      vecPts := if (c.banks.getD x .gpr).isVec then addPt c.nVec 1 vLv acc.vecPts
        else acc.vecPts }
  | mult, .store lv _ _ v a k, acc =>
    let uses := dedup (argVarIds v ++ argVarIds a)
    let (gLv, vLv) := splitBank c.banks lv
    let (gUse, vUse) := splitBank c.banks uses
    gather c mult k { acc with
      weights := addWeight mult uses acc.weights,
      gprPts := addPt c.nGpr gUse.length gLv acc.gprPts,
      vecPts := addPt c.nVec vUse.length vLv acc.vecPts }
  | mult, .call _ _ nv0 _ as bs args k, acc =>
    let defs := (List.range bs.length).map (nv0 + ·)
    let la := k.lv
    let di := defs.foldl (fun d x =>
      if natMem x la then (x, union defs la) :: d else d) acc.defInterf
    let (ag1, av1) := match I.assignArgs as with
      | some locs =>
        addAbiArgs (tupArgsToList args) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    let (ag2, av2) := match I.assignRets bs with
      | some locs =>
        addAbiArgs (defs.map some) (abiIdList c.allGpr c.allVec locs) (4 * mult) ag1 av1
      | none => (ag1, av1)
    gather c mult k { acc with
      weights := addWeight mult (defs ++ tupVarIds args) acc.weights, defInterf := di,
      abiGpr := ag2, abiVec := av2, callW := addWeight mult (eraseMany defs la) acc.callW }
  | mult, .jnz lv _ cx _ t e, acc =>
    let (gLv, _) := splitBank c.banks lv
    let acc1 := gather c mult e { acc with
      weights := (mult, [cx]) :: acc.weights,
      gprPts := addPt c.nGpr 1 gLv acc.gprPts }
    gather c mult t acc1
  | mult, .skip _ _ k, acc => gather c mult k acc
  | mult, .jump _ _ j _ args, acc =>
    { acc with weights := addWeight mult (tupVarIds args) acc.weights,
               affEdges := addAffZip (tupArgsToList args) (c.bparams.getD j []) (8 * mult)
                 acc.affEdges }
  | mult, .ret _ _ rs vs, acc =>
    let (ag, av) := match I.assignRets rs with
      | some locs =>
        addAbiArgs (tupArgsToList vs) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (tupVarIds vs) acc.weights, abiGpr := ag, abiVec := av }
  | mult, .exit _ _ _ as args, acc =>
    let (ag, av) := match I.assignArgs as with
      | some locs =>
        addAbiArgs (tupArgsToList args) (abiIdList c.allGpr c.allVec locs) (4 * mult)
          acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (tupVarIds args) acc.weights, abiGpr := ag, abiVec := av }
  | _, .stop _, acc => acc
  | mult, .group _ bs k, acc => gatherB c mult bs (gather c mult k acc)

def gatherB {I : Isa} (c : Ctx I) : Nat → TreeBlocks → GatherAcc → GatherAcc
  | _, .nil, acc => acc
  | mult, .cons l ps b bs, acc =>
    let pvars := ps.map Prod.fst
    let le := b.lv
    let di := pvars.foldl (fun d p =>
      if natMem p le then (p, union pvars le) :: d else d) acc.defInterf
    let mB := if c.loops.getD l false then min (10 * mult) 10000 else mult
    gatherB c mult bs
      (gather c mB b { acc with weights := addWeight mB pvars acc.weights, defInterf := di })
end

def triePush {α : Type} (t : Trie (List α)) (k : Nat) (v : α) : Trie (List α) :=
  t.insert k (v :: t.getD k [])

def sumWeights (ws : List (Nat × List Nat)) : Trie Nat :=
  ws.foldl (fun t (w, vs) => vs.foldl (fun t x => t.insert x (t.getD x 0 + w)) t) .empty

def decPts (pids : List Nat) (pb : Trie Nat) : Trie Nat :=
  pids.foldl (fun pb p => pb.insert p (pb.getD p 0 - 1)) pb

/-- Coloring state: homes, used callee-saved ids, slot count, pressure budgets, and the backup
slot `(slot, width)` of every split (call-crossing, caller-saved-homed) variable. -/
structure ColorSt (C : Type) where
  hT : Trie (Home C)
  usedCs : List Nat := []
  nslots : Nat := 0
  gPb : Trie Nat := .empty
  vPb : Trie Nat := .empty
  bk : Trie (Nat × SlotWidth) := .empty

/-- Color one variable `x` of weight `wx` and call-crossing weight `cw`. A call-crossing GPR
variable reuses an already-saved callee-saved register if one is free; otherwise it is split into
a caller-saved register when splitting (a store and a reload per crossed call, `2 * cw`) costs at
most one fresh callee-saved save/restore (`cw ≤ 1`) and is strictly cheaper than a slot home (a
store at the definition, or at entry for a parameter, plus a load per use, `≈ wx`); otherwise it
is promoted to a fresh callee-saved register, and only then spilled. (Splitting variables that
cross several calls measured worse: each straight-line path re-stores them and every join
reloads them.) A call-crossing vector is split whenever that beats a slot home. -/
def colorOne {I : Isa} (c : Ctx I) (interf : Trie (List Nat)) (gVp vVp : Trie (List Nat))
    (abiGT abiVT affT : Trie (List (Nat × Nat))) (cwT : Trie Nat) (fnParams : List Nat)
    (s : ColorSt I.Cond) (wx x : Nat) : ColorSt I.Cond :=
  let xI := interf.getD x []
  let forbSlots := xI.foldl (fun ss y =>
    let ss := match s.hT.getD y .none with | .slot b w => (b, w.slots) :: ss | _ => ss
    match s.bk.find? y with | some (b, w) => (b, w.slots) :: ss | none => ss) []
  let isX := c.cross.getD x false
  let cw := cwT.getD x 0
  let splitOk := Nat.ble (2 * cw + 1) (wx + if natMem x fnParams then 1 else 0)
  let cheapSplit := isX && splitOk && Nat.ble cw 1
  let toSlot (w : SlotWidth) : ColorSt I.Cond :=
    let b := firstFreeSlotRange w.slots forbSlots
    { s with hT := s.hT.insert x (.slot b w), nslots := max s.nslots (b + w.slots) }
  let withBk (w : SlotWidth) (s1 : ColorSt I.Cond) : ColorSt I.Cond :=
    let b := firstFreeSlotRange w.slots forbSlots
    { s1 with bk := s1.bk.insert x (b, w), nslots := max s1.nslots (b + w.slots) }
  match c.banks.getD x .gpr with
  | .gpr =>
    let forb := xI.foldl (fun rs y => match s.hT.getD y .none with
      | .gpr r => if natMem r rs then rs else r :: rs | _ => rs) []
    let pids := gVp.getD x []
    let caller := if pids.all (fun p => Nat.ble 1 (s.gPb.getD p 0)) then
        c.gAlloc.filter (!natMem · forb) else []
    let csFree := s.usedCs.filter (!natMem · forb)
    let newCs := if Nat.ble 3 wx then
        c.csIds.filter (fun r => !natMem r s.usedCs && !natMem r forb) else []
    let prefs := (affT.getD x []).foldl (fun ps (y, w) =>
      match s.hT.getD y .none with | .gpr ry => (ry, w) :: ps | _ => ps) (abiGT.getD x [])
    let inReg (r : Nat) : ColorSt I.Cond :=
      let s1 := { s with hT := s.hT.insert x (.gpr r),
                         gPb := if Nat.ble (r + 1) c.nGpr then decPts pids s.gPb else s.gPb }
      if isX && Nat.ble (r + 1) c.nGpr then withBk .w64 s1 else s1
    let inNewCs (r : Nat) : ColorSt I.Cond :=
      { s with hT := s.hT.insert x (.gpr r), usedCs := s.usedCs ++ [r] }
    let orNewCs : ColorSt I.Cond :=
      match bestRegPref prefs newCs with
      | some r => inNewCs r
      | none => toSlot .w64
    if !isX then
      match bestRegPref prefs (caller ++ csFree) with
      | some r => inReg r
      | none => orNewCs
    else
      match bestRegPref prefs csFree with
      | some r => inReg r
      | none =>
        match (if cheapSplit then bestRegPref prefs caller else none) with
        | some r => inReg r
        | none => orNewCs
  | .vec w =>
    let forb := xI.foldl (fun rs y => match s.hT.getD y .none with
      | .vec v => if natMem v rs then rs else v :: rs | _ => rs) []
    let pids := vVp.getD x []
    let cands := if (!isX || splitOk) && pids.all (fun p => Nat.ble 1 (s.vPb.getD p 0)) then
        c.vAlloc.filter (!natMem · forb) else []
    let prefs := (affT.getD x []).foldl (fun ps (y, w) =>
      match s.hT.getD y .none with | .vec vy => (vy, w) :: ps | _ => ps) (abiVT.getD x [])
    match bestRegPref prefs cands with
    | some v =>
      let s1 := { s with hT := s.hT.insert x (.vec v),
                         vPb := if Nat.ble (v + 1) c.nVec then decPts pids s.vPb else s.vPb }
      if isX then withBk w s1 else s1
    | none => toSlot w

def colorVars {I : Isa} (c : Ctx I) (nv : Nat) (flagHome : Trie I.Cond) (acc : GatherAcc)
    (fnParams : List Nat) (fnAbi : List (Option (Sum Nat Nat))) : ColorSt I.Cond :=
  let (abiG, abiV) := addAbiArgs (fnParams.map some) fnAbi 4 acc.abiGpr acc.abiVec
  let wTrie := sumWeights acc.weights
  let cwT := sumWeights acc.callW
  let di0 := fnParams.foldl (fun d p => (p, fnParams) :: d) acc.defInterf
  let order := sortByWeight nv ((dedup (di0.map Prod.fst)).map fun x => (wTrie.getD x 0, x))
  let interf : Trie (List Nat) := di0.foldl (fun t (z, ys) =>
    let (zL, t) := ys.foldl (fun (zAcc, t) y =>
      if Nat.beq y z then (zAcc, t) else (y :: zAcc, triePush t y z)) (t.getD z [], t)
    t.insert z zL) .empty
  let mkPts (pts : List (Nat × List Nat)) : Trie Nat × Trie (List Nat) × Nat :=
    pts.foldl (fun (pb, vp, pid) (b, vs) =>
      (pb.insert pid b, vs.foldl (fun vp x => triePush vp x pid) vp, pid + 1)) (.empty, .empty, 0)
  let (gPb0, gVp, _) := mkPts acc.gprPts
  let (vPb0, vVp, _) := mkPts acc.vecPts
  let abiGT : Trie (List (Nat × Nat)) := abiG.foldl (fun t (u, r, w) => triePush t u (r, w)) .empty
  let abiVT : Trie (List (Nat × Nat)) := abiV.foldl (fun t (u, r, w) => triePush t u (r, w)) .empty
  let affT : Trie (List (Nat × Nat)) := acc.affEdges.foldl (fun t (u, v, w) =>
    if Nat.beq u v then t else triePush (triePush t u (v, w)) v (u, w)) .empty
  let initHome : Trie (Home I.Cond) := (List.range nv).foldl (fun h x =>
    match flagHome.find? x with | some cc => h.insert x (.flag cc) | none => h) .empty
  order.foldl (fun s (wx, x) =>
    match s.hT.find? x with
    | some (.flag _) => s
    | _ => colorOne c interf gVp vVp abiGT abiVT affT cwT fnParams s wx x)
    { hT := initHome, gPb := gPb0, vPb := vPb0 }

/-! ## Parallel Moves and Hint Emission -/

def emitParMovesAux {α β : Type} (mkMov : α → α → β) (toR : Nat → α) (scrOpt : Option Nat) :
    Nat → List (Nat × Nat) → List β → List β
  | 0, _, acc | _, [], acc => acc.reverse
  | fuel + 1, pend, acc =>
    match pend.find? fun (d, _) => pend.all fun (_, s) => !Nat.beq s d with
    | some (d, s) =>
      let pend' := pend.filter fun p => !(Nat.beq p.1 d && Nat.beq p.2 s)
      emitParMovesAux mkMov toR scrOpt fuel pend'
        (if Nat.beq d s then acc else mkMov (toR d) (toR s) :: acc)
    | none =>
      match pend, scrOpt with
      | (d, s) :: rest, some tmp =>
        if Nat.beq d s then emitParMovesAux mkMov toR scrOpt fuel rest acc
        else
          let rest' := rest.map fun (d', s') => (d', if Nat.beq s' d then tmp else s')
          emitParMovesAux mkMov toR scrOpt fuel ((d, s) :: rest') (mkMov (toR tmp) (toR d) :: acc)
      | pend, none => acc.reverseAux (pend.map fun (d, s) => mkMov (toR d) (toR s))
      | [], _ => acc.reverse

def emitParMoves {α β : Type} (mkMov : α → α → β) (toR : Nat → α) (scrOpt : Option Nat)
    (pend : List (Nat × Nat)) : List β :=
  let pend := pend.filter fun (d, s) => !Nat.beq d s
  emitParMovesAux mkMov toR scrOpt (2 * pend.length + 2) pend []

def gprHomes {C : Type} (home : Trie (Home C)) (xs : List Nat) : List Nat :=
  xs.filterMap fun x => match home.getD x .none with | .gpr r => some r | _ => none
def vecHomes {C : Type} (home : Trie (Home C)) (xs : List Nat) : List Nat :=
  xs.filterMap fun x => match home.getD x .none with | .vec v => some v | _ => none
def freshReg (cands busy : List Nat) : Option Nat := cands.find? (!natMem · busy)

structure EmitSt (I : Isa) where
  (dest : Trie I.Loc := .empty) (entry : Trie (Entry I.Reg I.VReg I.Cond) := .empty)
  (pre : Trie (PreStep I.Reg I.VReg I.Cond) := .empty) (usedCs : List Nat := [])

/-- Moves pending from the previous node: stores of slot-homed arrivals `(x, slot, reg)` and
register-to-register arrival moves `(x, home, arrival)`, per bank. -/
structure Pend where
  gSt : List (Nat × Nat × Nat) := []
  vSt : List (Nat × Nat × SlotWidth × Nat) := []
  gRg : List (Nat × Nat × Nat) := []
  vRg : List (Nat × Nat × Nat) := []

def recordPre {I : Isa} (ip : Nat) (clr : Bool) (mvs : List I.Move)
    (pre : Trie (PreStep I.Reg I.VReg I.Cond)) : Trie (PreStep I.Reg I.VReg I.Cond) :=
  if !clr && mvs.isEmpty then pre else pre.insert ip ⟨clr, mvs⟩

/-- Split-variable moves: backup stores (`save`) or reloads of `xs` between home and backup. -/
def splitMoves {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (bk : Trie (Nat × SlotWidth))
    (save : Bool) (xs : List Nat) : List I.Move :=
  xs.filterMap fun x => (bk.find? x).bind fun (b, w) =>
    match home.getD x .none with
    | .gpr r => let g := c.gReg.getD r I.frame.sp; some (if save then .st b g else .ld g b)
    | .vec v => (c.vReg.find? v).map fun vr => if save then .vst w b vr else .vld w vr b
    | _ => none

/-- `PreStep` moves: pending arrivals first, then `extra` (split saves / reloads, which may read
registers the arrivals just filled), then loads of slot-homed operands into free registers. -/
def buildPre {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (usedCs : List Nat)
    (ipLive ops : List Nat) (pd : Pend) (extra : List I.Move) : List I.Move :=
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let gStMvs : List I.Move := pd.gSt.map fun (_, s, r) => .st s (gOf r)
  let vStMvs : List I.Move := pd.vSt.filterMap fun (_, s, w, v) => (c.vReg.find? v).map (.vst w s)
  let gRegMvs : List I.Move := emitParMoves Move.mov gOf c.gScr (pd.gRg.map fun (_, d, s) => (d, s))
  let vW := pd.vRg.foldl (fun w (x, _, _) => maxSlotWidth w (c.banks.getD x .gpr).slotWidth) .w64
  let vRegMvs : List I.Move := match c.vReg.find? 0 with
    | none => []
    | some v0 =>
      emitParMoves (Move.vmov vW) (fun i => c.vReg.getD i v0) c.vScr
        (pd.vRg.map fun (_, d, s) => (d, s))
  let baseMvs := gStMvs ++ vStMvs ++ gRegMvs ++ vRegMvs ++ extra
  if !(ops.any fun x => match home.getD x .none with | .slot _ _ => true | _ => false) then baseMvs
  else
    let wG := pd.gRg.map fun (_, d, _) => d; let wV := pd.vRg.map fun (_, d, _) => d
    let inG := pd.gSt.filterMap fun (x, _, r) => if !natMem r wG then some (x, r) else none
    let inV := pd.vSt.filterMap fun (x, _, _, v) => if !natMem v wV then some (x, v) else none
    let initGB := gprHomes home ipLive ++
      inG.filterMap fun (x, r) => if natMem x ops then some r else none
    let initVB := vecHomes home ipLive ++
      inV.filterMap fun (x, v) => if natMem x ops then some v else none
    let (_, _, ldRev) := ops.foldl (fun (gb, vb, mvs) x => match home.getD x .none with
      | .slot s w =>
        if (c.banks.getD x .gpr).isVec then
          if inV.any (fun (y, _) => Nat.beq y x) then (gb, vb, mvs)
          else match (freshReg c.vAlloc vb).bind fun v => (c.vReg.find? v).map (v, ·) with
            | some (v, vr) => (gb, v :: vb, .vld w vr s :: mvs) | none => (gb, vb, mvs)
        else
          if inG.any (fun (y, _) => Nat.beq y x) then (gb, vb, mvs)
          else match freshReg (c.gAlloc ++ usedCs) gb with
            | some r => (r :: gb, vb, .ld (gOf r) s :: mvs) | none => (gb, vb, mvs)
      | _ => (gb, vb, mvs)) (initGB, initVB, [])
    baseMvs ++ ldRev.reverse

def allocDefs {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (usedCs : List Nat)
    (defs la : List Nat) (prefVar? : Option Nat) (dest : Trie I.Loc) :
    Trie I.Loc × List (Nat × Nat × Nat) × List (Nat × Nat × SlotWidth × Nat) :=
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let pickG (gb sibG : List Nat) (pref : Option Nat) :=
    pref.filter (!natMem · sibG) <|> freshReg (c.gAlloc ++ usedCs) gb <|>
      c.gAlloc.find? (!natMem · sibG) <|> c.gAlloc.head?
  let pickV (vb sibV : List Nat) (pref : Option Nat) :=
    pref.filter (!natMem · sibV) <|> freshReg c.vAlloc vb <|>
      c.vAlloc.find? (!natMem · sibV) <|> c.vAlloc.head?
  let initGb := gprHomes home (union defs la)
  let initVb := vecHomes home (union defs la)
  let initSibG := gprHomes home defs
  let initSibV := vecHomes home defs
  let (dest', _, _, _, _, gSt, vSt) := defs.foldl
    (fun (dT, gb, vb, sibG, sibV, gS, vS) x => match home.getD x .none with
      | .flag cc => (dT.insert x (.flag cc), gb, vb, sibG, sibV, gS, vS)
      | .gpr r => (dT.insert x (.gpr (gOf r)), r :: gb, vb, r :: sibG, sibV, gS, vS)
      | .vec v =>
        match c.vReg.find? v with
        | some vr => (dT.insert x (.vec vr), gb, v :: vb, sibG, v :: sibV, gS, vS)
        | none => (dT, gb, vb, sibG, sibV, gS, vS)
      | h =>
        let spill? := match h with | .slot s w => some (s, w) | _ => none
        if (c.banks.getD x .gpr).isVec then
          let pref :=
            if spill?.isSome then prefVar?.bind fun a => match home.getD a .none with
              | .vec va => if Nat.ble (va + 1) c.nVec && !natMem va vb then some va else none
              | _ => none
            else none
          match (pickV vb sibV pref).bind fun v => (c.vReg.find? v).map (v, ·) with
          | some (v, vr) =>
            let vS' := match spill? with | some (s, w) => (x, s, w, v) :: vS | none => vS
            (dT.insert x (.vec vr), gb, v :: vb, sibG, v :: sibV, gS, vS')
          | none => (dT, gb, vb, sibG, sibV, gS, vS)
        else
          let pref :=
            if spill?.isSome then prefVar?.bind fun a => match home.getD a .none with
              | .gpr ra => if Nat.ble (ra + 1) c.nGpr && !natMem ra gb then some ra else none
              | _ => none
            else none
          match pickG gb sibG pref with
          | some r =>
            let gS' := match spill? with | some (s, _) => (x, s, r) :: gS | none => gS
            (dT.insert x (.gpr (gOf r)), r :: gb, vb, r :: sibG, sibV, gS', vS)
          | none => (dT, gb, vb, sibG, sibV, gS, vS))
    (dest, initGb, initVb, initSibG, initSibV, [], [])
  (dest', gSt, vSt)

def pickPlocs {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (liveL ps usedCs : List Nat) :
    List I.Loc × List (Option (Sum Nat Nat)) × List Nat :=
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let (locsRev, idsRev, _, _, cs') := ps.foldl (fun (ls, ids, gb, vb, cs) p =>
    match home.getD p .none with
    | .flag cc => (.flag cc :: ls, none :: ids, gb, vb, cs)
    | .gpr r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
    | .vec v => match c.vReg.find? v with
      | some vr => (.vec vr :: ls, some (.inr v) :: ids, gb, v :: vb, cs)
      | none => (ls, none :: ids, gb, vb, cs)
    | _ =>
      if (c.banks.getD p .gpr).isVec then
        match (freshReg c.vAlloc vb <|> c.vAlloc.head?).bind fun v =>
            (c.vReg.find? v).map (v, ·) with
        | some (v, vr) => (.vec vr :: ls, some (.inr v) :: ids, gb, v :: vb, cs)
        | none => (ls, none :: ids, gb, vb, cs)
      else match freshReg (c.gAlloc ++ cs) gb with
        | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
        | none => match c.csIds.find? (fun r => !natMem r gb && !natMem r cs) with
          | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs ++ [r])
          | none => match c.gAlloc.head? with
            | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
            | none => (ls, none :: ids, gb, vb, cs))
    ([], [], gprHomes home liveL ++ gprHomes home ps,
      vecHomes home liveL ++ vecHomes home ps, usedCs)
  (locsRev.reverse, idsRev.reverse, cs')

def pendFromArrivals {C : Type} (home : Trie (Home C)) (ps : List Nat)
    (arr : List (Option (Sum Nat Nat))) : Pend :=
  (ps.zip arr).foldl (fun pd (x, ao) =>
    match ao, home.getD x .none with
    | some (.inl rA), .gpr rH =>
      if Nat.beq rH rA then pd else { pd with gRg := (x, rH, rA) :: pd.gRg }
    | some (.inl rA), .slot s _ => { pd with gSt := (x, s, rA) :: pd.gSt }
    | some (.inr vA), .vec vH =>
      if Nat.beq vH vA then pd else { pd with vRg := (x, vH, vA) :: pd.vRg }
    | some (.inr vA), .slot s w => { pd with vSt := (x, s, w, vA) :: pd.vSt }
    | _, _ => pd) {}

/-! Hint emission. Besides the pending arrival moves, each path threads the split variables
`ev` that currently live only in their backup slot (evicted by a call) and `sv` whose backup slot
holds their value (stored on this path). Both reset at block entries, where `Entry.live` puts
every variable in its home. -/
mutual
def emitAlloc {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (bk : Trie (Nat × SlotWidth))
    (clrAt : Trie Bool) : Tree → Pend → List Nat → List Nat → EmitSt I → EmitSt I
  | .let_ lv ip nv0 ts op k, pd, ev, sv, st =>
    let ops := opVarIds op
    let rl := ops.filter (natMem · ev)
    let mvs := buildPre c home st.usedCs lv ops pd (splitMoves c home bk false rl)
    let defs := (List.range ts.length).map (nv0 + ·)
    let (dest, gSt', vSt') := allocDefs c home st.usedCs defs k.lv (firstOpVar op).1 st.dest
    emitAlloc c home bk clrAt k { gSt := gSt', vSt := vSt' } (eraseMany rl ev) sv
      { st with dest := dest, pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .load lv ip x _ a k, pd, ev, sv, st =>
    let ops := argVarIds a
    let rl := ops.filter (natMem · ev)
    let mvs := buildPre c home st.usedCs lv ops pd (splitMoves c home bk false rl)
    let (dest, gSt', vSt') := allocDefs c home st.usedCs [x] k.lv none st.dest
    emitAlloc c home bk clrAt k { gSt := gSt', vSt := vSt' } (eraseMany rl ev) sv
      { st with dest := dest, pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .store lv ip _ v a k, pd, ev, sv, st =>
    let ops := dedup (argVarIds v ++ argVarIds a)
    let rl := ops.filter (natMem · ev)
    let mvs := buildPre c home st.usedCs lv ops pd (splitMoves c home bk false rl)
    emitAlloc c home bk clrAt k {} (eraseMany rl ev) sv
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .call lv ip nv0 _ _ bs _ k, pd, ev, sv, st =>
    let defs := (List.range bs.length).map (nv0 + ·)
    let la := (eraseMany defs k.lv).filter fun x => (bk.find? x).isSome
    let sav := la.filter fun x => !natMem x ev && !natMem x sv
    let mvs := buildPre c home st.usedCs lv [] pd (splitMoves c home bk true sav)
    let arr := match I.assignRets bs with
      | some locs => abiIdList c.allGpr c.allVec locs | none => []
    emitAlloc c home bk clrAt k (pendFromArrivals home defs arr) (union ev la) (union sv sav)
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .jnz lv ip cx _ t e, pd, ev, sv, st =>
    let rl := if natMem cx ev then [cx] else []
    let mvs := buildPre c home st.usedCs lv [cx] pd (splitMoves c home bk false rl)
    let ev' := eraseMany rl ev
    let st1 := emitAlloc c home bk clrAt e {} ev' sv
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
    emitAlloc c home bk clrAt t {} ev' sv st1
  | .skip lv ip k, pd, ev, sv, st =>
    let mvs := buildPre c home st.usedCs lv [] pd []
    emitAlloc c home bk clrAt k {} ev sv
      { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .jump lv ip _ _ _, pd, ev, _, st =>
    let mvs := buildPre c home st.usedCs lv [] pd
      (splitMoves c home bk false (lv.filter (natMem · ev)))
    { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .ret lv ip _ _, pd, _, _, st | .exit lv ip _ _ _, pd, _, _, st =>
    let mvs := buildPre c home st.usedCs lv [] pd []
    { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .stop _, _, _, _, st => st
  | .group _ bs k, pd, ev, sv, st =>
    emitAllocB c home bk clrAt bs (emitAlloc c home bk clrAt k pd ev sv st)

def emitAllocB {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (bk : Trie (Nat × SlotWidth))
    (clrAt : Trie Bool) : TreeBlocks → EmitSt I → EmitSt I
  | .nil, st => st
  | .cons l ps b bs, st =>
    let lv := c.lTrie.getD l []
    let pvars := ps.map Prod.fst
    let (plocs, pids, cs') := pickPlocs c home lv pvars st.usedCs
    let liveL : List (SymArg × I.Loc) := lv.filterMap fun x =>
      match home.getD x .none with
      | .gpr r => some (.var x, .gpr (c.gReg.getD r I.frame.sp))
      | .vec v => (c.vReg.find? v).map fun vr => (.var x, .vec vr)
      | .flag cc => some (.var x, .flag cc)
      | .slot s w => some (.var x, .slot s w)
      | .none => none
    let st1 := emitAlloc c home bk clrAt b (pendFromArrivals home pvars pids) [] []
      { st with entry := st.entry.insert l ⟨liveL, plocs⟩, usedCs := cs' }
    emitAllocB c home bk clrAt bs st1
end

/-- Compute untrusted `Hints` for `Rega.lowerFn` via per-bank priority graph coloring. -/
def hints (I : Isa) (f : Fn)
    (condCands : List I.Cond :=
      I.gpr.zeroFlags ++ I.gpr.zeroFlags.map I.gpr.negCond ++ I.gpr.cmpFlags) : I.Hints :=
  let nGpr := I.frame.allocatable.length
  let nCs := I.frame.calleeSaved.length
  let allGpr := I.frame.allocatable ++ I.frame.calleeSaved ++ I.frame.scratch ++
    I.frame.argRegs ++ I.frame.retRegs
  let nVec := I.vec.vecAllocatable.length
  let allVec := I.vec.vecAllocatable ++ I.vec.vecScratch ++ I.vec.vecArgRegs ++ I.vec.vecRetRegs
  let (t0, fnPs, nv, _, _, tys) := Tree.ofFn f
  let (t1, elideIps) := elideAddrTree I t0
  let bs0 := t1.blocks
  let lTrie := liveLabels bs0
  let (_, t) := fillLive lTrie t1
  let crossList := acrossCalls t
  let c : Ctx I := {
    allGpr := allGpr, allVec := allVec,
    gReg := (allGpr.foldl (fun (t, i) r => (t.insert i r, i + 1)) (.empty, 0)).1,
    vReg := (allVec.foldl (fun (t, i) v => (t.insert i v, i + 1)) (.empty, 0)).1,
    nGpr := nGpr, nVec := nVec, gAlloc := List.range nGpr,
    csIds := (List.range nCs).map (· + nGpr), vAlloc := List.range nVec,
    gScr := if I.frame.scratch.isEmpty then none else some (nGpr + nCs),
    vScr := if I.vec.vecScratch.isEmpty then none else some nVec,
    cross := crossList.foldl (fun a x => a.insert x true) .empty,
    loops := loopBlocks bs0,
    banks := (List.range nv).foldl (fun b x => b.insert x (bankOf I (tys.getD x i64))) .empty,
    bparams := bs0.foldl (fun a (l, ps, _) => a.insert l (ps.map Prod.fst)) .empty,
    lTrie := lTrie }
  let fh := match I.frame.allocatable.head? with
    | some r0 =>
      let r1 := I.frame.allocatable[1]?.getD r0
      let v0 := I.vec.vecAllocatable.head?
      let v1 := I.vec.vecAllocatable[1]? <|> v0
      gatherFlags I r0 r1 v0 v1 condCands nv (fnPs.map Prod.fst) c.cross c.bparams tys lTrie t
    | none => {}
  let acc := gather c 1 t {}
  let fnAbi := match I.assignArgs f.as with
    | some locs => abiIdList allGpr allVec locs | none => []
  let cs := colorVars c nv fh.flagHome acc (fnPs.map Prod.fst) fnAbi
  let st := emitAlloc c cs.hT cs.bk fh.clearAt t (pendFromArrivals cs.hT (fnPs.map Prod.fst) fnAbi)
    [] [] { usedCs := cs.usedCs }
  { dest := st.dest, entry := st.entry, pre := st.pre, variant := fh.variant, elide := elideIps,
    nslots := cs.nslots, saved := st.usedCs.map fun r => c.gReg.getD r I.frame.sp }

end Spill
end LeanQbe.T
