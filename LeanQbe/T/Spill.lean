module

public import LeanQbe.T.Live

/-!
# Priority Graph-Coloring Register Allocator & Spilling Oracle (`T7a`, `L-E1.2`, untrusted)

Full port of E1's priority graph-coloring allocator extended to typed banks (`GPR` + `Vec` + local
flag hints): cross-call spilling, `calleeSaved` promotion, `abiPref`, `affEdges`, `ptBudget`,
`10 * mult` loop depth weights, destructive `allocDef`, unified multi-granule spill slots, and
GPR/Vec parallel-move cycle breaking via `scratch`/`vecScratch`.

Untrusted: `Rega.lowerFn` checks every hint, so any heuristic bug can only fail lowering.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Spill

open Live Rega

inductive Home (Cond : Type) where
  | none | gpr (r : Nat) | vec (v : Nat) | flag (c : Cond) | slot (s : Nat) (w : SlotWidth)
  deriving Inhabited

/-! ## Sorting, Intervals, and Preferences -/

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
    let score (r : Nat) : Nat := xPrefs.foldl (fun s (r', w) => if Nat.beq r r' then s + w else s) 0
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

def dummyPArgs {I : Isa} (r0 : I.Reg) (v0 : Option I.VReg) (c0 : Option I.Cond) :
    {sig : List Ty} → Tup (Arg VNat) sig → Option (Tup (PArg I.Reg I.VReg I.Cond) sig)
  | [], () => some ()
  | .bool :: _, (.imm b, as) =>
    (dummyPArgs r0 v0 c0 as).map (match c0 with | some c => .flag c | none => .imm b, ·)
  | .bool :: _, (.var _, as) =>
    (dummyPArgs r0 v0 c0 as).map (match c0 with | some c => .flag c | none => .gpr r0, ·)
  | .bits _ :: _, (.var _, as) => (dummyPArgs r0 v0 c0 as).map (.gpr r0, ·)
  | .bits _ :: _, (.imm c, as) => (dummyPArgs r0 v0 c0 as).map (.imm c, ·)
  | .pair _ _ :: _, (.var _, as) => match v0 with | some v => (dummyPArgs r0 v0 c0 as).map (.vec v, ·) | none => none
  | .pair _ _ :: _, (.imm c, as) => (dummyPArgs r0 v0 c0 as).map (.imm c, ·)
  | .float _ :: _, _ => none

def probeCmpFlag (I : Isa) (r0 : I.Reg) (conds : List I.Cond) {ts : List Ty} (op : Op VNat ts) : Option I.Cond :=
  let { sig := _, code, args } := op
  match ts, code, args with
  | [.bool], .cmp cmp t .bool h, args =>
    match dummyPArgs r0 I.vec.vecAllocatable.head? none args with
    | none => none
    | some pas => conds.find? fun c => (I.gpr.op (.cmp cmp t .bool h) pas (.flag c, ()) .default).isSome
  | _, _, _ => none

def probeCarryFlag (I : Isa) (r0 : I.Reg) (conds : List I.Cond) {ts : List Ty} (op : Op VNat ts)
    (cinFlag : Option I.Cond) : Option (I.Cond × VariantHint × Bool) :=
  let { sig := _, code, args } := op
  let go (w : Nat) (code : OpCode [Ty.bits w, Ty.bits w, .bool] [Ty.bits w, .bool])
      (args : Tup (Arg VNat) [Ty.bits w, Ty.bits w, .bool]) (vhs : List VariantHint) :=
    let cin := args.2.2.1
    vhs.findSome? fun vh => conds.findSome? fun c =>
      let needClr := match cin with | .imm false => I.gpr.zeroFlags.contains c | _ => false
      let cIn := match cin with | .var _ => cinFlag | .imm false => if needClr then some c else none | _ => none
      match dummyPArgs r0 I.vec.vecAllocatable.head? cIn args with
      | some pas => if (I.gpr.op code pas (.gpr r0, .flag c, ()) vh).isSome then some (c, vh, needClr) else none
      | none => none
  match ts, code, args with
  | [.bits w, .bool], .addc _, args => go w (.addc w) args [.default, .adcx, .adox]
  | [.bits w, .bool], .subb _, args => go w (.subb w) args [.default]
  | _, _, _ => none

structure FlagHints (Cond : Type) where
  flagHome : Trie Cond := .empty
  variant : Trie VariantHint := .empty
  clearAt : Trie Bool := .empty

mutual
def gatherFlags (I : Isa) (r0 : I.Reg) (conds : List I.Cond) : Tree → FlagHints I.Cond → FlagHints I.Cond
  | .let_ _ ip nv0 ts op k, fh =>
    let { sig := _, code, args } := op
    let fh1 := match ts, code, k with
      | [.bool], .cmp _ _ .bool _, .jnz _ _ c _ t e =>
        if Nat.beq c nv0 && !natMem nv0 t.lv && !natMem nv0 e.lv then
          match probeCmpFlag I r0 conds op with
          | some cc => { fh with flagHome := fh.flagHome.insert nv0 cc }
          | none => fh
        else fh
      | [.bits _, .bool], .addc _, _ | [.bits _, .bool], .subb _, _ =>
        let cOut := nv0 + 1
        let cinFlag := match code, args with
          | .addc _, (_, _, .var cv, ()) | .subb _, (_, _, .var cv, ()) => fh.flagHome.find? cv
          | _, _ => none
        let localOnly := match k with
          | .let_ _ _ _ _ op2 k2 =>
            let { sig := _, code := code2, args := _ } := op2
            natMem cOut (opVarIds op2) && !natMem cOut k2.lv &&
            match code2 with | .addc _ | .subb _ | .select _ => true | _ => false
          | _ => false
        if localOnly then
          match probeCarryFlag I r0 conds op cinFlag with
          | some (cc, vh, clr) =>
            { flagHome := fh.flagHome.insert cOut cc
              variant := if vh == VariantHint.default then fh.variant else fh.variant.insert ip vh
              clearAt := if clr then fh.clearAt.insert ip true else fh.clearAt }
          | none => fh
        else fh
      | _, _, _ => fh
    gatherFlags I r0 conds k fh1
  | .load _ _ _ _ _ k, fh | .store _ _ _ _ _ k, fh | .call _ _ _ _ _ _ _ k, fh | .skip _ _ k, fh =>
    gatherFlags I r0 conds k fh
  | .jnz _ _ _ _ t e, fh => gatherFlags I r0 conds t (gatherFlags I r0 conds e fh)
  | .group _ bs k, fh => gatherFlagsB I r0 conds bs (gatherFlags I r0 conds k fh)
  | .jump .., fh | .ret .., fh | .exit .., fh | .stop _, fh => fh

def gatherFlagsB (I : Isa) (r0 : I.Reg) (conds : List I.Cond) : TreeBlocks → FlagHints I.Cond → FlagHints I.Cond
  | .nil, fh => fh
  | .cons _ _ b bs, fh => gatherFlagsB I r0 conds bs (gatherFlags I r0 conds b fh)
end

/-! ## Interference, Weights, Pressure Points, and Priority Coloring -/

structure Ctx (I : Isa) where
  (allGpr : List I.Reg) (allVec : List I.VReg) (gReg : Trie I.Reg) (vReg : Trie I.VReg)
  (nGpr nVec : Nat) (gAlloc csIds vAlloc : List Nat) (gScr vScr : Option Nat)
  (hasCalls : Bool) (cross loops : Trie Bool) (banks : Trie Bank)
  (bparams lTrie : Trie (List Nat))

structure GatherAcc where
  (weights defInterf gprPts vecPts : List (Nat × List Nat) := [])
  (abiGpr abiVec affEdges : List (Nat × Nat × Nat) := [])

def addWeight (mult : Nat) (uses : List Nat) (ws : List (Nat × List Nat)) : List (Nat × List Nat) :=
  if uses.isEmpty then ws else (mult, uses) :: ws

def addPt (allocLen : Nat) (hasCalls : Bool) (cross : Trie Bool) (need : Nat) (vars : List Nat)
    (pts : List (Nat × List Nat)) : List (Nat × List Nat) :=
  let b := allocLen - need
  if Nat.ble 1 need && Nat.ble (b + 1) vars.length then
    let cVars := if hasCalls then vars.filter (!cross.getD · false) else vars
    if Nat.ble (b + 1) cVars.length then
      match pts with
      | (b0, vs0) :: pts' =>
        if cVars == vs0 then (if Nat.ble (b + 1) b0 then (b, vs0) :: pts' else pts) else (b, cVars) :: pts
      | [] => [(b, cVars)]
    else pts
  else pts

def splitBank (banks : Trie Bank) (vs : List Nat) : List Nat × List Nat :=
  vs.foldl (fun (gs, vcs) x => if (banks.getD x .gpr).isVec then (gs, x :: vcs) else (x :: gs, vcs)) ([], [])

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
    let di := defs.foldl (fun d x => if natMem x la || Nat.ble 2 defs.length then (x, union defs la) :: d else d) acc.defInterf
    let (gLv, vLv) := splitBank c.banks lv
    let (gUse, vUse) := splitBank c.banks uses
    let (gDef, vDef) := splitBank c.banks defs
    gather c mult k { acc with
      weights := (mult, defs ++ uses) :: acc.weights, defInterf := di, affEdges := aff,
      gprPts := addPt c.nGpr c.hasCalls c.cross (max gUse.length gDef.length) gLv acc.gprPts,
      vecPts := addPt c.nVec c.hasCalls c.cross (max vUse.length vDef.length) vLv acc.vecPts }
  | mult, .load lv _ x _ a k, acc =>
    let la := k.lv
    let di := if natMem x la then (x, la) :: acc.defInterf else acc.defInterf
    let (gLv, vLv) := splitBank c.banks lv
    gather c mult k { acc with
      weights := (mult, x :: argVarIds a) :: acc.weights, defInterf := di,
      gprPts := addPt c.nGpr c.hasCalls c.cross 1 gLv acc.gprPts,
      vecPts := if (c.banks.getD x .gpr).isVec then addPt c.nVec c.hasCalls c.cross 1 vLv acc.vecPts else acc.vecPts }
  | mult, .store lv _ _ v a k, acc =>
    let uses := dedup (argVarIds v ++ argVarIds a)
    let (gLv, vLv) := splitBank c.banks lv
    let (gUse, vUse) := splitBank c.banks uses
    gather c mult k { acc with
      weights := addWeight mult uses acc.weights,
      gprPts := addPt c.nGpr c.hasCalls c.cross gUse.length gLv acc.gprPts,
      vecPts := addPt c.nVec c.hasCalls c.cross vUse.length vLv acc.vecPts }
  | mult, .call _ _ nv0 _ as bs args k, acc =>
    let defs := (List.range bs.length).map (nv0 + ·)
    let la := k.lv
    let di := defs.foldl (fun d x => if natMem x la then (x, union defs la) :: d else d) acc.defInterf
    let (ag1, av1) := match I.assignArgs as with
      | some locs => addAbiArgs (tupArgsToList args) (abiIdList c.allGpr c.allVec locs) (4 * mult) acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    let (ag2, av2) := match I.assignRets bs with
      | some locs => addAbiArgs (defs.map some) (abiIdList c.allGpr c.allVec locs) (4 * mult) ag1 av1
      | none => (ag1, av1)
    gather c mult k { acc with
      weights := addWeight mult (defs ++ tupVarIds args) acc.weights, defInterf := di, abiGpr := ag2, abiVec := av2 }
  | mult, .jnz lv _ cx _ t e, acc =>
    let (gLv, _) := splitBank c.banks lv
    let acc1 := gather c mult e { acc with
      weights := (mult, [cx]) :: acc.weights,
      gprPts := addPt c.nGpr c.hasCalls c.cross 1 gLv acc.gprPts }
    gather c mult t acc1
  | mult, .skip _ _ k, acc => gather c mult k acc
  | mult, .jump _ _ j _ args, acc =>
    { acc with weights := addWeight mult (tupVarIds args) acc.weights,
               affEdges := addAffZip (tupArgsToList args) (c.bparams.getD j []) (8 * mult) acc.affEdges }
  | mult, .ret _ _ rs vs, acc =>
    let (ag, av) := match I.assignRets rs with
      | some locs => addAbiArgs (tupArgsToList vs) (abiIdList c.allGpr c.allVec locs) (4 * mult) acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (tupVarIds vs) acc.weights, abiGpr := ag, abiVec := av }
  | mult, .exit _ _ _ as args, acc =>
    let (ag, av) := match I.assignArgs as with
      | some locs => addAbiArgs (tupArgsToList args) (abiIdList c.allGpr c.allVec locs) (4 * mult) acc.abiGpr acc.abiVec
      | none => (acc.abiGpr, acc.abiVec)
    { acc with weights := addWeight mult (tupVarIds args) acc.weights, abiGpr := ag, abiVec := av }
  | _, .stop _, acc => acc
  | mult, .group _ bs k, acc => gatherB c mult bs (gather c mult k acc)

def gatherB {I : Isa} (c : Ctx I) : Nat → TreeBlocks → GatherAcc → GatherAcc
  | _, .nil, acc => acc
  | mult, .cons l ps b bs, acc =>
    let pvars := ps.map Prod.fst
    let le := b.lv
    let di := pvars.foldl (fun d p => if natMem p le then (p, union pvars le) :: d else d) acc.defInterf
    let mB := if c.loops.getD l false then min (10 * mult) 10000 else mult
    gatherB c mult bs (gather c mB b { acc with weights := addWeight mB pvars acc.weights, defInterf := di })
end

def triePush {α : Type} (t : Trie (List α)) (k : Nat) (v : α) : Trie (List α) := t.insert k (v :: t.getD k [])

def colorVars {I : Isa} (c : Ctx I) (nv : Nat) (flagHome : Trie I.Cond) (acc : GatherAcc)
    (fnParams : List Nat) (fnAbi : List (Option (Sum Nat Nat))) : Trie (Home I.Cond) × List Nat × Nat :=
  let (abiG, abiV) := addAbiArgs (fnParams.map some) fnAbi 4 acc.abiGpr acc.abiVec
  let wTrie : Trie Nat := acc.weights.foldl (fun t (w, vs) => vs.foldl (fun t x => t.insert x (t.getD x 0 + w)) t) .empty
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
  let (home, usedCs, nslots, _, _) := order.foldl (fun (hT, usedCs, nslots, gPb, vPb) (wx, x) =>
    match hT.find? x with
    | some (.flag _) => (hT, usedCs, nslots, gPb, vPb)
    | _ =>
      let xI := interf.getD x []
      let forbSlots := xI.foldl (fun ss y => match hT.getD y .none with | .slot s w => (s, w.slots) :: ss | _ => ss) []
      match c.banks.getD x .gpr with
      | .gpr =>
        let forb := xI.foldl (fun rs y => match hT.getD y .none with
          | .gpr r => if natMem r rs then rs else r :: rs | _ => rs) []
        let pids := gVp.getD x []
        let cCands := if !c.cross.getD x false && pids.all (fun p => Nat.ble 1 (gPb.getD p 0)) then
            c.gAlloc.filter (!natMem · forb) else []
        let prefs := (affT.getD x []).foldl (fun ps (y, w) =>
          match hT.getD y .none with | .gpr ry => (ry, w) :: ps | _ => ps) (abiGT.getD x [])
        match bestRegPref prefs (cCands ++ usedCs.filter (!natMem · forb)) with
        | some r =>
          let gPb' := if Nat.ble (r + 1) c.nGpr then pids.foldl (fun pb p => pb.insert p (pb.getD p 0 - 1)) gPb else gPb
          (hT.insert x (.gpr r), usedCs, nslots, gPb', vPb)
        | none =>
          let newCs := if Nat.ble 3 wx then c.csIds.filter (fun r => !natMem r usedCs && !natMem r forb) else []
          match bestRegPref prefs newCs with
          | some r => (hT.insert x (.gpr r), usedCs ++ [r], nslots, gPb, vPb)
          | none => let s := firstFreeSlotRange 1 forbSlots; (hT.insert x (.slot s .w64), usedCs, max nslots (s + 1), gPb, vPb)
      | .vec w =>
        let forb := xI.foldl (fun rs y => match hT.getD y .none with
          | .vec v => if natMem v rs then rs else v :: rs | _ => rs) []
        let pids := vVp.getD x []
        let cCands := if !c.cross.getD x false && pids.all (fun p => Nat.ble 1 (vPb.getD p 0)) then
            c.vAlloc.filter (!natMem · forb) else []
        let prefs := (affT.getD x []).foldl (fun ps (y, w) =>
          match hT.getD y .none with | .vec vy => (vy, w) :: ps | _ => ps) (abiVT.getD x [])
        match bestRegPref prefs cCands with
        | some v =>
          let vPb' := if Nat.ble (v + 1) c.nVec then pids.foldl (fun pb p => pb.insert p (pb.getD p 0 - 1)) vPb else vPb
          (hT.insert x (.vec v), usedCs, nslots, gPb, vPb')
        | none => let s := firstFreeSlotRange w.slots forbSlots; (hT.insert x (.slot s w), usedCs, max nslots (s + w.slots), gPb, vPb))
    (initHome, [], 0, gPb0, vPb0)
  (home, usedCs, nslots)

/-! ## Parallel Moves and Hint Emission -/

def emitParMovesAux {α β : Type} (mkMov : α → α → β) (toR : Nat → α) (scrOpt : Option Nat) :
    Nat → List (Nat × Nat) → List β → List β
  | 0, _, acc | _, [], acc => acc.reverse
  | fuel + 1, pend, acc =>
    match pend.find? fun (d, _) => pend.all fun (_, s) => !Nat.beq s d with
    | some (d, s) =>
      let pend' := pend.filter fun p => !(Nat.beq p.1 d && Nat.beq p.2 s)
      emitParMovesAux mkMov toR scrOpt fuel pend' (if Nat.beq d s then acc else mkMov (toR d) (toR s) :: acc)
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

def recordPre {I : Isa} (ip : Nat) (clr : Bool) (mvs : List I.Move)
    (pre : Trie (PreStep I.Reg I.VReg I.Cond)) : Trie (PreStep I.Reg I.VReg I.Cond) :=
  if !clr && mvs.isEmpty then pre else pre.insert ip ⟨clr, mvs⟩

def buildPre {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (usedCs : List Nat)
    (ipLive ops : List Nat) (pGSt : List (Nat × Nat × Nat)) (pVSt : List (Nat × Nat × SlotWidth × Nat))
    (pGReg pVReg : List (Nat × Nat × Nat)) : List I.Move :=
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let gStMvs : List I.Move := pGSt.map fun (_, s, r) => .st s (gOf r)
  let vStMvs : List I.Move := pVSt.filterMap fun (_, s, w, v) => (c.vReg.find? v).map (.vst w s)
  let gRegMvs : List I.Move := emitParMoves Move.mov gOf c.gScr (pGReg.map fun (_, d, s) => (d, s))
  let vW := pVReg.foldl (fun w (x, _, _) => maxSlotWidth w (c.banks.getD x .gpr).slotWidth) .w64
  let vRegMvs : List I.Move := match c.vReg.find? 0 with
    | none => []
    | some v0 => emitParMoves (Move.vmov vW) (fun i => c.vReg.getD i v0) c.vScr (pVReg.map fun (_, d, s) => (d, s))
  let baseMvs := gStMvs ++ vStMvs ++ gRegMvs ++ vRegMvs
  if !(ops.any fun x => match home.getD x .none with | .slot _ _ => true | _ => false) then baseMvs
  else
    let wG := pGReg.map fun (_, d, _) => d; let wV := pVReg.map fun (_, d, _) => d
    let inG := pGSt.filterMap fun (x, _, r) => if !natMem r wG then some (x, r) else none
    let inV := pVSt.filterMap fun (x, _, _, v) => if !natMem v wV then some (x, v) else none
    let initGB := gprHomes home ipLive ++ inG.filterMap fun (x, r) => if natMem x ops then some r else none
    let initVB := vecHomes home ipLive ++ inV.filterMap fun (x, v) => if natMem x ops then some v else none
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
  let pickG (gb : List Nat) (pref : Option Nat) := pref <|> freshReg (c.gAlloc ++ usedCs) gb <|> c.gAlloc.head?
  let pickV (vb : List Nat) (pref : Option Nat) := pref <|> freshReg c.vAlloc vb <|> c.vAlloc.head?
  let (dest', _, _, gSt, vSt) := defs.foldl (fun (dT, gb, vb, gS, vS) x => match home.getD x .none with
    | .flag cc => (dT.insert x (.flag cc), gb, vb, gS, vS)
    | .gpr r => (dT.insert x (.gpr (gOf r)), r :: gb, vb, gS, vS)
    | .vec v => match c.vReg.find? v with | some vr => (dT.insert x (.vec vr), gb, v :: vb, gS, vS) | none => (dT, gb, vb, gS, vS)
    | h =>
      let spill? := match h with | .slot s w => some (s, w) | _ => none
      if (c.banks.getD x .gpr).isVec then
        let pref := if spill?.isSome then prefVar?.bind fun a => match home.getD a .none with
          | .vec va => if Nat.ble (va + 1) c.nVec && !natMem va vb then some va else none | _ => none else none
        match (pickV vb pref).bind fun v => (c.vReg.find? v).map (v, ·) with
        | some (v, vr) =>
          let vS' := match spill? with | some (s, w) => (x, s, w, v) :: vS | none => vS
          (dT.insert x (.vec vr), gb, v :: vb, gS, vS')
        | none => (dT, gb, vb, gS, vS)
      else
        let pref := if spill?.isSome then prefVar?.bind fun a => match home.getD a .none with
          | .gpr ra => if Nat.ble (ra + 1) c.nGpr && !natMem ra gb then some ra else none | _ => none else none
        match pickG gb pref with
        | some r =>
          let gS' := match spill? with | some (s, _) => (x, s, r) :: gS | none => gS
          (dT.insert x (.gpr (gOf r)), r :: gb, vb, gS', vS)
        | none => (dT, gb, vb, gS, vS))
    (dest, gprHomes home (eraseMany defs la), vecHomes home (eraseMany defs la), [], [])
  (dest', gSt, vSt)

def pickPlocs {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (liveL ps usedCs : List Nat) :
    List I.Loc × List (Option (Sum Nat Nat)) × List Nat :=
  let gOf (r : Nat) := c.gReg.getD r I.frame.sp
  let (locsRev, idsRev, _, _, cs') := ps.foldl (fun (ls, ids, gb, vb, cs) p => match home.getD p .none with
    | .flag cc => (.flag cc :: ls, none :: ids, gb, vb, cs)
    | .gpr r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
    | .vec v => match c.vReg.find? v with
      | some vr => (.vec vr :: ls, some (.inr v) :: ids, gb, v :: vb, cs) | none => (ls, none :: ids, gb, vb, cs)
    | _ =>
      if (c.banks.getD p .gpr).isVec then
        match (freshReg c.vAlloc vb <|> c.vAlloc.head?).bind fun v => (c.vReg.find? v).map (v, ·) with
        | some (v, vr) => (.vec vr :: ls, some (.inr v) :: ids, gb, v :: vb, cs) | none => (ls, none :: ids, gb, vb, cs)
      else match freshReg (c.gAlloc ++ cs) gb with
        | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
        | none => match c.csIds.find? (fun r => !natMem r gb && !natMem r cs) with
          | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs ++ [r])
          | none => match c.gAlloc.head? with
            | some r => (.gpr (gOf r) :: ls, some (.inl r) :: ids, r :: gb, vb, cs)
            | none => (ls, none :: ids, gb, vb, cs))
    ([], [], gprHomes home liveL ++ gprHomes home ps, vecHomes home liveL ++ vecHomes home ps, usedCs)
  (locsRev.reverse, idsRev.reverse, cs')

def pendFromArrivals {C : Type} (home : Trie (Home C)) (ps : List Nat) (arr : List (Option (Sum Nat Nat))) :
    List (Nat × Nat × Nat) × List (Nat × Nat × SlotWidth × Nat) × List (Nat × Nat × Nat) × List (Nat × Nat × Nat) :=
  (ps.zip arr).foldl (fun (gSt, vSt, gRg, vRg) (x, ao) =>
    match ao, home.getD x .none with
    | some (.inl rA), .gpr rH => if Nat.beq rH rA then (gSt, vSt, gRg, vRg) else (gSt, vSt, (x, rH, rA) :: gRg, vRg)
    | some (.inl rA), .slot s _ => ((x, s, rA) :: gSt, vSt, gRg, vRg)
    | some (.inr vA), .vec vH => if Nat.beq vH vA then (gSt, vSt, gRg, vRg) else (gSt, vSt, gRg, (x, vH, vA) :: vRg)
    | some (.inr vA), .slot s w => (gSt, (x, s, w, vA) :: vSt, gRg, vRg)
    | _, _ => (gSt, vSt, gRg, vRg)) ([], [], [], [])

mutual
def emitAlloc {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (clrAt : Trie Bool) :
    Tree → List (Nat × Nat × Nat) → List (Nat × Nat × SlotWidth × Nat) →
    List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → EmitSt I → EmitSt I
  | .let_ lv ip nv0 ts op k, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv (opVarIds op) gSt vSt gRg vRg
    let defs := (List.range ts.length).map (nv0 + ·)
    let (dest, gSt', vSt') := allocDefs c home st.usedCs defs k.lv (firstOpVar op).1 st.dest
    emitAlloc c home clrAt k gSt' vSt' [] [] { st with dest := dest, pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .load lv ip x _ a k, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv (argVarIds a) gSt vSt gRg vRg
    let (dest, gSt', vSt') := allocDefs c home st.usedCs [x] k.lv none st.dest
    emitAlloc c home clrAt k gSt' vSt' [] [] { st with dest := dest, pre := recordPre ip false mvs st.pre }
  | .store lv ip _ v a k, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv (dedup (argVarIds v ++ argVarIds a)) gSt vSt gRg vRg
    emitAlloc c home clrAt k [] [] [] [] { st with pre := recordPre ip false mvs st.pre }
  | .call lv ip nv0 _ _ bs _ k, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv [] gSt vSt gRg vRg
    let defs := (List.range bs.length).map (nv0 + ·)
    let arr := match I.assignRets bs with | some locs => abiIdList c.allGpr c.allVec locs | none => []
    let (gSt', vSt', gRg', vRg') := pendFromArrivals home defs arr
    emitAlloc c home clrAt k gSt' vSt' gRg' vRg' { st with pre := recordPre ip false mvs st.pre }
  | .jnz lv ip cx _ t e, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv [cx] gSt vSt gRg vRg
    let st1 := emitAlloc c home clrAt e [] [] [] [] { st with pre := recordPre ip false mvs st.pre }
    emitAlloc c home clrAt t [] [] [] [] st1
  | .skip lv ip k, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv [] gSt vSt gRg vRg
    emitAlloc c home clrAt k [] [] [] [] { st with pre := recordPre ip false mvs st.pre }
  | .jump lv ip _ _ _, gSt, vSt, gRg, vRg, st | .ret lv ip _ _, gSt, vSt, gRg, vRg, st
  | .exit lv ip _ _ _, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv [] gSt vSt gRg vRg
    { st with pre := recordPre ip false mvs st.pre }
  | .stop _, _, _, _, _, st => st
  | .group _ bs k, gSt, vSt, gRg, vRg, st =>
    emitAllocB c home clrAt bs (emitAlloc c home clrAt k gSt vSt gRg vRg st)

def emitAllocB {I : Isa} (c : Ctx I) (home : Trie (Home I.Cond)) (clrAt : Trie Bool) :
    TreeBlocks → EmitSt I → EmitSt I
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
    let (gSt, vSt, gRg, vRg) := pendFromArrivals home pvars pids
    let st1 := emitAlloc c home clrAt b gSt vSt gRg vRg
      { st with entry := st.entry.insert l ⟨liveL, plocs⟩, usedCs := cs' }
    emitAllocB c home clrAt bs st1
end

/-- Compute untrusted `Hints` for `Rega.lowerFn` via per-bank priority graph coloring. -/
def hints (I : Isa) (f : Fn)
    (condCands : List I.Cond := I.gpr.zeroFlags ++ I.gpr.zeroFlags.map I.gpr.negCond) : I.Hints :=
  let nGpr := I.frame.allocatable.length
  let nCs := I.frame.calleeSaved.length
  let allGpr := I.frame.allocatable ++ I.frame.calleeSaved ++ I.frame.scratch ++ I.frame.argRegs ++ I.frame.retRegs
  let nVec := I.vec.vecAllocatable.length
  let allVec := I.vec.vecAllocatable ++ I.vec.vecScratch ++ I.vec.vecArgRegs ++ I.vec.vecRetRegs
  let (t0, fnPs, nv, _, _, tys) := Tree.ofFn f
  let bs0 := t0.blocks
  let lTrie := liveLabels bs0
  let (_, t) := fillLive lTrie t0
  let crossList := acrossCalls t
  let c : Ctx I := {
    allGpr := allGpr, allVec := allVec,
    gReg := (allGpr.foldl (fun (t, i) r => (t.insert i r, i + 1)) (.empty, 0)).1,
    vReg := (allVec.foldl (fun (t, i) v => (t.insert i v, i + 1)) (.empty, 0)).1,
    nGpr := nGpr, nVec := nVec, gAlloc := List.range nGpr, csIds := (List.range nCs).map (· + nGpr),
    vAlloc := List.range nVec,
    gScr := if I.frame.scratch.isEmpty then none else some (nGpr + nCs),
    vScr := if I.vec.vecScratch.isEmpty then none else some nVec,
    hasCalls := !crossList.isEmpty,
    cross := crossList.foldl (fun a x => a.insert x true) .empty,
    loops := loopBlocks bs0,
    banks := (List.range nv).foldl (fun b x => b.insert x (bankOf I (tys.getD x i64))) .empty,
    bparams := bs0.foldl (fun a (l, ps, _) => a.insert l (ps.map Prod.fst)) .empty,
    lTrie := lTrie }
  let fh := match I.frame.allocatable.head? with | some r0 => gatherFlags I r0 condCands t {} | none => {}
  let acc := gather c 1 t {}
  let fnAbi := match I.assignArgs f.as with | some locs => abiIdList allGpr allVec locs | none => []
  let (home, usedCs, nslots) := colorVars c nv fh.flagHome acc (fnPs.map Prod.fst) fnAbi
  let (gSt0, vSt0, gRg0, vRg0) := pendFromArrivals home (fnPs.map Prod.fst) fnAbi
  let st := emitAlloc c home fh.clearAt t gSt0 vSt0 gRg0 vRg0 { usedCs := usedCs }
  { dest := st.dest, entry := st.entry, pre := st.pre, variant := fh.variant,
    nslots := nslots, saved := st.usedCs.map fun r => c.gReg.getD r I.frame.sp }

end Spill
end LeanQbe.T
