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

def mkDummyPArgs {I : Isa} (r0 : I.Reg) (v0 : Option I.VReg) (fArg : Nat → Option I.Cond) (immF : Option I.Cond) :
    {sig : List Ty} → Tup (Arg VNat) sig → Option (Tup (PArg I.Reg I.VReg I.Cond) sig)
  | [], () => some ()
  | .bool :: _, (.imm b, as) =>
    let pa := if !b then match immF with | some c => .flag c | none => .imm false else .imm true
    (mkDummyPArgs r0 v0 fArg immF as).map (pa, ·)
  | .bool :: _, (.var x, as) => (mkDummyPArgs r0 v0 fArg immF as).map (match fArg x with | some c => .flag c | none => .gpr r0, ·)
  | .bits _ :: _, (.var _, as) => (mkDummyPArgs r0 v0 fArg immF as).map (.gpr r0, ·)
  | .bits _ :: _, (.imm c, as) => (mkDummyPArgs r0 v0 fArg immF as).map (.imm c, ·)
  | .pair _ _ :: _, (.var _, as) => v0.bind fun v => (mkDummyPArgs r0 v0 fArg immF as).map (.vec v, ·)
  | .pair _ _ :: _, (.imm c, as) => (mkDummyPArgs r0 v0 fArg immF as).map (.imm c, ·)
  | .float _ :: _, _ => none

def mkDummyPDsts {I : Isa} (r0 : I.Reg) (v0 : Option I.VReg) (fDst : Nat → Option I.Cond) (nv0 : Nat) :
    (ts : List Ty) → Option (Tup (PDst I.Reg I.VReg I.Cond) ts)
  | [] => some ()
  | .bool :: ts => (mkDummyPDsts r0 v0 fDst (nv0 + 1) ts).map (match fDst nv0 with | some c => .flag c | none => .gpr r0, ·)
  | .bits _ :: ts => (mkDummyPDsts r0 v0 fDst (nv0 + 1) ts).map (.gpr r0, ·)
  | .pair _ _ :: ts => v0.bind fun v => (mkDummyPDsts r0 v0 fDst (nv0 + 1) ts).map (.vec v, ·)
  | .float _ :: _ => none

def probeOp (I : Isa) (r0 : I.Reg) (v0 : Option I.VReg) (fArg fDst : Nat → Option I.Cond) (immF : Option I.Cond)
    (nv0 : Nat) {ts : List Ty} (op : Op VNat ts) (vh : VariantHint) : Option FlagMask :=
  (mkDummyPArgs r0 v0 fArg immF op.args).bind fun pas => (mkDummyPDsts r0 v0 fDst nv0 ts).bind fun dsts =>
    if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
      ((I.gpr.op op.code pas dsts vh).map Prod.snd) <|> ((I.vec.vop op.code pas dsts vh).map Prod.snd)
    else (I.vec.vop op.code pas dsts vh).map Prod.snd

def altVariantsFor {ts : List Ty} (op : Op VNat ts) : List VariantHint :=
  let { sig := _, code, args } := op
  match code, args with
  | .umulw _, _ => [.mulxFast]
  | .add (.bits w), (.var _, .imm c, ()) =>
    let dec := if c == 1#w || c == -(1#w) then [.decInc] else []
    if Nat.beq w 64 then .disp ⟨⟨c.setWidth 64⟩⟩ :: dec else dec
  | .add (.bits w), (.imm c, .var _, ()) => if c == 1#w || c == -(1#w) then [.decInc] else []
  | .sub (.bits w), (.var _, .imm c, ()) =>
    let dec := if c == 1#w || c == -(1#w) then [.decInc] else []
    if Nat.beq w 64 then .disp (-⟨⟨c.setWidth 64⟩⟩) :: dec else dec
  | _, _ => []

structure FlagHints (Cond : Type) where
  (flagHome : Trie Cond := .empty) (variant : Trie VariantHint := .empty) (clearAt : Trie Bool := .empty)

structure ScanInfo where
  (badFlag isBParam hoistBlocked : Trie Bool := .empty) (defIp prevIp anchorOf : Trie Nat := .empty)
  (nodeAt : Trie Tree := .empty) (jumpEdges : List (Nat × Nat) := []) (immFalseJumps : List (Nat × Nat × Nat) := [])
  (liveIn liveAfter usesOf interf varLiveIps : Trie (List Nat) := .empty)

def trieAdd (t : Trie (List Nat)) (k v : Nat) : Trie (List Nat) :=
  let xs := t.getD k []; if natMem v xs then t else t.insert k (v :: xs)

def addInterfList (t : Trie (List Nat)) (x : Nat) (ys : List Nat) : Trie (List Nat) :=
  ys.foldl (fun a y => if Nat.beq x y then a else trieAdd (trieAdd a x y) y x) t

def carryVhs : {ts : List Ty} → Op VNat ts → List VariantHint
  | [.bits _, .bool], ⟨.addc _, _⟩ | [.bits _, .bool], ⟨.subb _, _⟩ => [.default, .adcx, .adox]
  | _, _ => [.default]

def canOpReadFlag (I : Isa) (r0 : I.Reg) (v0 : Option I.VReg) (conds : List I.Cond) (nv0 : Nat)
    {ts : List Ty} (op : Op VNat ts) (x : Nat) : Bool :=
  let fArg (c : I.Cond) (y : Nat) := if Nat.beq y x then some c else none
  let { sig := _, code, args := _ } := op
  conds.any fun c => (carryVhs op).any fun vh => (probeOp I r0 v0 (fArg c) (fun _ => none) none nv0 op vh).isSome ||
    match ts, code with
    | [.bits _, .bool], .addc _ | [.bits _, .bool], .subb _ =>
      (probeOp I r0 v0 (fArg c) (fun y => if Nat.beq y (nv0 + 1) then some c else none) none nv0 op vh).isSome
    | _, _ => false

mutual
def scanDefs (I : Isa) (r0 : I.Reg) (v0 : Option I.VReg) (conds : List I.Cond)
    (isBool : Nat → Bool) (bparams : Trie (List Nat)) : Tree → ScanInfo → ScanInfo
  | n@(.let_ _ ip nv0 ts op k), s =>
    let bf := (opVarIds op).foldl (fun b x => if isBool x && !canOpReadFlag I r0 v0 conds nv0 op x then b.insert x true else b) s.badFlag
    let { sig := _, code, args := _ } := op
    let (di, bf) := match ts, code with
      | [.bool], .cmp _ (.bits _) .bool _ => (s.defIp.insert nv0 ip, bf)
      | [.bits _, .bool], .addc _ | [.bits _, .bool], .subb _ => (s.defIp.insert (nv0 + 1) ip, bf)
      | _, _ => (s.defIp, ((List.range ts.length).map (nv0 + ·)).foldl (fun b d => if isBool d then b.insert d true else b) bf)
    scanDefs I r0 v0 conds isBool bparams k { s with nodeAt := s.nodeAt.insert ip n, defIp := di, badFlag := bf }
  | n@(.load _ ip x _ _ k), s =>
    scanDefs I r0 v0 conds isBool bparams k { s with nodeAt := s.nodeAt.insert ip n, badFlag := if isBool x then s.badFlag.insert x true else s.badFlag }
  | n@(.store _ ip t v _ k), s =>
    scanDefs I r0 v0 conds isBool bparams k { s with nodeAt := s.nodeAt.insert ip n, badFlag := if t == .bool then (argVarIds v).foldl (fun b x => b.insert x true) s.badFlag else s.badFlag }
  | n@(.call _ ip nv0 _ _ bs _ k), s =>
    let bf := ((List.range bs.length).map (nv0 + ·)).foldl (fun b d => if isBool d then b.insert d true else b) s.badFlag
    scanDefs I r0 v0 conds isBool bparams k { s with nodeAt := s.nodeAt.insert ip n, badFlag := bf }
  | n@(.jnz _ ip _ _ t e), s => scanDefs I r0 v0 conds isBool bparams t (scanDefs I r0 v0 conds isBool bparams e { s with nodeAt := s.nodeAt.insert ip n })
  | n@(.skip _ ip k), s => scanDefs I r0 v0 conds isBool bparams k { s with nodeAt := s.nodeAt.insert ip n }
  | n@(.jump _ ip j _ args), s =>
    let rec goArgs : {ts : List Ty} → Tup (Arg VNat) ts → List Nat → ScanInfo → ScanInfo
      | [], (), _, sc | _ :: _, _, [], sc => sc
      | .bool :: _, (.var v, as), p :: ps, sc => goArgs as ps { sc with jumpEdges := (p, v) :: sc.jumpEdges }
      | .bool :: _, (.imm false, as), p :: ps, sc => goArgs as ps { sc with immFalseJumps := (ip, j, p) :: sc.immFalseJumps }
      | .bool :: _, (.imm true, as), p :: ps, sc => goArgs as ps { sc with badFlag := sc.badFlag.insert p true }
      | _ :: _, (_, as), _ :: ps, sc => goArgs as ps sc
    goArgs args (bparams.getD j []) { s with nodeAt := s.nodeAt.insert ip n }
  | .group _ bs k, s => scanDefsB I r0 v0 conds isBool bparams bs (scanDefs I r0 v0 conds isBool bparams k s)
  | _, s => s
def scanDefsB (I : Isa) (r0 : I.Reg) (v0 : Option I.VReg) (conds : List I.Cond) (isBool : Nat → Bool) (bparams : Trie (List Nat)) : TreeBlocks → ScanInfo → ScanInfo
  | .nil, s => s
  | .cons _ ps b bs, s => scanDefsB I r0 v0 conds isBool bparams bs (scanDefs I r0 v0 conds isBool bparams b
      { s with isBParam := ps.foldl (fun t (p, ty) => if ty == .bool then t.insert p true else t) s.isBParam })
end

def markIfHoist (prevIp : Trie Nat) (hb : Trie Bool) (anc? : Option Nat) (ip : Nat) : Trie Bool :=
  let rec go : Nat → Nat → Trie Bool → Trie Bool
    | 0, _, t => t
    | f + 1, cur, t => if Nat.beq cur (anc?.getD ip) then t.insert cur true else match prevIp.find? cur with | some p => go f p (t.insert cur true) | none => t
  match anc? with
  | some a => if Nat.beq a ip then hb else (match prevIp.find? ip with | some p => go (ip + 1) p hb | none => hb)
  | none => hb

def stepScan (ip : Nat) (lvC afterC : List Nat) (prev? anc? : Option Nat) (s : ScanInfo) : ScanInfo :=
  { s with
    prevIp := match prev? with | some p => s.prevIp.insert ip p | none => s.prevIp,
    anchorOf := match anc? with | some a => s.anchorOf.insert ip a | none => s.anchorOf,
    liveIn := s.liveIn.insert ip lvC, liveAfter := s.liveAfter.insert ip afterC,
    interf := lvC.foldl (fun t x => addInterfList t x lvC) s.interf, varLiveIps := afterC.foldl (fun t x => trieAdd t x ip) s.varLiveIps }

mutual
def scanRanges (isCand : Nat → Bool) (lTrie : Trie (List Nat)) : Option Nat → Option Nat → Tree → ScanInfo → ScanInfo
  | prev?, anchor?, .let_ lv ip nv0 ts op k, s =>
    let lvC := lv.filter isCand; let anc? := if lvC.isEmpty then some ip else anchor?
    let defs := (List.range ts.length).map (nv0 + ·); let afterC := (k.lv.filter isCand).filter (!natMem · defs)
    let s1 := stepScan ip lvC afterC prev? anc? s
    let uses := (opVarIds op).foldl (fun u x => if isCand x then trieAdd u x ip else u) s1.usesOf
    let interf := match defs.find? (s1.defIp.find? · == some ip) with | some d => addInterfList s1.interf d afterC | none => s1.interf
    let { sig := _, code, args } := op
    let hasImmF := match code, args with | .addc _, (_, _, .imm false, ()) | .subb _, (_, _, .imm false, ()) => true | _, _ => false
    let hb := if hasImmF && defs.any (fun d => isCand d && s1.defIp.find? d == some ip) then markIfHoist s1.prevIp s1.hoistBlocked anc? ip else s1.hoistBlocked
    scanRanges isCand lTrie (some ip) anc? k { s1 with usesOf := uses, interf := interf, hoistBlocked := hb }
  | prev?, anchor?, .load lv ip _ _ _ k, s | prev?, anchor?, .store lv ip _ _ _ k, s =>
    let lvC := lv.filter isCand; let anc? := if lvC.isEmpty then some ip else anchor?
    scanRanges isCand lTrie (some ip) anc? k (stepScan ip lvC (k.lv.filter isCand) prev? anc? s)
  | prev?, _, .call lv ip _ _ _ _ _ k, s => scanRanges isCand lTrie (some ip) none k (stepScan ip (lv.filter isCand) [] prev? none s)
  | prev?, anchor?, .jnz lv ip cx _ t e, s =>
    let lvC := lv.filter isCand; let anc? := if lvC.isEmpty && !isCand cx then none else anchor?
    let s1 := stepScan ip lvC (union (t.lv.filter isCand) (e.lv.filter isCand)) prev? anc? s
    scanRanges isCand lTrie (some ip) anc? t (scanRanges isCand lTrie (some ip) anc? e
      { s1 with usesOf := if isCand cx then trieAdd s1.usesOf cx ip else s1.usesOf })
  | prev?, anchor?, .skip lv ip k, s =>
    let lvC := lv.filter isCand; let anc? := if lvC.isEmpty then some ip else anchor?
    scanRanges isCand lTrie (some ip) anc? k (stepScan ip lvC lvC prev? anc? s)
  | prev?, anchor?, .jump lv ip j _ _, s =>
    let lvC := lv.filter isCand; let anc? := if lvC.isEmpty then some ip else anchor?
    let s1 := stepScan ip lvC ((lTrie.getD j []).filter isCand) prev? anc? s
    { s1 with hoistBlocked := if s1.immFalseJumps.any (fun (ij, _, p) => Nat.beq ij ip && isCand p) then markIfHoist s1.prevIp s1.hoistBlocked anc? ip else s1.hoistBlocked }
  | prev?, _, .ret lv ip _ _, s | prev?, _, .exit lv ip _ _ _, s => stepScan ip (lv.filter isCand) [] prev? none s
  | prev?, anchor?, .group _ bs k, s => scanRangesB isCand lTrie bs (scanRanges isCand lTrie prev? anchor? k s)
  | _, _, .stop _, s => s
def scanRangesB (isCand : Nat → Bool) (lTrie : Trie (List Nat)) : TreeBlocks → ScanInfo → ScanInfo
  | .nil, s => s
  | .cons _ ps b bs, s =>
    let pC := (ps.map Prod.fst).filter isCand; let bC := b.lv.filter isCand
    scanRangesB isCand lTrie bs (scanRanges isCand lTrie none none b { s with interf := pC.foldl (fun t p => addInterfList (addInterfList t p bC) p pC) s.interf })
end

structure FlagState (Cond : Type) where
  (flagHome : Trie Cond := .empty) (variant : Trie VariantHint := .empty) (clearAt : Trie Bool := .empty) (lockedClob : Trie FlagMask := .empty)

def maskOf {I : Isa} (fh : Trie I.Cond) (xs : List Nat) : FlagMask :=
  xs.foldl (fun m x => match fh.find? x with | some c => m ||| I.gpr.condReads c | none => m) 0#8

def lockVh {C : Type} (ip : Nat) (vh : VariantHint) (cl : FlagMask) (st : FlagState C) : FlagState C :=
  { st with variant := if vh == .default then st.variant else st.variant.insert ip vh, lockedClob := st.lockedClob.insert ip cl }

def probeIntervening (I : Isa) (r0 : I.Reg) (v0 : Option I.VReg) (conds : List I.Cond) (isCand : Nat → Bool)
    (info : ScanInfo) (fArg : Nat → Option I.Cond) (reqMask : FlagMask) (ip : Nat) (st : FlagState I.Cond) : Option (FlagState I.Cond) :=
  match st.lockedClob.find? ip with
  | some cl => if FlagMask.disjoint reqMask cl then some st else none
  | none => match info.nodeAt.find? ip with
    | none => some st
    | some (.let_ _ _ nv0 ts op _) =>
      let { sig := _, code, args := _ } := op
      match ts, code with
      | [.bool], .cmp _ (.bits _) .bool _ =>
        (probeOp I r0 v0 fArg st.flagHome.find? none nv0 op .default).bind fun cl =>
          if FlagMask.disjoint reqMask cl then some st else if !isCand nv0 then none else
            conds.findSome? fun c => (probeOp I r0 v0 fArg (fun x => if Nat.beq x nv0 then some c else none) none nv0 op .decInc).bind fun cl' =>
              let usesOk := (info.usesOf.getD nv0 []).all fun u => match info.nodeAt.find? u with
                | some (.let_ _ _ nu _ opU _) => (carryVhs opU).any fun vhU =>
                    (probeOp I r0 v0 (fun y => if Nat.beq y nv0 then some c else fArg y) (fun _ => none) none nu opU vhU).isSome
                | _ => true
              if FlagMask.disjoint reqMask cl' && usesOk then some { lockVh ip .decInc cl' st with flagHome := st.flagHome.insert nv0 c } else none
      | [.bits _, .bool], .addc _ | [.bits _, .bool], .subb _ =>
        let cOut := nv0 + 1
        if (st.flagHome.find? cOut).isSome then none else match probeOp I r0 v0 fArg (fun _ => none) none nv0 op .default with
          | some cl => if FlagMask.disjoint reqMask cl then some st else none
          | none => if isCand cOut && [VariantHint.adcx, .adox].any (fun vh => conds.any fun c =>
              match probeOp I r0 v0 fArg (fun x => if Nat.beq x cOut then some c else none) (if I.gpr.zeroFlags.contains c then some c else none) nv0 op vh with
              | some cl => FlagMask.disjoint reqMask cl | none => false) then some st else none
      | _, _ => (VariantHint.default :: altVariantsFor op).findSome? fun vh =>
          (probeOp I r0 v0 fArg st.flagHome.find? none nv0 op vh).bind fun cl => if FlagMask.disjoint reqMask cl then some (lockVh ip vh cl st) else none
    | some (.load _ _ _ t _ _) => match I.gpr.load t r0 (.baseDisp r0 0) <|> v0.bind (I.vec.vload t · (.baseDisp r0 0)) with
      | some (_, cl) => if FlagMask.disjoint reqMask cl then some st else none | none => none
    | some (.store _ _ t _ _ _) => match I.gpr.store t (.gpr r0) (.baseDisp r0 0) <|> v0.bind (I.vec.vstore t · (.baseDisp r0 0)) with
      | some (_, cl) => if FlagMask.disjoint reqMask cl then some st else none | none => none
    | some (.jnz _ _ cx _ _ _) => if (fArg cx).isSome || FlagMask.disjoint reqMask (I.gpr.jnzGpr r0 "").2 then some st else none
    | some (.call ..) => none | _ => some st

def placeOrHoistClear (I : Isa) (r0 : I.Reg) (v0 : Option I.VReg) (conds : List I.Cond) (isCand : Nat → Bool)
    (info : ScanInfo) (cc : I.Cond) (ip : Nat) (extraLive : List Nat) (st : FlagState I.Cond) : Option (FlagState I.Cond) :=
  if !I.gpr.zeroFlags.contains cc then none else
    let noLive (xs : List Nat) := xs.all fun y => !natMem y extraLive && (st.flagHome.find? y).isNone
    let safeHere := match info.nodeAt.find? ip with | some (.let_ ..) => noLive (info.liveIn.getD ip []) | _ => noLive (info.liveIn.getD ip []) && noLive (info.liveAfter.getD ip [])
    if safeHere then some { st with clearAt := st.clearAt.insert ip true } else
      (info.anchorOf.find? ip).bind fun a => if Nat.beq a ip || !noLive (info.liveIn.getD a []) then none else
        let rec collectPath : Nat → Nat → List Nat → Option (List Nat)
          | 0, _, _ => none | f + 1, cur, acc => if Nat.beq cur a then some (a :: acc) else (info.prevIp.find? cur).bind fun p => collectPath f p (cur :: acc)
        (info.prevIp.find? ip).bind fun p => (collectPath (ip + 1) p []).bind fun path =>
          (path.foldl (fun acc? ip' => acc?.bind fun stAcc =>
            let req := I.gpr.condReads cc ||| maskOf stAcc.flagHome (info.liveAfter.getD ip' [])
            probeIntervening I r0 v0 conds isCand info (fun x => if natMem x extraLive then some cc else stAcc.flagHome.find? x) req ip' stAcc) (some st)).map
              fun st1 => { st1 with clearAt := st1.clearAt.insert a true }

def tryColorWeb (I : Isa) (r0 : I.Reg) (v0 : Option I.VReg) (conds : List I.Cond) (isCand : Nat → Bool)
    (info : ScanInfo) (vars : List Nat) (st : FlagState I.Cond) : Option (FlagState I.Cond) :=
  let liveIps := (vars.foldl (fun acc v => (info.varLiveIps.getD v []).foldl (fun a ip => if natMem ip a then a else ip :: a) acc) []).mergeSort (· ≤ ·)
  conds.findSome? fun cc =>
    let fArg (x : Nat) := if natMem x vars then some cc else st.flagHome.find? x
    if !(vars.all fun v => (info.interf.getD v []).all fun y => natMem y vars ||
      match st.flagHome.find? y with | some cy => FlagMask.disjoint (I.gpr.condReads cc) (I.gpr.condReads cy) | none => true) then none else
    let st1? := vars.foldl (fun acc? v => acc?.bind fun stAcc => match info.defIp.find? v with
      | none => some stAcc
      | some ip => (info.nodeAt.find? ip).bind fun node => match node with
        | .let_ _ _ nv0 ts op _ =>
          let liveOther := (info.liveAfter.getD ip []).filter (!natMem · vars); let cm := maskOf stAcc.flagHome liveOther
          let hasOther := !liveOther.isEmpty || info.hoistBlocked.getD ip false; let locked := (stAcc.lockedClob.find? ip).isSome
          let { sig := _, code, args } := op
          match ts, code, args with
          | [.bool], .cmp _ (.bits _) .bool _, _ =>
            (if locked then [stAcc.variant.getD ip .default] else if hasOther then [.decInc, .default] else [.default, .decInc]).findSome? fun vh =>
              (probeOp I r0 v0 fArg (fun x => if Nat.beq x nv0 then some cc else none) none nv0 op vh).bind fun cl =>
                if FlagMask.disjoint cm cl then some (lockVh ip vh cl stAcc) else none
          | [.bits _, .bool], .addc _, (_, _, cin, _) | [.bits _, .bool], .subb _, (_, _, cin, _) =>
            let vhs := if locked then [stAcc.variant.getD ip .default] else if hasOther then [.adcx, .adox, .default] else [.default, .adcx, .adox]
            let tryVh (immF : Option I.Cond) (vh : VariantHint) :=
              (probeOp I r0 v0 fArg (fun x => if Nat.beq x (nv0 + 1) then some cc else none) immF nv0 op vh).bind fun cl => if FlagMask.disjoint cm cl then some cl else none
            let clr? := match cin with | .imm false => vhs.findSome? fun vh => (tryVh (if I.gpr.zeroFlags.contains cc then some cc else none) vh).bind fun cl =>
              (placeOrHoistClear I r0 v0 conds isCand info cc ip vars stAcc).map (lockVh ip vh cl ·) | _ => none
            clr? <|> vhs.findSome? fun vh => (tryVh none vh).map (lockVh ip vh · stAcc)
          | _, _, _ => none
        | _ => none) (some st)
    let st2? := st1?.bind fun st1 => vars.foldl (fun acc? v => acc?.bind fun stAcc =>
      (info.usesOf.getD v []).foldl (fun ac? ip_u => ac?.bind fun stU => match info.nodeAt.find? ip_u with
        | some (.let_ _ _ nv0 ts op _) => let { sig := _, code, args := _ } := op; match ts, code with
          | [.bits _, .bool], .addc _ | [.bits _, .bool], .subb _ =>
            let cOut := nv0 + 1
            if natMem cOut vars then some stU else
              let vhs := if (stU.lockedClob.find? ip_u).isSome then [stU.variant.getD ip_u .default] else [.default, .adcx, .adox]
              let fDst := match stU.flagHome.find? cOut with | some co => (fun x => if Nat.beq x cOut then some co else none) | none => (fun _ => none)
              if vhs.any (fun vh => (probeOp I r0 v0 fArg fDst none nv0 op vh).isSome ||
                  (isCand cOut && conds.any (fun co => (probeOp I r0 v0 fArg (fun x => if Nat.beq x cOut then some co else none) none nv0 op vh).isSome)))
              then some stU else none
          | _, _ => if (probeOp I r0 v0 fArg stU.flagHome.find? none nv0 op (stU.variant.getD ip_u .default)).isSome then some stU else none
        | _ => some stU) (some stAcc)) (some st1)
    let st3? := st2?.bind fun st2 => liveIps.foldl (fun acc? ip' => acc?.bind fun stAcc =>
      if stAcc.clearAt.getD ip' false then none else
        let req := I.gpr.condReads cc ||| maskOf stAcc.flagHome ((info.liveAfter.getD ip' []).filter (!natMem · vars))
        probeIntervening I r0 v0 conds isCand info (fun x => if natMem x vars then some cc else stAcc.flagHome.find? x) req ip' stAcc) (some st2)
    let st4? := st3?.bind fun st3 => info.immFalseJumps.foldl (fun acc? (ipJ, _, p) => acc?.bind fun stAcc =>
      if natMem p vars then placeOrHoistClear I r0 v0 conds isCand info cc ipJ vars stAcc else some stAcc) (some st3)
    st4?.map fun st4 => { st4 with flagHome := vars.foldl (fun fh v => fh.insert v cc) st4.flagHome }

def ufFind (rep : Trie Nat) (x : Nat) : Nat :=
  let rec go : Nat → Nat → Nat | 0, c => c | f + 1, c => match rep.find? c with | some p => if Nat.beq p c then c else go f p | none => c
  go 64 x

def gatherFlags (I : Isa) (r0 : I.Reg) (v0 : Option I.VReg) (conds : List I.Cond) (nv : Nat)
    (fnParams : List Nat) (cross : Trie Bool) (bparams : Trie (List Nat)) (tys : Trie Ty) (lTrie : Trie (List Nat)) (t : Tree) : FlagHints I.Cond :=
  let isBool (x : Nat) : Bool := match tys.getD x i64 with | .bool => true | _ => false
  if !(List.range nv).any isBool then {} else
    let s0 := scanDefs I r0 v0 conds isBool bparams t {}
    let bf0 := (List.range nv).foldl (fun bf x => if isBool x && cross.getD x false then bf.insert x true else bf)
      (fnParams.foldl (fun bf x => if isBool x then bf.insert x true else bf) s0.badFlag)
    let bf := (List.range (s0.jumpEdges.length + 1)).foldl (fun bf _ =>
      s0.jumpEdges.foldl (fun bf (p, v) => if bf.getD v false then bf.insert p true else bf) bf) bf0
    let isCand (x : Nat) : Bool := isBool x && !bf.getD x false
    let info := scanRanges isCand lTrie none none t { s0 with badFlag := bf }
    let rep := info.jumpEdges.foldl (fun rep (p, v) =>
      if isCand p && isCand v then let rp := ufFind rep p; let rv := ufFind rep v
        if Nat.beq rp rv then rep else rep.insert rp rv else rep) (.empty : Trie Nat)
    let cands := (List.range nv).filter isCand
    let groups := cands.foldl (fun (g : Trie (List Nat)) x => let r := ufFind rep x; g.insert r (g.getD r [] ++ [x])) .empty
    let (bpWebs, locWebs) := (dedup (cands.map (ufFind rep))).foldl (fun (bps, locs) r =>
      let vs := groups.getD r []
      if vs.any (info.isBParam.getD · false) then (vs :: bps, locs) else (bps, (info.defIp.getD (vs.headD 0) 0, vs) :: locs)) ([], [])
    let st1 := bpWebs.foldl (fun st vs =>
      if vs.any (fun v => (st.flagHome.find? v).isSome) then st else
        match tryColorWeb I r0 v0 conds isCand info vs st with
        | some st' => st'
        | none => (vs.filter (!info.isBParam.getD · false)).foldl (fun stAcc v => (tryColorWeb I r0 v0 conds isCand info [v] stAcc).getD stAcc) st) {}
    let st2 := ((locWebs.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd).foldl (fun st vs =>
      if vs.any (fun v => (st.flagHome.find? v).isSome) then st else (tryColorWeb I r0 v0 conds isCand info vs st).getD st) st1
    { flagHome := st2.flagHome, variant := st2.variant, clearAt := st2.clearAt }

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
    emitAlloc c home clrAt k gSt' vSt' [] [] { st with dest := dest, pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .store lv ip _ v a k, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv (dedup (argVarIds v ++ argVarIds a)) gSt vSt gRg vRg
    emitAlloc c home clrAt k [] [] [] [] { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .call lv ip nv0 _ _ bs _ k, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv [] gSt vSt gRg vRg
    let defs := (List.range bs.length).map (nv0 + ·)
    let arr := match I.assignRets bs with | some locs => abiIdList c.allGpr c.allVec locs | none => []
    let (gSt', vSt', gRg', vRg') := pendFromArrivals home defs arr
    emitAlloc c home clrAt k gSt' vSt' gRg' vRg' { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .jnz lv ip cx _ t e, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv [cx] gSt vSt gRg vRg
    let st1 := emitAlloc c home clrAt e [] [] [] [] { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
    emitAlloc c home clrAt t [] [] [] [] st1
  | .skip lv ip k, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv [] gSt vSt gRg vRg
    emitAlloc c home clrAt k [] [] [] [] { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
  | .jump lv ip _ _ _, gSt, vSt, gRg, vRg, st | .ret lv ip _ _, gSt, vSt, gRg, vRg, st
  | .exit lv ip _ _ _, gSt, vSt, gRg, vRg, st =>
    let mvs := buildPre c home st.usedCs lv [] gSt vSt gRg vRg
    { st with pre := recordPre ip (clrAt.getD ip false) mvs st.pre }
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
  let fh := match I.frame.allocatable.head? with
    | some r0 => gatherFlags I r0 I.vec.vecAllocatable.head? condCands nv (fnPs.map Prod.fst) c.cross c.bparams tys lTrie t | none => {}
  let acc := gather c 1 t {}; let fnAbi := match I.assignArgs f.as with | some locs => abiIdList allGpr allVec locs | none => []
  let (home, usedCs, nslots) := colorVars c nv fh.flagHome acc (fnPs.map Prod.fst) fnAbi
  let (gSt0, vSt0, gRg0, vRg0) := pendFromArrivals home (fnPs.map Prod.fst) fnAbi
  let st := emitAlloc c home fh.clearAt t gSt0 vSt0 gRg0 vRg0 { usedCs := usedCs }
  { dest := st.dest, entry := st.entry, pre := st.pre, variant := fh.variant, nslots := nslots, saved := st.usedCs.map fun r => c.gReg.getD r I.frame.sp }

end Spill
end LeanQbe.T
