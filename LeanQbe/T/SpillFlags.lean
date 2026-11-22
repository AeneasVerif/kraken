module

public import LeanQbe.T.Live
public import Std.Data.HashSet

/-!
# Local Flag-Web Coloring & Variant Probing (`T7a`, `L3`, `L7`, untrusted)

Split from `LeanQbe.T.Spill`: scans `Live.Tree` definitions and candidate live ranges, probes
target opcodes for flag-producing / flag-consuming variants (`decInc`, `adcx`, `adox`, `.disp`),
colors flag webs across `I.Cond` without interference, and inserts / hoists `clearFlags` for
immediate-false carry/borrow inputs.

Untrusted: `Rega.lowerFn` verifies every hint.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace SpillFlags

open Live Rega

def mkDummyPArgs {I : Isa} (r0 : I.Reg) (v0 : Option I.VReg) (fArg : Nat → Option I.Cond)
    (immF : Option I.Cond) :
    {sig : List Ty} → Tup (Arg VNat) sig → Option (Tup (PArg I.Reg I.VReg I.Cond) sig)
  | [], () => some ()
  | .bool :: _, (.imm b, as) =>
    let pa :=
      if !b then match immF with | some c => .flag c | none => .imm false else .imm true
    (mkDummyPArgs r0 v0 fArg immF as).map (pa, ·)
  | .bool :: _, (.var x, as) =>
    (mkDummyPArgs r0 v0 fArg immF as).map
      (match fArg x with | some c => .flag c | none => .gpr r0, ·)
  | .bits _ :: _, (.var _, as) => (mkDummyPArgs r0 v0 fArg immF as).map (.gpr r0, ·)
  | .bits _ :: _, (.imm c, as) => (mkDummyPArgs r0 v0 fArg immF as).map (.imm c, ·)
  | .pair _ _ :: _, (.var _, as) =>
    v0.bind fun v => (mkDummyPArgs r0 v0 fArg immF as).map (.vec v, ·)
  | .pair _ _ :: _, (.imm c, as) => (mkDummyPArgs r0 v0 fArg immF as).map (.imm c, ·)
  | .float _ :: _, _ => none

def mkDummyPDsts {I : Isa} (r0 r1 : I.Reg) (v0 v1 : Option I.VReg)
    (fDst : Nat → Option I.Cond) (nv0 : Nat) :
    (ts : List Ty) → Option (Tup (PDst I.Reg I.VReg I.Cond) ts)
  | [] => some ()
  | .bool :: ts =>
    (mkDummyPDsts r0 r1 v0 v1 fDst (nv0 + 1) ts).map
      (match fDst nv0 with | some c => .flag c | none => .gpr r0, ·)
  | .bits _ :: ts => (mkDummyPDsts r1 r0 v0 v1 fDst (nv0 + 1) ts).map (.gpr r0, ·)
  | .pair _ _ :: ts => v0.bind fun v =>
    (mkDummyPDsts r0 r1 v1 v0 fDst (nv0 + 1) ts).map (.vec v, ·)
  | .float _ :: _ => none

def probeOpLen (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (fArg fDst : Nat → Option I.Cond)
    (immF : Option I.Cond) (nv0 : Nat) {ts : List Ty} (op : Op VNat ts)
    (vh : VariantHint) : Option (FlagMask × Nat) :=
  (mkDummyPArgs r0 v0 fArg immF op.args).bind fun pas =>
    (mkDummyPDsts r0 r1 v0 v1 fDst nv0 ts).bind fun dsts =>
      if (tupDstVecs dsts).isEmpty && (tupArgVecs pas).isEmpty then
        ((I.gpr.op op.code pas dsts vh).map fun (ds, m) => (m, ds.length)) <|>
          ((I.vec.vop op.code pas dsts vh).map fun (ds, m) => (m, ds.length))
      else (I.vec.vop op.code pas dsts vh).map fun (ds, m) => (m, ds.length)

def probeOp (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (fArg fDst : Nat → Option I.Cond)
    (immF : Option I.Cond) (nv0 : Nat) {ts : List Ty} (op : Op VNat ts)
    (vh : VariantHint) : Option FlagMask :=
  (probeOpLen I r0 r1 v0 v1 fArg fDst immF nv0 op vh).map Prod.fst

def altVariantsFor {ts : List Ty} (op : Op VNat ts) : List VariantHint :=
  let { sig := _, code, args } := op
  match code, args with
  | .umulw _, _ => [.mulxFast]
  | .add (.bits w), (.var _, .imm c, ()) =>
    let dec := if c == 1#w || c == -(1#w) then [.decInc] else []
    if Nat.beq w 64 || Nat.beq w 32 then .disp (Int64.ofBitVec (c.signExtend 64)) :: dec else dec
  | .add (.bits w), (.imm c, .var _, ()) =>
    let dec := if c == 1#w || c == -(1#w) then [.decInc] else []
    if Nat.beq w 64 || Nat.beq w 32 then .disp (Int64.ofBitVec (c.signExtend 64)) :: dec else dec
  | .sub (.bits w), (.var _, .imm c, ()) =>
    let dec := if c == 1#w || c == -(1#w) then [.decInc] else []
    if Nat.beq w 64 || Nat.beq w 32 then .disp (Int64.ofBitVec (-(c.signExtend 64))) :: dec
    else dec
  | _, _ => []

structure FlagHints (Cond : Type) where
  flagHome : Trie Cond := .empty
  variant : Trie VariantHint := .empty
  clearAt : Trie Bool := .empty

structure ScanInfo where
  badFlag : Trie Bool := .empty
  isBParam : Trie Bool := .empty
  hoistBlocked : Trie Bool := .empty
  defIp : Trie Nat := .empty
  prevIp : Trie Nat := .empty
  anchorOf : Trie Nat := .empty
  nodeAt : Trie Tree := .empty
  jumpEdges : List (Nat × Nat) := []
  immFalseJumps : List (Nat × Nat × Nat) := []
  liveIn : Trie (List Nat) := .empty
  liveAfter : Trie (List Nat) := .empty
  usesOf : Trie (List Nat) := .empty
  interf : Trie (List Nat) := .empty
  varLiveIps : Trie (List Nat) := .empty

def trieAdd (t : Trie (List Nat)) (k v : Nat) : Trie (List Nat) :=
  let xs := t.getD k []
  if natMem v xs then t else t.insert k (v :: xs)

def addInterfList (t : Trie (List Nat)) (x : Nat) (ys : List Nat) : Trie (List Nat) :=
  ys.foldl (fun a y => if Nat.beq x y then a else trieAdd (trieAdd a x y) y x) t

def carryVhs : {ts : List Ty} → Op VNat ts → List VariantHint
  | [.bits _, .bool], ⟨.addc _, _⟩ | [.bits _, .bool], ⟨.subb _, _⟩ => [.default, .adcx, .adox]
  | _, _ => [.default]

def canOpReadFlag (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (conds : List I.Cond)
    (nv0 : Nat) {ts : List Ty} (op : Op VNat ts) (x : Nat) : Bool :=
  let fArg (c : I.Cond) (y : Nat) := if Nat.beq y x then some c else none
  let { sig := _, code, args := _ } := op
  conds.any fun c =>
    (carryVhs op).any fun vh =>
      (probeOp I r0 r1 v0 v1 (fArg c) (fun _ => none) none nv0 op vh).isSome ||
        match ts, code with
        | [.bits _, .bool], .addc _ | [.bits _, .bool], .subb _ =>
          let fDst y := if Nat.beq y (nv0 + 1) then some c else none
          (probeOp I r0 r1 v0 v1 (fArg c) fDst none nv0 op vh).isSome
        | _, _ => false

mutual
def scanDefs (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (conds : List I.Cond)
    (isBool : Nat → Bool) (bparams : Trie (List Nat)) : Tree → ScanInfo → ScanInfo
  | n@(.let_ _ ip nv0 ts op k), s =>
    let bf := (opVarIds op).foldl (fun b x =>
      if isBool x && !canOpReadFlag I r0 r1 v0 v1 conds nv0 op x then b.insert x true else b)
      s.badFlag
    let { sig := _, code, args := _ } := op
    let (di, bf) := match ts, code with
      | [.bool], .cmp _ (.bits _) .bool _ => (s.defIp.insert nv0 ip, bf)
      | [.bits _, .bool], .addc _ | [.bits _, .bool], .subb _ => (s.defIp.insert (nv0 + 1) ip, bf)
      | _, _ =>
        let bf' := ((List.range ts.length).map (nv0 + ·)).foldl
          (fun b d => if isBool d then b.insert d true else b) bf
        (s.defIp, bf')
    scanDefs I r0 r1 v0 v1 conds isBool bparams k
      { s with nodeAt := s.nodeAt.insert ip n, defIp := di, badFlag := bf }
  | n@(.load _ ip x _ _ k), s =>
    let bf := if isBool x then s.badFlag.insert x true else s.badFlag
    scanDefs I r0 r1 v0 v1 conds isBool bparams k
      { s with nodeAt := s.nodeAt.insert ip n, badFlag := bf }
  | n@(.store _ ip t v _ k), s =>
    let bf :=
      if t == .bool then (argVarIds v).foldl (fun b x => b.insert x true) s.badFlag
      else s.badFlag
    scanDefs I r0 r1 v0 v1 conds isBool bparams k
      { s with nodeAt := s.nodeAt.insert ip n, badFlag := bf }
  | n@(.call _ ip nv0 _ _ bs _ k), s =>
    let bf := ((List.range bs.length).map (nv0 + ·)).foldl
      (fun b d => if isBool d then b.insert d true else b) s.badFlag
    scanDefs I r0 r1 v0 v1 conds isBool bparams k
      { s with nodeAt := s.nodeAt.insert ip n, badFlag := bf }
  | n@(.jnz _ ip _ _ t e), s =>
    scanDefs I r0 r1 v0 v1 conds isBool bparams t
      (scanDefs I r0 r1 v0 v1 conds isBool bparams e { s with nodeAt := s.nodeAt.insert ip n })
  | n@(.skip _ ip k), s =>
    scanDefs I r0 r1 v0 v1 conds isBool bparams k { s with nodeAt := s.nodeAt.insert ip n }
  | n@(.jump _ ip j _ args), s =>
    let rec goArgs : {ts : List Ty} → Tup (Arg VNat) ts → List Nat → ScanInfo → ScanInfo
      | [], (), _, sc | _ :: _, _, [], sc => sc
      | .bool :: _, (.var v, as), p :: ps, sc =>
        goArgs as ps { sc with jumpEdges := (p, v) :: sc.jumpEdges }
      | .bool :: _, (.imm false, as), p :: ps, sc =>
        goArgs as ps { sc with immFalseJumps := (ip, j, p) :: sc.immFalseJumps }
      | .bool :: _, (.imm true, as), p :: ps, sc =>
        goArgs as ps { sc with badFlag := sc.badFlag.insert p true }
      | _ :: _, (_, as), _ :: ps, sc => goArgs as ps sc
    goArgs args (bparams.getD j []) { s with nodeAt := s.nodeAt.insert ip n }
  | .group _ bs k, s =>
    scanDefsB I r0 r1 v0 v1 conds isBool bparams bs
      (scanDefs I r0 r1 v0 v1 conds isBool bparams k s)
  | _, s => s

def scanDefsB (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (conds : List I.Cond)
    (isBool : Nat → Bool) (bparams : Trie (List Nat)) : TreeBlocks → ScanInfo → ScanInfo
  | .nil, s => s
  | .cons _ ps b bs, s =>
    let bp := ps.foldl (fun t (p, ty) => if ty == .bool then t.insert p true else t) s.isBParam
    scanDefsB I r0 r1 v0 v1 conds isBool bparams bs
      (scanDefs I r0 r1 v0 v1 conds isBool bparams b { s with isBParam := bp })
end

def markIfHoist (prevIp : Trie Nat) (hb : Trie Bool) (anc? : Option Nat) (ip : Nat) : Trie Bool :=
  let rec go : Nat → Nat → Trie Bool → Trie Bool
    | 0, _, t => t
    | f + 1, cur, t =>
      if Nat.beq cur (anc?.getD ip) then t.insert cur true
      else match prevIp.find? cur with
        | some p => go f p (t.insert cur true)
        | none => t
  match anc? with
  | some a =>
    if Nat.beq a ip then hb
    else match prevIp.find? ip with
      | some p => go (ip + 1) p hb
      | none => hb
  | none => hb

def stepScan (ip : Nat) (lvC afterC : List Nat) (prev? anc? : Option Nat)
    (s : ScanInfo) : ScanInfo :=
  { s with
    prevIp := match prev? with | some p => s.prevIp.insert ip p | none => s.prevIp,
    anchorOf := match anc? with | some a => s.anchorOf.insert ip a | none => s.anchorOf,
    liveIn := s.liveIn.insert ip lvC,
    liveAfter := s.liveAfter.insert ip afterC,
    interf := lvC.foldl (fun t x => addInterfList t x lvC) s.interf,
    varLiveIps := afterC.foldl (fun t x => trieAdd t x ip) s.varLiveIps }

mutual
def scanRanges (isCand : Nat → Bool) (lTrie : Trie (List Nat)) :
    Option Nat → Option Nat → Tree → ScanInfo → ScanInfo
  | prev?, anchor?, .let_ lv ip nv0 ts op k, s =>
    let lvC := lv.filter isCand
    let anc? := if lvC.isEmpty then some ip else anchor?
    let defs := (List.range ts.length).map (nv0 + ·)
    let afterC := (k.lv.filter isCand).filter (!natMem · defs)
    let s1 := stepScan ip lvC afterC prev? anc? s
    let uses := (opVarIds op).foldl (fun u x => if isCand x then trieAdd u x ip else u) s1.usesOf
    let interf := match defs.find? (s1.defIp.find? · == some ip) with
      | some d => addInterfList s1.interf d afterC
      | none => s1.interf
    let { sig := _, code, args } := op
    let hasImmF := match code, args with
      | .addc _, (_, _, .imm false, ()) | .subb _, (_, _, .imm false, ()) => true
      | _, _ => false
    let hb :=
      if hasImmF && defs.any (fun d => isCand d && s1.defIp.find? d == some ip) then
        markIfHoist s1.prevIp s1.hoistBlocked anc? ip
      else s1.hoistBlocked
    scanRanges isCand lTrie (some ip) anc? k
      { s1 with usesOf := uses, interf := interf, hoistBlocked := hb }
  | prev?, anchor?, .load lv ip _ _ _ k, s | prev?, anchor?, .store lv ip _ _ _ k, s =>
    let lvC := lv.filter isCand
    let anc? := if lvC.isEmpty then some ip else anchor?
    scanRanges isCand lTrie (some ip) anc? k (stepScan ip lvC (k.lv.filter isCand) prev? anc? s)
  | prev?, _, .call lv ip _ _ _ _ _ k, s =>
    scanRanges isCand lTrie (some ip) none k (stepScan ip (lv.filter isCand) [] prev? none s)
  | prev?, anchor?, .jnz lv ip cx _ t e, s =>
    let lvC := lv.filter isCand
    let anc? := if lvC.isEmpty && !isCand cx then none else anchor?
    let s1 := stepScan ip lvC (union (t.lv.filter isCand) (e.lv.filter isCand)) prev? anc? s
    let uses := if isCand cx then trieAdd s1.usesOf cx ip else s1.usesOf
    scanRanges isCand lTrie (some ip) anc? t
      (scanRanges isCand lTrie (some ip) anc? e { s1 with usesOf := uses })
  | prev?, anchor?, .skip lv ip k, s =>
    let lvC := lv.filter isCand
    let anc? := if lvC.isEmpty then some ip else anchor?
    scanRanges isCand lTrie (some ip) anc? k (stepScan ip lvC lvC prev? anc? s)
  | prev?, anchor?, .jump lv ip j _ _, s =>
    let lvC := lv.filter isCand
    let anc? := if lvC.isEmpty then some ip else anchor?
    let s1 := stepScan ip lvC ((lTrie.getD j []).filter isCand) prev? anc? s
    let hb :=
      if s1.immFalseJumps.any (fun (ij, _, p) => Nat.beq ij ip && isCand p) then
        markIfHoist s1.prevIp s1.hoistBlocked anc? ip
      else s1.hoistBlocked
    { s1 with hoistBlocked := hb }
  | prev?, _, .ret lv ip _ _, s | prev?, _, .exit lv ip _ _ _, s =>
    stepScan ip (lv.filter isCand) [] prev? none s
  | prev?, anchor?, .group _ bs k, s =>
    scanRangesB isCand lTrie bs (scanRanges isCand lTrie prev? anchor? k s)
  | _, _, .stop _, s => s

def scanRangesB (isCand : Nat → Bool) (lTrie : Trie (List Nat)) :
    TreeBlocks → ScanInfo → ScanInfo
  | .nil, s => s
  | .cons _ ps b bs, s =>
    let pC := (ps.map Prod.fst).filter isCand
    let bC := b.lv.filter isCand
    let interf := pC.foldl (fun t p => addInterfList (addInterfList t p bC) p pC) s.interf
    scanRangesB isCand lTrie bs (scanRanges isCand lTrie none none b { s with interf := interf })
end

structure FlagState (Cond : Type) where
  flagHome : Trie Cond := .empty
  variant : Trie VariantHint := .empty
  clearAt : Trie Bool := .empty
  lockedClob : Trie FlagMask := .empty

def maskOf {I : Isa} (fh : Trie I.Cond) (xs : List Nat) : FlagMask :=
  xs.foldl
    (fun m x => match fh.find? x with | some c => m ||| I.gpr.condReads c | none => m)
    0#8

def lockVh {C : Type} (ip : Nat) (vh : VariantHint) (cl : FlagMask)
    (st : FlagState C) : FlagState C :=
  { st with
    variant := if vh == .default then st.variant else st.variant.insert ip vh,
    lockedClob := st.lockedClob.insert ip cl }

def probeIntervening (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (conds : List I.Cond)
    (isCand : Nat → Bool) (info : ScanInfo) (fArg : Nat → Option I.Cond) (reqMask : FlagMask)
    (ip : Nat) (st : FlagState I.Cond) : Option (FlagState I.Cond) :=
  match st.lockedClob.find? ip with
  | some cl => if FlagMask.disjoint reqMask cl then some st else none
  | none => match info.nodeAt.find? ip with
    | none => some st
    | some (.let_ _ _ nv0 ts op _) =>
      let { sig := _, code, args := _ } := op
      match ts, code with
      | [.bool], .cmp _ (.bits _) .bool _ =>
        (probeOp I r0 r1 v0 v1 fArg st.flagHome.find? none nv0 op .default).bind fun cl =>
          if FlagMask.disjoint reqMask cl then some st
          else if !isCand nv0 then none
          else conds.findSome? fun c =>
            let fDst x := if Nat.beq x nv0 then some c else none
            (probeOp I r0 r1 v0 v1 fArg fDst none nv0 op .decInc).bind fun cl' =>
              let usesOk := (info.usesOf.getD nv0 []).all fun u =>
                match info.nodeAt.find? u with
                | some (.let_ _ _ nu _ opU _) =>
                  (carryVhs opU).any fun vhU =>
                    let fArgU y := if Nat.beq y nv0 then some c else fArg y
                    (probeOp I r0 r1 v0 v1 fArgU (fun _ => none) none nu opU vhU).isSome
                | _ => true
              if FlagMask.disjoint reqMask cl' && usesOk then
                some { lockVh ip .decInc cl' st with flagHome := st.flagHome.insert nv0 c }
              else none
      | [.bits _, .bool], .addc _ | [.bits _, .bool], .subb _ =>
        let cOut := nv0 + 1
        if (st.flagHome.find? cOut).isSome then none
        else
          let defOk := match probeOp I r0 r1 v0 v1 fArg (fun _ => none) none nv0 op .default with
            | some cl => FlagMask.disjoint reqMask cl
            | none => false
          if defOk then some st
          else
            let fDst (c : I.Cond) (x : Nat) := if Nat.beq x cOut then some c else none
            let canCarry := isCand cOut && [VariantHint.adcx, .adox].any fun vh =>
              conds.any fun c =>
                let immF := if I.gpr.zeroFlags.contains c then some c else none
                match probeOp I r0 r1 v0 v1 fArg (fDst c) immF nv0 op vh with
                | some cl => FlagMask.disjoint reqMask cl
                | none => false
            if canCarry then some st else none
      | _, _ =>
        (VariantHint.default :: altVariantsFor op).findSome? fun vh =>
          (probeOp I r0 r1 v0 v1 fArg st.flagHome.find? none nv0 op vh).bind fun cl =>
            if FlagMask.disjoint reqMask cl then some (lockVh ip vh cl st) else none
    | some (.load _ _ _ t _ _) =>
      match I.gpr.load t r0 (.baseDisp r0 0) <|> v0.bind (I.vec.vload t · (.baseDisp r0 0)) with
      | some (_, cl) => if FlagMask.disjoint reqMask cl then some st else none
      | none => none
    | some (.store _ _ t _ _ _) =>
      match
        I.gpr.store t (.gpr r0) (.baseDisp r0 0) <|> v0.bind (I.vec.vstore t · (.baseDisp r0 0))
      with
      | some (_, cl) => if FlagMask.disjoint reqMask cl then some st else none
      | none => none
    | some (.jnz _ _ cx _ _ _) =>
      if (fArg cx).isSome || FlagMask.disjoint reqMask (I.gpr.jnzGpr r0 "").2 then some st
      else none
    | some (.call ..) => none
    | _ => some st

def placeOrHoistClear (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (conds : List I.Cond)
    (isCand : Nat → Bool) (info : ScanInfo) (cc : I.Cond) (ip : Nat)
    (extraLive : Std.HashSet Nat) (st : FlagState I.Cond) : Option (FlagState I.Cond) :=
  if !I.gpr.zeroFlags.contains cc then none else
    let noLive (xs : List Nat) :=
      xs.all fun y => !extraLive.contains y && (st.flagHome.find? y).isNone
    let safeHere := match info.nodeAt.find? ip with
      | some (.let_ ..) => noLive (info.liveIn.getD ip [])
      | _ => noLive (info.liveIn.getD ip []) && noLive (info.liveAfter.getD ip [])
    if safeHere then some { st with clearAt := st.clearAt.insert ip true } else
      (info.anchorOf.find? ip).bind fun a =>
        if Nat.beq a ip || !noLive (info.liveIn.getD a []) then none else
          let rec collectPath : Nat → Nat → List Nat → Option (List Nat)
            | 0, _, _ => none
            | f + 1, cur, acc =>
              if Nat.beq cur a then some (a :: acc)
              else (info.prevIp.find? cur).bind fun p => collectPath f p (cur :: acc)
          (info.prevIp.find? ip).bind fun p => (collectPath (ip + 1) p []).bind fun path =>
            let st'? := path.foldl (fun acc? ip' => acc?.bind fun stAcc =>
              let req := I.gpr.condReads cc ||| maskOf stAcc.flagHome (info.liveAfter.getD ip' [])
              let fArg x := if extraLive.contains x then some cc else stAcc.flagHome.find? x
              probeIntervening I r0 r1 v0 v1 conds isCand info fArg req ip' stAcc) (some st)
            st'?.map fun st1 => { st1 with clearAt := st1.clearAt.insert a true }

def tryColorWeb (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (conds : List I.Cond)
    (isCand : Nat → Bool) (info : ScanInfo) (vars : List Nat) (st : FlagState I.Cond) :
    Option (FlagState I.Cond) :=
  let varSet : Std.HashSet Nat := Std.HashSet.ofList vars
  let liveSet : Std.HashSet Nat := vars.foldl
    (fun s v => (info.varLiveIps.getD v []).foldl (fun s ip => s.insert ip) s) {}
  let liveIps := liveSet.toList.mergeSort (· ≤ ·)
  let isFastCmp (cc : I.Cond) : Bool :=
    let cmpDefs := vars.filterMap fun v =>
      (info.defIp.find? v).bind fun ip =>
        match info.nodeAt.find? ip with
        | some (.let_ _ _ nv0 [.bool] op _) =>
          let { sig := _, code, args := _ } := op
          match code with
          | .cmp _ (.bits _) .bool _ => some (nv0, op)
          | _ => none
        | _ => none
    !cmpDefs.isEmpty && cmpDefs.all fun (nv0, op) =>
      let fDst x := if Nat.beq x nv0 then some cc else none
      match probeOpLen I r0 r1 v0 v1 st.flagHome.find? fDst none nv0 op .default with
      | some (_, len) => len ≤ 1
      | none => false
  let ordConds := conds.filter isFastCmp ++ conds.filter (!isFastCmp ·)
  ordConds.findSome? fun cc =>
    let fArg (x : Nat) := if varSet.contains x then some cc else st.flagHome.find? x
    let interfOk := vars.all fun v =>
      (info.interf.getD v []).all fun y =>
        varSet.contains y ||
          match st.flagHome.find? y with
          | some cy => FlagMask.disjoint (I.gpr.condReads cc) (I.gpr.condReads cy)
          | none => true
    if !interfOk then none else
    let st1? := vars.foldl (fun acc? v => acc?.bind fun stAcc =>
      match info.defIp.find? v with
      | none => some stAcc
      | some ip => (info.nodeAt.find? ip).bind fun node => match node with
        | .let_ _ _ nv0 ts op _ =>
          let liveOther := (info.liveAfter.getD ip []).filter (!varSet.contains ·)
          let cm := maskOf stAcc.flagHome liveOther
          let hasOther := !liveOther.isEmpty || info.hoistBlocked.getD ip false
          let locked := (stAcc.lockedClob.find? ip).isSome
          let { sig := _, code, args } := op
          match ts, code, args with
          | [.bool], .cmp _ (.bits _) .bool _, _ =>
            let vhs :=
              if locked then [stAcc.variant.getD ip .default]
              else if hasOther then [.decInc, .default] else [.default, .decInc]
            vhs.findSome? fun vh =>
              let fDst x := if Nat.beq x nv0 then some cc else none
              (probeOp I r0 r1 v0 v1 fArg fDst none nv0 op vh).bind fun cl =>
                if FlagMask.disjoint cm cl then some (lockVh ip vh cl stAcc) else none
          | [.bits _, .bool], .addc _, (_, _, cin, _)
          | [.bits _, .bool], .subb _, (_, _, cin, _) =>
            let vhs :=
              if locked then [stAcc.variant.getD ip .default]
              else if hasOther then [.adcx, .adox, .default] else [.default, .adcx, .adox]
            let tryVh (immF : Option I.Cond) (vh : VariantHint) :=
              let fDst x := if Nat.beq x (nv0 + 1) then some cc else none
              (probeOp I r0 r1 v0 v1 fArg fDst immF nv0 op vh).bind fun cl =>
                if FlagMask.disjoint cm cl then some cl else none
            let clr? := match cin with
              | .imm false =>
                vhs.findSome? fun vh =>
                  let immF := if I.gpr.zeroFlags.contains cc then some cc else none
                  (tryVh immF vh).bind fun cl =>
                    (placeOrHoistClear I r0 r1 v0 v1 conds isCand info cc ip varSet stAcc).map
                      (lockVh ip vh cl ·)
              | _ => none
            clr? <|> vhs.findSome? fun vh => (tryVh none vh).map (lockVh ip vh · stAcc)
          | _, _, _ => none
        | _ => none) (some st)
    let st2? := st1?.bind fun st1 => vars.foldl (fun acc? v => acc?.bind fun stAcc =>
      (info.usesOf.getD v []).foldl (fun ac? ip_u => ac?.bind fun stU =>
        match info.nodeAt.find? ip_u with
        | some (.let_ _ _ nv0 ts op _) =>
          let { sig := _, code, args := _ } := op
          match ts, code with
          | [.bits _, .bool], .addc _ | [.bits _, .bool], .subb _ =>
            let cOut := nv0 + 1
            if varSet.contains cOut then some stU else
              let vhs :=
                if (stU.lockedClob.find? ip_u).isSome then [stU.variant.getD ip_u .default]
                else [.default, .adcx, .adox]
              let fDst := match stU.flagHome.find? cOut with
                | some co => (fun x => if Nat.beq x cOut then some co else none)
                | none => (fun _ => none)
              let ok := vhs.any fun vh =>
                (probeOp I r0 r1 v0 v1 fArg fDst none nv0 op vh).isSome ||
                  (isCand cOut && conds.any fun co =>
                    let fDst' x := if Nat.beq x cOut then some co else none
                    (probeOp I r0 r1 v0 v1 fArg fDst' none nv0 op vh).isSome)
              if ok then some stU else none
          | _, _ =>
            let vh := stU.variant.getD ip_u .default
            if (probeOp I r0 r1 v0 v1 fArg stU.flagHome.find? none nv0 op vh).isSome then some stU
            else none
        | _ => some stU) (some stAcc)) (some st1)
    let st3? := st2?.bind fun st2 => liveIps.foldl (fun acc? ip' => acc?.bind fun stAcc =>
      if stAcc.clearAt.getD ip' false then none else
        let liveOther := (info.liveAfter.getD ip' []).filter (!varSet.contains ·)
        let req := I.gpr.condReads cc ||| maskOf stAcc.flagHome liveOther
        let fArgAcc x := if varSet.contains x then some cc else stAcc.flagHome.find? x
        probeIntervening I r0 r1 v0 v1 conds isCand info fArgAcc req ip' stAcc) (some st2)
    let st4? := st3?.bind fun st3 =>
      info.immFalseJumps.foldl (fun acc? (ipJ, _, p) => acc?.bind fun stAcc =>
        if varSet.contains p then
          placeOrHoistClear I r0 r1 v0 v1 conds isCand info cc ipJ varSet stAcc
        else some stAcc) (some st3)
    st4?.map fun st4 =>
      { st4 with flagHome := vars.foldl (fun fh v => fh.insert v cc) st4.flagHome }

def ufFind (rep : Trie Nat) (x : Nat) : Nat :=
  let rec go : Nat → Nat → Nat
    | 0, c => c
    | f + 1, c => match rep.find? c with
      | some p => if Nat.beq p c then c else go f p
      | none => c
  go 64 x

/-- One coloring round with candidates `isCand`; returns the final state and the candidates. -/
def colorRound (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (conds : List I.Cond)
    (nv : Nat) (lTrie : Trie (List Nat)) (t : Tree) (s0 : ScanInfo) (bf : Trie Bool)
    (isCand : Nat → Bool) : FlagState I.Cond × List Nat :=
  let info := scanRanges isCand lTrie none none t { s0 with badFlag := bf }
  let rep := info.jumpEdges.foldl (fun rep (p, v) =>
    if isCand p && isCand v then
      let rp := ufFind rep p; let rv := ufFind rep v
      if Nat.beq rp rv then rep else rep.insert rp rv
    else rep) (.empty : Trie Nat)
  let cands := (List.range nv).filter isCand
  let groups := cands.foldl
    (fun (g : Trie (List Nat)) x => let r := ufFind rep x; g.insert r (g.getD r [] ++ [x]))
    .empty
  let (bpWebs, locWebs) := (dedup (cands.map (ufFind rep))).foldl (fun (bps, locs) r =>
    let vs := groups.getD r []
    if vs.any (info.isBParam.getD · false) then (vs :: bps, locs)
    else (bps, (info.defIp.getD (vs.headD 0) 0, vs) :: locs)) ([], [])
  let st1 := bpWebs.foldl (fun st vs =>
    if vs.any (fun v => (st.flagHome.find? v).isSome) then st else
      match tryColorWeb I r0 r1 v0 v1 conds isCand info vs st with
      | some st' => st'
      | none =>
        (vs.filter (!info.isBParam.getD · false)).foldl (fun stAcc v =>
          (tryColorWeb I r0 r1 v0 v1 conds isCand info [v] stAcc).getD stAcc) st) {}
  let st2 := ((locWebs.mergeSort (fun a b => a.1 ≤ b.1)).map Prod.snd).foldl (fun st vs =>
    if vs.any (fun v => (st.flagHome.find? v).isSome) then st
    else (tryColorWeb I r0 r1 v0 v1 conds isCand info vs st).getD st) st1
  (st2, cands)

/-- Flag-web coloring to a fixpoint: a candidate left uncolored (e.g. an `.addc`/`.subb` carry-out
whose `adcx`/`adox` variant another web speculated on) is demoted to a non-candidate and the round
is rerun, so no colored web relies on a speculation that did not materialize. -/
def gatherFlags (I : Isa) (r0 r1 : I.Reg) (v0 v1 : Option I.VReg) (conds : List I.Cond) (nv : Nat)
    (fnParams : List Nat) (cross : Trie Bool) (bparams : Trie (List Nat)) (tys : Trie Ty)
    (lTrie : Trie (List Nat)) (t : Tree) : FlagHints I.Cond :=
  let isBool (x : Nat) : Bool := match tys.getD x i64 with | .bool => true | _ => false
  if !(List.range nv).any isBool then {} else
    let s0 := scanDefs I r0 r1 v0 v1 conds isBool bparams t {}
    let bf0 := (List.range nv).foldl
      (fun bf x => if isBool x && cross.getD x false then bf.insert x true else bf)
      (fnParams.foldl (fun bf x => if isBool x then bf.insert x true else bf) s0.badFlag)
    let bf := (List.range (s0.jumpEdges.length + 1)).foldl (fun bf _ =>
      s0.jumpEdges.foldl (fun bf (p, v) => if bf.getD v false then bf.insert p true else bf) bf)
      bf0
    let isCand (x : Nat) : Bool := isBool x && !bf.getD x false
    let rec loop : Nat → Std.HashSet Nat → FlagState I.Cond
      | 0, failed => (colorRound I r0 r1 v0 v1 conds nv lTrie t s0 bf
          fun x => isCand x && !failed.contains x).1
      | fuel + 1, failed =>
        let (st, cands) := colorRound I r0 r1 v0 v1 conds nv lTrie t s0 bf
          fun x => isCand x && !failed.contains x
        let newFail := cands.filter fun x => (st.flagHome.find? x).isNone
        if newFail.isEmpty then st else loop fuel (newFail.foldl (·.insert ·) failed)
    let st := loop (nv + 2) {}
    { flagHome := st.flagHome, variant := st.variant, clearAt := st.clearAt }

end SpillFlags
end LeanQbe.T
