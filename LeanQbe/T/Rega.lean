module

public import LeanQbe.T.RegaDefs
public import LeanQbe.T.RegaZero
public import LeanQbe.T.RegaZext
public import LeanQbe.T.RegaCmpReuse
public import LeanQbe.T.RegaRemat

/-!
# PHOAS-First Checked Register-Allocation Lowering (`Rega`)

Direct structural lowering of `Expr VNat LNat rs` / `Blocks VNat LNat rs sig` (zero
`TFlat`/`denote`) consuming untrusted literal `LeanQbe.T.Trie` `Hints`: bounded `regs`, `O(log N)`
`slots : Trie SlotEntry` with 15-granule overlap clearing, lexical `defs : Trie DefFact` and
`vecWidths : Trie SlotWidth`, sequential `nv` (`h.dest` keyed by `x : Nat`), `entryScopeOk nv`,
read-only flag cache, `PreStep.clearFlags`, `canonAbi` (skipped by `abiSkips`
for canonical `.gprZ`/exact-immediate registers), `loadSext` fusion, `UXTW` `zext 32 64` fusion,
pure `Bool` comparisons, and monotone `nl` label counter.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-! ## Generic Kill Rule and Multi-Granule Slot Updates -/

def keepRegLoc (I : Isa) (gClob : List I.Reg) (vClob : List I.VReg) (fClob : FlagMask) :
    RegLoc I.Reg I.VReg I.Cond → Bool
  | .gpr r | .gprZ r => !(gClob.contains r)
  | .vec v => !(vClob.contains v)
  | .flag c => FlagMask.disjoint (I.gpr.condReads c) fClob

def killRegs (I : Isa) (gClob : List I.Reg) (vClob : List I.VReg) (fClob : FlagMask)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) :
    List (SymArg × RegLoc I.Reg I.VReg I.Cond) :=
  R.filter fun p => keepRegLoc I gClob vClob fClob p.2

def killZeroExt {Reg : Type} [DecidableEq Reg] (gClob : List Reg) (zeroExt : List Reg) : List Reg :=
  zeroExt.filter fun r => !(gClob.contains r)

def keepFlagCmp (I : Isa) (fClob : FlagMask) (eqNeOnly : Bool) : Bool :=
  (if eqNeOnly then [.eq, .ne]
   else [.eq, .ne, .ult, .ule, .ugt, .uge, .slt, .sle, .sgt, .sge]).all fun co =>
    match I.gpr.condOfCmp? co with
    | some cc => FlagMask.disjoint (I.gpr.condReads cc) fClob
    | none => true

def killFlags (I : Isa) (fClob : FlagMask) : Option FlagFact → Option FlagFact
  | some (.cmp w l r eqNe) => if keepFlagCmp I fClob eqNe then some (.cmp w l r eqNe) else none
  | none => none

def eraseIfOverlaps (i d : Nat) (slots : Trie SlotEntry) : Trie SlotEntry :=
  if Nat.ble d i then
    match slots.find? (i - d) with
    | some se => if Nat.ble (d + 1) se.slots then slots.erase (i - d) else slots
    | none => slots
  else slots

def eraseSeq (i : Nat) : Nat → Trie SlotEntry → Trie SlotEntry
  | 0, slots => slots | k + 1, slots => eraseSeq (i + 1) k (slots.erase i)

def clearSlotRange (i k : Nat) (slots : Trie SlotEntry) : Trie SlotEntry :=
  eraseSeq i k (eraseIfOverlaps i 1 (eraseIfOverlaps i 2 (eraseIfOverlaps i 3
    (eraseIfOverlaps i 4 (eraseIfOverlaps i 5 (eraseIfOverlaps i 6
      (eraseIfOverlaps i 7 slots)))))))

def addSlotEntry (vw : Trie SlotWidth) (sa : SymArg) (i : Nat) (w : SlotWidth)
    (slots : Trie SlotEntry) : Option (Trie SlotEntry) :=
  match symArgWidth vw sa with
  | some wsa =>
    if !Nat.ble wsa.bits w.bits then none
    else match slots.find? i with
      | some (.vec w' sas) =>
        if slotWidthEq w' w then some (slots.insert i (.vec w (sa :: sas)))
        else some ((clearSlotRange i w.slots slots).insert i (.vec w [sa]))
      | _ => some ((clearSlotRange i w.slots slots).insert i (.vec w [sa]))
  | none =>
    if !slotWidthEq w .w64 then none
    else match slots.find? i with
      | some (.gpr sas) => some (slots.insert i (.gpr (sa :: sas)))
      | _ => some ((clearSlotRange i 1 slots).insert i (.gpr [sa]))

/-! ## Checked Moves and `PreStep` -/

def gprEntries {I : Isa} (r : I.Reg)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : List SymArg :=
  R.filterMap fun (sa, rl) =>
    match rl with | .gpr r' | .gprZ r' => if r' == r then some sa else none | _ => none

def gprTaggedEntries {I : Isa} (r : I.Reg)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : List (SymArg × Bool) :=
  R.filterMap fun (sa, rl) =>
    match rl with
    | .gpr r' => if r' == r then some (sa, false) else none
    | .gprZ r' => if r' == r then some (sa, true) else none
    | _ => none

def vecEntries {I : Isa} (vw : Trie SlotWidth) (w : SlotWidth) (v : I.VReg)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : List SymArg :=
  R.filterMap fun (sa, rl) =>
    match rl with
    | .vec v' =>
      if v' == v then
        match symArgWidth vw sa with
        | some wsa => if Nat.ble wsa.bits w.bits then some sa else none
        | none => none
      else none
    | _ => none

def flagEntries {I : Isa} (c : I.Cond)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : List SymArg :=
  R.filterMap fun (sa, rl) =>
    match rl with | .flag c' => if c' == c then some sa else none | _ => none

def execMove (I : Isa) (nslots : Nat) (saved : List I.Reg) (mv : I.Move) (st : SymState I)
    (deadHint : Bool := false) : Option (List I.Directive × SymState I) :=
  match mv with
  | .mov d s =>
    if !isMoveGpr I saved d then none
    else if d == s then some (I.gpr.mov d s, st)
    else
      let zExt := if st.zeroExt32.contains s then d :: killZeroExt [d] st.zeroExt32
                  else killZeroExt [d] st.zeroExt32
      some (I.gpr.mov d s,
        { st with
          regs := (gprTaggedEntries s st.regs).map (fun (sa, z) =>
                    (sa, if z then RegLoc.gprZ d else .gpr d)) ++
                  killRegs I [d] [] FlagMask.none st.regs
          zeroExt32 := zExt })
  | .movi d c =>
    if !isMoveGpr I saved d then none
    else
      let clob := d :: I.frame.scratch
      let zExt := if (c.setWidth 32).setWidth 64 == c then d :: killZeroExt clob st.zeroExt32
                  else killZeroExt clob st.zeroExt32
      let (code, fClob) := execMovi I st deadHint d c
      some (code,
        { st with
          regs := (.immBits 64 c, .gpr d) :: killRegs I clob [] fClob st.regs
          zeroExt32 := zExt
          flags := if fClob == FlagMask.none then st.flags else killFlags I fClob st.flags })
  | .ld d i =>
    if !(isAllocGpr I saved d && Nat.ble (i + 1) nslots) then none
    else
      let copied := match st.slots.find? i with
        | some (.gpr sas) => sas.map (·, RegLoc.gpr d)
        | some (.gprZ sas) => sas.map fun (sa, z) => (sa, if z then .gprZ d else .gpr d)
        | _ => []
      some (I.frame.slotLd d i,
        { st with
          regs := copied ++ killRegs I (d :: I.frame.scratch) [] FlagMask.none st.regs
          zeroExt32 := killZeroExt (d :: I.frame.scratch) st.zeroExt32 })
  | .st i s =>
    if !(!(I.frame.scratch.contains s) && Nat.ble (i + 1) nslots) then none
    else some (I.frame.slotSt i s,
      { st with
        regs := killRegs I I.frame.scratch [] FlagMask.none st.regs
        slots := (clearSlotRange i 1 st.slots).insert i (.gprZ (gprTaggedEntries s st.regs))
        zeroExt32 := killZeroExt I.frame.scratch st.zeroExt32 })
  | .setcc d c =>
    if !isAllocGpr I saved d then none
    else some (I.gpr.setcc d c,
      { st with
        regs := (flagEntries c st.regs).map (·, .gpr d) ++
                killRegs I (d :: I.frame.scratch) [] FlagMask.none st.regs
        zeroExt32 := killZeroExt (d :: I.frame.scratch) st.zeroExt32 })
  | .vmov w d s =>
    if !isMoveVec I d then none
    else some (I.vec.vmov w d s,
      { st with regs := (vecEntries st.vecWidths w s st.regs).map (·, .vec d) ++
                        killRegs I [] [d] FlagMask.none st.regs })
  | .vmovi w d c =>
    if !isAllocVec I d then none
    else match I.vec.vmovi w d c with
      | none => none
      | some code => some (code,
          { st with
            regs := (.immVec w c, .vec d) ::
                    killRegs I I.frame.scratch (d :: I.vec.vecScratch) FlagMask.none st.regs
            zeroExt32 := killZeroExt I.frame.scratch st.zeroExt32 })
  | .vld w d i =>
    if !(isAllocVec I d && Nat.ble (i + w.slots) nslots) then none
    else
      let copied := match st.slots.find? i with
        | some (.vec w' sas) => if slotWidthEq w' w then sas.map (·, .vec d) else [] | _ => []
      some (I.vec.vslotLd w d i,
        { st with
          regs := copied ++ killRegs I I.frame.scratch (d :: I.vec.vecScratch) FlagMask.none st.regs
          zeroExt32 := killZeroExt I.frame.scratch st.zeroExt32 })
  | .vst w i s =>
    if !(!(I.vec.vecScratch.contains s) && Nat.ble (i + w.slots) nslots) then none
    else some (I.vec.vslotSt w i s,
      { st with
        regs := killRegs I I.frame.scratch I.vec.vecScratch FlagMask.none st.regs
        slots := (clearSlotRange i w.slots st.slots).insert i
          (.vec w (vecEntries st.vecWidths w s st.regs))
        zeroExt32 := killZeroExt I.frame.scratch st.zeroExt32 })

def execMoves (I : Isa) (nslots : Nat) (saved : List I.Reg) :
    List I.Move → SymState I → (deadHint : Bool := false) → Option (List I.Directive × SymState I)
  | [], st, _ => some ([], st)
  | mv :: mvs, st, deadHint => (execMove I nslots saved mv st deadHint).bind fun (c1, st1) =>
      (execMoves I nslots saved mvs st1 deadHint).map fun (c2, st2) => (c1 ++ c2, st2)

def execClearFlags (I : Isa) (st : SymState I) : List I.Directive × SymState I :=
  (I.gpr.clearFlags, { st with
    regs := I.gpr.zeroFlags.map (.immBool false, .flag ·) ++
            killRegs I I.frame.scratch [] FlagMask.all st.regs
    zeroExt32 := killZeroExt I.frame.scratch st.zeroExt32
    flags := none })

def stepPre (I : Isa) (h : I.Hints) (ip : Nat) (st : SymState I) :
    Option (List I.Directive × SymState I) :=
  match h.pre.find? ip with
  | none => some ([], st)
  | some ps =>
    (execMoves I h.nslots h.saved ps.moves st (h.deadFlags.getD ip false)).map fun (mc, st1) =>
      if ps.clearFlags then let (cc, st2) := execClearFlags I st1; (mc ++ cc, st2) else (mc, st1)

/-! ## Target Presence Checking and Untrusted Parallel-Move Shuffle -/

def holdsLoc (I : Isa) (st : SymState I) (sa : SymArg) : I.Loc → Bool
  | .gpr r => st.regs.any fun (sa', rl) =>
    match rl with | .gpr r' | .gprZ r' => r' == r && symArgMatchesGpr sa' sa | _ => false
  | .vec v => st.regs.any fun (sa', rl) =>
    match rl with | .vec v' => v' == v && symArgEq sa' sa | _ => false
  | .flag c => st.regs.any fun (sa', rl) =>
    match rl with | .flag c' => c' == c && symArgEq sa' sa | _ => false
  | .slot i w =>
    match symArgWidth st.vecWidths sa with
    | some wsa =>
      Nat.ble wsa.bits w.bits &&
      match st.slots.find? i with
      | some (.vec w' sas) => slotWidthEq w' w && sas.any (symArgEq · sa)
      | _ => false
    | none =>
      slotWidthEq w .w64 &&
      match st.slots.find? i with
      | some (.gpr sas) => sas.any (symArgMatchesGpr · sa)
      | some (.gprZ sas) => sas.any fun (sa', _) => symArgMatchesGpr sa' sa
      | _ => false

def findVecFor (I : Isa) (noScr : Bool)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (sa : SymArg) : Option I.VReg :=
  R.findSome? fun (sa', rl) =>
    match rl with
    | .vec v => if (!noScr || !(I.vec.vecScratch.contains v)) && symArgEq sa' sa
                then some v else none
    | _ => none

def findFlagFor (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (sa : SymArg) : Option I.Cond :=
  R.findSome? fun (sa', rl) =>
    match rl with | .flag c => if symArgEq sa' sa then some c else none | _ => none

def findSlotFor (nslots : Nat) (slots : Trie SlotEntry) (sa : SymArg) : Option (Nat × SlotWidth) :=
  let rec go (i : Nat) : Nat → Option (Nat × SlotWidth)
    | 0 => none
    | fuel + 1 =>
      match slots.find? i with
      | some (.gpr sas) =>
        if sas.any (symArgMatchesGpr · sa) then some (i, .w64) else go (i + 1) fuel
      | some (.gprZ sas) =>
        if sas.any fun (sa', _) => symArgMatchesGpr sa' sa then some (i, .w64) else go (i + 1) fuel
      | some (.vec w sas) => if sas.any (symArgEq · sa) then some (i, w) else go (i + 1) fuel
      | none => go (i + 1) fuel
  go 0 nslots

def moveFor (I : Isa) (nslots : Nat) (st : SymState I) (sa : SymArg) : I.Loc → Option I.Move
  | .gpr d =>
    match sa with
    | .immBits _ c => some (.movi d c)
    | .immBool b => some (.movi d (if b then 1#64 else 0#64))
    | .var _ =>
      (findGprFor I false st.regs sa).map (.mov d) <|> (findFlagFor I st.regs sa).map (.setcc d) <|>
      match findSlotFor nslots st.slots sa with | some (i, .w64) => some (.ld d i) | _ => none
    | .immVec _ _ => none
  | .vec vd =>
    match sa with
    | .immVec w c => some (.vmovi w vd c)
    | .var _ =>
      match symArgWidth st.vecWidths sa with
      | none => none
      | some w => (findVecFor I false st.regs sa).map (.vmov w vd) <|>
                  (findSlotFor nslots st.slots sa).map fun (i, sw) => .vld sw vd i
    | _ => none
  | .slot i w =>
    match symArgWidth st.vecWidths sa with
    | some _ => (findVecFor I true st.regs sa).map (.vst w i)
    | none => (findGprFor I true st.regs sa).map (.st i)
  | .flag _ => none

def execShufMove (I : Isa) (nslots : Nat) (saved : List I.Reg)
    (mv : ShufMove I.Reg I.VReg I.Cond) (st : SymState I)
    (deadHint : Bool := false) : Option (List I.Directive × SymState I) :=
  match mv with
  | .base m => execMove I nslots saved m st deadHint
  | .rematAdd x base disp d =>
    if !isAllocGpr I saved d then none
    else match st.defs.find? x with
      | some (.addImm64 base' disp') =>
        if Nat.beq base' base && disp' == disp then
          (findGprFor I true st.regs (.var base)).bind fun rb =>
            (rematAddImm64 I rb d disp).map fun code =>
              let clob := d :: I.frame.scratch
              (code, { st with
                regs := (.var x, .gpr d) :: killRegs I clob [] FlagMask.none st.regs
                zeroExt32 := killZeroExt clob st.zeroExt32 })
        else none
      | _ => none

def execShufMoves (I : Isa) (nslots : Nat) (saved : List I.Reg) :
    List (ShufMove I.Reg I.VReg I.Cond) → SymState I → (deadHint : Bool := false) →
    Option (List I.Directive × SymState I)
  | [], st, _ => some ([], st)
  | mv :: mvs, st, deadHint => (execShufMove I nslots saved mv st deadHint).bind fun (c1, st1) =>
      (execShufMoves I nslots saved mvs st1 deadHint).map fun (c2, st2) => (c1 ++ c2, st2)

def isVarSymArg : SymArg → Bool | .var _ => true | _ => false

def regOnlyHoldsVar (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (sa : SymArg) (r : I.Reg) : Bool :=
  R.all (fun (sa', rl) => !symArgEq sa' sa || regLocMatchesGpr rl r) &&
  R.any (fun (sa', rl) => symArgEq sa' sa && regLocMatchesGpr rl r)

def regOnlyNonScrHoldsVar (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (sa : SymArg) (r : I.Reg) : Bool :=
  !(I.frame.scratch.contains r) &&
  R.all (fun (sa', rl) => !symArgEq sa' sa ||
    match rl with
    | .gpr r' | .gprZ r' => I.frame.scratch.contains r' || r' == r
    | _ => true) &&
  R.any (fun (sa', rl) => symArgEq sa' sa && regLocMatchesGpr rl r)

def locRematBlocked (I : Isa) (st : SymState I) (pend : List (SymArg × I.Loc)) (r : I.Reg) : Bool :=
  pend.any fun (sa, d') =>
    !(locEq d' (.gpr r)) &&
    match sa with
    | .var x =>
      (findGprFor I false st.regs sa).isNone && (findFlagFor I st.regs sa).isNone &&
      match st.defs.find? x with
      | some (.addImm64 base _) => regOnlyNonScrHoldsVar I st.regs (.var base) r
      | _ => false
    | _ => false

def locBlocked (I : Isa) (st : SymState I) (pend : List (SymArg × I.Loc)) (d : I.Loc) : Bool :=
  pend.any fun (sa, d') =>
    !(locEq d' d) && isVarSymArg sa &&
    match d with
    | .gpr r =>
      regOnlyHoldsVar I st.regs sa r ||
      match sa with
      | .var x =>
        (findGprFor I false st.regs sa).isNone && (findFlagFor I st.regs sa).isNone &&
        match st.defs.find? x with
        | some (.addImm64 base _) => regOnlyNonScrHoldsVar I st.regs (.var base) r
        | _ => false
      | _ => false
    | .vec v =>
      st.regs.all (fun (sa', rl) => !symArgEq sa' sa || regLocEq rl (.vec v)) &&
      st.regs.any (fun (sa', rl) => symArgEq sa' sa && regLocEq rl (.vec v))
    | _ => false

def findRematSlotTmp (I : Isa) (saved : List I.Reg) (st : SymState I)
    (targets pend : List (SymArg × I.Loc)) : Option I.Reg :=
  (I.frame.allocatable ++ saved).find? fun r =>
    !(I.frame.scratch.contains r) && !(locBlocked I st pend (.gpr r)) &&
    !(targets.any fun (_, loc) => locEq loc (.gpr r))

def moveForShuf (I : Isa) (nslots : Nat) (saved : List I.Reg) (st : SymState I)
    (targets pend : List (SymArg × I.Loc)) (sa : SymArg) :
    I.Loc → Option (ShufMove I.Reg I.VReg I.Cond)
  | .gpr d =>
    (moveFor I nslots st sa (.gpr d)).map .base <|>
      match sa with
      | .var x =>
        if isAllocGpr I saved d then
          (rematBaseOf? I st x).bind fun (base, disp, rb) =>
            (rematAddImm64 I rb d disp).map fun _ => .rematAdd x base disp d
        else none
      | _ => none
  | .slot i .w64 =>
    (moveFor I nslots st sa (.slot i .w64)).map .base <|>
      match sa with
      | .var x =>
        (rematBaseOf? I st x).bind fun (base, disp, rb) =>
          (findRematSlotTmp I saved st targets pend).bind fun tmp =>
            (rematAddImm64 I rb tmp disp).map fun _ => .rematAdd x base disp tmp
      | _ => none
  | loc => (moveFor I nslots st sa loc).map .base

def rangesOverlap (i1 k1 i2 k2 : Nat) : Bool :=
  Nat.ble (i1 + 1) (i2 + k2) && Nat.ble (i2 + 1) (i1 + k1)

def slotBusy (I : Isa) (st : SymState I) (pend : List (SymArg × I.Loc)) (i k : Nat) : Bool :=
  pend.any (fun (_, loc) =>
    match loc with | .slot j w => rangesOverlap i k j w.slots | _ => false) ||
  let rec scan (j : Nat) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      (match st.slots.find? j with | some se => rangesOverlap i k j se.slots | none => false) ||
      scan (j + 1) fuel
  scan (i - 7) (k + 7)

def findFreeSlot (I : Isa) (nslots : Nat) (st : SymState I)
    (pend : List (SymArg × I.Loc)) (k : Nat) : Option Nat :=
  let rec go (i : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      if Nat.ble (i + k) nslots && !(slotBusy I st pend i k) then some i else go (i + 1) fuel
  go 0 nslots

def maxSlotWidth (a b : SlotWidth) : SlotWidth := if Nat.ble a.bits b.bits then b else a

def vecWidthAt (I : Isa) (st : SymState I) (vd : I.VReg) : SlotWidth :=
  st.regs.foldl (fun w (sa, rl) => match rl with
    | .vec v =>
      if v == vd then
        match symArgWidth st.vecWidths sa with | some ws => maxSlotWidth w ws | none => w
      else w
    | _ => w) .w64

def pmoveAux (I : Isa) (nslots : Nat) (saved : List I.Reg) :
    Nat → SymState I → List (SymArg × I.Loc) → List (ShufMove I.Reg I.VReg I.Cond) →
    List (ShufMove I.Reg I.VReg I.Cond)
  | 0, _, _, acc => acc.reverse
  | fuel + 1, st, targets, acc =>
    match targets.filter fun (sa, loc) => !holdsLoc I st sa loc with
    | [] => acc.reverse
    | pend =>
      let goMv (mv : ShufMove I.Reg I.VReg I.Cond) : List (ShufMove I.Reg I.VReg I.Cond) :=
        match execShufMove I nslots saved mv st with
        | some (_, st') => pmoveAux I nslots saved fuel st' pend (mv :: acc)
        | none => acc.reverse
      let step (sa : SymArg) (loc : I.Loc) : List (ShufMove I.Reg I.VReg I.Cond) :=
        match moveForShuf I nslots saved st targets pend sa loc with
        | some mv => goMv mv
        | none => acc.reverse
      match pend.find? fun (sa, loc) => isVarSymArg sa && !(locBlocked I st pend loc) with
      | some (sa, loc) => step sa loc
      | none =>
        match pend.find? fun (sa, loc) =>
            isVarSymArg sa && match loc with | .gpr _ => true | _ => false with
        | some (_, .gpr d) =>
          let tmp? :=
            (if locRematBlocked I st pend d then findRematSlotTmp I saved st targets pend
             else none) <|>
            (I.frame.scratch.find? fun tmp => !(locBlocked I st pend (.gpr tmp)))
          match tmp? with
          | some tmp => goMv (.base (.mov tmp d))
          | none =>
            match findFreeSlot I nslots st pend 1 with
            | some sl =>
              if !(I.frame.scratch.contains d) then goMv (.base (.st sl d)) else acc.reverse
            | none => acc.reverse
        | _ =>
          match pend.find? fun (sa, loc) =>
              isVarSymArg sa && match loc with | .vec _ => true | _ => false with
          | some (_, .vec vd) =>
            let w := vecWidthAt I st vd
            match I.vec.vecScratch.find? fun vtmp => !(locBlocked I st pend (.vec vtmp)) with
            | some vtmp => goMv (.base (.vmov w vtmp vd))
            | none =>
              match findFreeSlot I nslots st pend w.slots with
              | some sl =>
                if !(I.vec.vecScratch.contains vd) then goMv (.base (.vst w sl vd)) else acc.reverse
              | none => acc.reverse
          | _ => match pend.head? with | some (sa, loc) => step sa loc | none => acc.reverse

def shuffle (I : Isa) (nslots : Nat) (saved : List I.Reg) (st : SymState I)
    (tgts : List (SymArg × I.Loc)) (deadHint : Bool := false) :
    Option (List I.Directive × SymState I) :=
  if tgts.all fun (sa, loc) => holdsLoc I st sa loc then some ([], st)
  else
    let mvs := pmoveAux I nslots saved (3 * tgts.length + 4) st tgts []
    match execShufMoves I nslots saved mvs st deadHint with
    | none => none
    | some (code, st') =>
      if tgts.all fun (sa, loc) => holdsLoc I st' sa loc then some (code, st') else none

/-! ## ABI Helpers, Lexical Defs, and Operand/Destination Resolution -/

def abiTargets (I : Isa) :
    {ts : List Ty} → Tup (Arg VNat) ts → Tup (AbiReg I.Reg I.VReg) ts →
    Option (List (SymArg × I.Loc))
  | [], (), () => some []
  | t :: _, (a, as), (loc, locs) =>
    match toSymArg I t a, abiTargets I as locs with
    | some sa, some rest =>
      some ((sa, match loc with | .gpr r => .gpr r | .vec v => .vec v) :: rest)
    | _, _ => none

def hasVarGpr (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (x : Nat) (rd : I.Reg) : Bool :=
  R.any fun (sa, rl) => symArgEq sa (.var x) && regLocMatchesGpr rl rd

/-- `true` when `R` and `zeroExt` prove GPR `r` already holds the canonical
(zero-extended ABI) form of `sa`: a `.gprZ r` variable, a zero-extended `.bits 32`
variable in `zeroExt`, or an exact 64-bit immediate. -/
def abiHeld (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (zeroExt : List I.Reg) (t : Ty) (r : I.Reg) : SymArg → Bool
  | .var x =>
    (tyEq t (.bits 32) && zeroExt.contains r && hasVarGpr I R x r) ||
    R.any fun (sa', rl) => symArgEq sa' (.var x) && regLocEq rl (.gprZ r)
  | .immBits _ c => R.any fun (sa', rl) => symArgEq sa' (.immBits 64 c) && regLocMatchesGpr rl r
  | .immBool b => R.any fun (sa', rl) =>
    symArgEq sa' (.immBits 64 (if b then 1#64 else 0#64)) && regLocMatchesGpr rl r
  | .immVec _ _ => false

/-- Per-position `canonAbi` skip flags of ABI targets `args`/`locs` against
post-shuffle `R` and `zeroExt`. -/
def abiSkips (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (zeroExt : List I.Reg) :
    {ts : List Ty} → Tup (Arg VNat) ts → Tup (AbiReg I.Reg I.VReg) ts → List Bool
  | [], (), () => []
  | t :: _, (a, as), (loc, locs) =>
    (match loc, toSymArg I t a with
     | .gpr r, some sa => abiHeld I R zeroExt t r sa
     | _, _ => false) :: abiSkips I R zeroExt as locs

/-- ABI canonicalization code, skipping GPR positions flagged in `sk` (see `abiSkips`). -/
def canonAbiCode (I : Isa) :
    {ts : List Ty} → Tup (AbiReg I.Reg I.VReg) ts → List Bool → List I.Directive
  | [], (), _ => []
  | t :: _, (.gpr r, locs), sk =>
    (if sk.headD false then [] else (I.frame.canonAbi t r).1) ++ canonAbiCode I locs sk.tail
  | _ :: _, (.vec _, locs), sk => canonAbiCode I locs sk.tail

def saveCsList (I : Isa) (base : Nat) : List I.Reg → List I.Directive
  | [] => [] | r :: rs => I.frame.slotSt base r ++ saveCsList I (base + 1) rs

def restoreCsList (I : Isa) (base : Nat) : List I.Reg → List I.Directive
  | [] => [] | r :: rs => I.frame.slotLd r base ++ restoreCsList I (base + 1) rs

def saveCs (I : Isa) (base : Nat) (rs : List I.Reg) : List I.Directive :=
  match rs with
  | [] => []
  | _ => match I.frame.saveRegs? with
    | some fn => fn base rs
    | none => saveCsList I base rs

def restoreCs (I : Isa) (base : Nat) (rs : List I.Reg) : List I.Directive :=
  match rs with
  | [] => []
  | _ => match I.frame.restoreRegs? with
    | some fn => fn base rs
    | none => restoreCsList I base rs

def recordAddVarImm (defs : Trie DefFact) (x : Nat) (c : BitVec 64) : DefFact :=
  match defs.find? x with
  | some (.imm64 c0) => .imm64 (c0 + c)
  | some (.addImm64 b d) => .addImm64 b (d + c)
  | some (.scaleOff idx sh d) => .scaleOff idx sh (d + c)
  | some (.addrSum b idx sh d) =>
    if Nat.beq sh 0 then .addImm64 x c
    else .addrSum b idx sh (d + c)
  | _ => .addImm64 x c

def recordAddScale (dfx : DefFact) (dfy? : Option DefFact) (y : Nat) : Option DefFact :=
  match dfx with
  | .scaleOff idx sh d1 =>
    if Nat.ble sh 3 then
      match dfy? with
      | some (.addImm64 b d2) => some (.addrSum b idx sh (d1 + d2))
      | _ => some (.addrSum y idx sh d1)
    else none
  | _ => none

def recordAddBase (dfx : DefFact) (y : Nat) (dfy? : Option DefFact) : Option DefFact :=
  match dfx with
  | .addImm64 b d1 =>
    match dfy? with
    | some (.addImm64 b2 d2) => some (.addrSum b b2 0 (d1 + d2))
    | _ => some (.addrSum b y 0 d1)
  | _ => none

def recordAddVarVar (defs : Trie DefFact) (x y : Nat) : DefFact :=
  let dfx? := defs.find? x
  let dfy? := defs.find? y
  match dfx?, dfy? with
  | some (.imm64 c), _ => recordAddVarImm defs y c
  | _, some (.imm64 c) => recordAddVarImm defs x c
  | _, _ =>
    let s1 := dfx?.bind (recordAddScale · dfy? y)
    let s2 := dfy?.bind (recordAddScale · dfx? x)
    let b1 := dfx?.bind (recordAddBase · y dfy?)
    let b2 := dfy?.bind (recordAddBase · x dfx?)
    (s1 <|> s2 <|> b1 <|> b2).getD (.addrSum x y 0 0)

def recordRmwBin (w : Nat) (op : RmwOp) (a b : Arg VNat (.bits w)) : Option DefFact :=
  if !Nat.ble w 64 then none
  else match a, b with
    | .var x, .var y => some (.binVarVar w op x y)
    | .var x, .imm c => some (.binVarImm w op x (c.setWidth 64))
    | .imm c, .var y => if op.isComm then some (.binVarImm w op y (c.setWidth 64)) else none
    | _, _ => none

def recordDef (defs : Trie DefFact) :
    {sig rs : List Ty} → OpCode sig rs → Tup (Arg VNat) sig → Option DefFact
  | _, _, .add (.bits n), (a, b, ()) =>
    if !Nat.beq n 64 then recordRmwBin n .add a b
    else match a, b with
      | .var x, .imm c | .imm c, .var x => some (recordAddVarImm defs x (c.setWidth 64))
      | .var x, .var y => some (recordAddVarVar defs x y)
      | _, _ => none
  | _, _, .sub (.bits n), (a, b, ()) =>
    match a, b with
    | .var x, .imm c =>
      if Nat.beq n 64 then some (recordAddVarImm defs x (-(c.setWidth 64)))
      else recordRmwBin n .sub (.var x) (.imm c)
    | _, _ => recordRmwBin n .sub a b
  | _, _, .or  (.bits n), (a, b, ()) => recordRmwBin n .or a b
  | _, _, .xor (.bits n), (a, b, ()) => recordRmwBin n .xor a b
  | _, _, .shl (.bits n), (.var x, .imm k, ()) =>
    let kn := k.toNat
    if Nat.beq n 64 then
      if !Nat.blt kn 64 then none else
        match defs.find? x with
        | some (.imm64 c0) => some (.imm64 (c0 <<< kn))
        | some (.addImm64 b d) => some (.scaleOff b kn (d <<< kn))
        | some (.scaleOff idx sh d) =>
          if Nat.blt (sh + kn) 64 then some (.scaleOff idx (sh + kn) (d <<< kn)) else none
        | _ => some (.scaleOff x kn 0)
    else if Nat.ble n 64 && Nat.blt 0 n && Nat.blt kn n then
      some (.shlVarImm n x kn)
    else none
  | _, _, .lshr (.bits n), (.var x, .imm k, ()) => recordShiftImm n .lsr x k
  | _, _, .ashr (.bits n), (.var x, .imm k, ()) => recordShiftImm n .asr x k
  | _, _, .copy (.bits n), (.imm c, ()) =>
    if Nat.beq n 64 then some (.imm64 (c.setWidth 64)) else none
  | _, _, .copy (.bits n), (.var x, ()) =>
    if Nat.beq n 64 then
      match defs.find? x with
      | some d => if d.isAddr then some d else some (.addImm64 x 0)
      | none => some (.addImm64 x 0)
    else none
  | _, _, .and (.bits n), (a, b, ()) =>
    if !Nat.ble n 64 then none else match a, b with
      | .var x, .var y => some (.andVarVar n x y)
      | .var x, .imm c | .imm c, .var x => some (.andVarImm n x (c.setWidth 64))
      | _, _ => none
  | _, _, .sext m n, (.var x, ()) =>
    if Nat.blt 0 m && Nat.blt m n && Nat.ble n 64 then some (.sextVar m n x) else none
  | _, _, .zext m n, (.var x, ()) =>
    if Nat.blt 0 m && Nat.blt m n && Nat.ble n 64 then some (.zextVar m n x) else none
  | _, _, _, _ => none

/-- `recordDef`, except that under `cse` an `x ± c` over a scaled `addrSum` `x` is recorded as
`addImm64 x (±c)` (`recordDef` over empty facts), keeping `x` as the shared base register. -/
def recordDefC (cse : Bool) (defs : Trie DefFact) {sig rs : List Ty} (code : OpCode sig rs)
    (args : Tup (Arg VNat) sig) : Option DefFact :=
  if addrCseHit defs code args && cse then recordDef .empty code args
  else recordDef defs code args

def tupDstFlags {I : Isa} : {ts : List Ty} → Tup (PDst I.Reg I.VReg I.Cond) ts → List I.Cond
  | [], () => [] | _ :: _, (.flag c, ds) => c :: tupDstFlags ds | _ :: _, (_, ds) => tupDstFlags ds

def resolveDsts (I : Isa) (h : I.Hints) :
    (ts : List Ty) → Nat → Option (Tup (PDst I.Reg I.VReg I.Cond) ts)
  | [], _ => some ()
  | t :: ts, nv =>
    match h.dest.find? nv, resolveDsts I h ts (nv + 1) with
    | some (.gpr r), some rest =>
      if isAllocGpr I h.saved r && isGprTy I t then some (.gpr r, rest) else none
    | some (.vec v), some rest =>
      if isAllocVec I v && (vecWidth? I t).isSome then some (.vec v, rest) else none
    | some (.flag c), some rest => match t with | .bool => some (.flag c, rest) | _ => none
    | _, _ => none

def bindDsts (I : Isa) :
    {ts : List Ty} → Tup (PDst I.Reg I.VReg I.Cond) ts → Nat →
    List (SymArg × RegLoc I.Reg I.VReg I.Cond) × Trie SlotWidth →
    List (SymArg × RegLoc I.Reg I.VReg I.Cond) × Trie SlotWidth
  | [], (), _, acc => acc
  | t :: _, (d, ds), nv, (regs, vw) =>
    let (rl, vw') := match d with
      | .gpr r => (RegLoc.gpr r, vw)
      | .vec v => (.vec v, match vecWidth? I t with | some w => vw.insert nv w | none => vw)
      | .flag c => (.flag c, vw)
    bindDsts I ds (nv + 1) ((.var nv, rl) :: regs, vw')

def tryFlag (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (pref : List I.Cond)
    {α : Type} (sa : SymArg) (k : I.Cond → Option α) : Option α :=
  (pref.findSome? fun c =>
    if R.any (fun (sa', rl) => symArgEq sa' sa && regLocEq rl (.flag c)) then k c else none) <|>
  (R.findSome? fun (sa', rl) =>
    match rl with | .flag c => if symArgEq sa' sa then k c else none | _ => none)

def tryGpr (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) {α : Type}
    (sa : SymArg) (k : I.Reg → Option α) : Option α :=
  R.findSome? fun (sa', rl) =>
    match rl with
    | .gpr r | .gprZ r =>
      if !(I.frame.scratch.contains r) && symArgMatchesGpr sa' sa then k r else none
    | _ => none

def tryVec (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) {α : Type}
    (sa : SymArg) (k : I.VReg → Option α) : Option α :=
  R.findSome? fun (sa', rl) =>
    match rl with
    | .vec v => if !(I.vec.vecScratch.contains v) && symArgEq sa' sa then k v else none
    | _ => none

def tryArg (I : Isa) (st : SymState I) (pref : List I.Cond) {α : Type}
    (t : Ty) (a : Arg VNat t) (k : PArg I.Reg I.VReg I.Cond t → Option α) : Option α :=
  match t, a with
  | .bool, .var x =>
    tryFlag I st.regs pref (.var x) (k ∘ .flag) <|> tryGpr I st.regs (.var x) (k ∘ .gpr)
  | .bool, .imm b =>
    tryFlag I st.regs pref (.immBool b) (k ∘ .flag) <|> k (.imm b) <|>
      tryGpr I st.regs (.immBool b) (k ∘ .gpr)
  | .bits _, .var x => tryGpr I st.regs (.var x) (k ∘ .gpr)
  | .bits n, .imm c =>
    k (.imm c) <|>
      if Nat.ble n 64 then tryGpr I st.regs (.immBits n (c.setWidth 64)) (k ∘ .gpr) else none
  | .pair _ _, .var x => tryVec I st.regs (.var x) (k ∘ .vec)
  | .pair a b, .imm c =>
    k (.imm c) <|> match vecWidth? I (.pair a b) with
      | none => none
      | some w =>
        tryVec I st.regs (.immVec w ((toBits (.pair a b) c).setWidth 512)) (k ∘ .vec)
  | .float _, _ => none

def pickPArgs (I : Isa) (st : SymState I) (pref : List I.Cond) {α : Type} :
    {sig : List Ty} → Tup (Arg VNat) sig →
    (Tup (PArg I.Reg I.VReg I.Cond) sig → Option α) → Option α
  | [], (), k => k ()
  | t :: _, (a, as), k =>
    tryArg I st pref t a fun pa => pickPArgs I st pref as fun pas => k (pa, pas)

def hasVarGprZ (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (x : Nat) (rd : I.Reg) : Bool :=
  R.any fun (sa, rl) => symArgEq sa (.var x) && regLocEq rl (.gprZ rd)

/-- `true` when an unsigned/equality `w`-bit compare of `.var x` in canonical `.gprZ rd` may be
lowered at width `64` (`GprIsa.widenZextCmp`). -/
def widenZextCmp? (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (co : CmpOp)
    (w x : Nat) (rd : I.Reg) : Bool :=
  I.gpr.widenZextCmp && Nat.blt w 64 && cmpIsUnsignedOrEq co && hasVarGprZ I R x rd

/-- `.zext m n` of a `.gprZ rd` (or zero-extended 32-bit in `rd`) into the same `rd` is a no-op. -/
def elideZext32? (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (zeroExt : List I.Reg) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig →
    Tup (PDst I.Reg I.VReg I.Cond) ts → Bool
  | _, _, .zext m n, (.var x, ()), (.gpr rd, ()) =>
    Nat.ble n 64 && I.gpr.elideZext32 &&
      (hasVarGprZ I R x rd || (Nat.beq m 32 && zeroExt.contains rd && hasVarGpr I R x rd))
  | _, _, _, _, _ => false

/-- `.trunc m n` of a `.var x` already in `rd` into the same `rd` emits no code, unless
`elideZext32` expects `trunc m 32` to zero upper 32 bits (`zeroUpper32Op`). -/
def elideTrunc? (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig →
    Tup (PDst I.Reg I.VReg I.Cond) ts → Bool
  | _, _, .trunc m n, (.var x, ()), (.gpr rd, ()) =>
    Nat.ble n m && Nat.ble n 64 && hasVarGpr I R x rd &&
      !(I.gpr.elideZext32 && Nat.beq n 32 &&
        I.gpr.zeroUpper32Op (.trunc m n) (.gpr rd, ()) (.gpr rd, ()))
  | _, _, _, _, _ => false

def testBoolExtra? (I : Isa) (neg : Bool) (cl : FlagMask)
    (pd : PDst I.Reg I.VReg I.Cond .bool) : Option I.Cond :=
  if I.gpr.hasTestFlags && !(cl == FlagMask.none) then
    match pd with | .gpr _ => I.gpr.condOfCmp? (if neg then .ne else .eq) | _ => none
  else none

def cmpMemRes (I : Isa) (st : SymState I) (co : CmpOp) (w : Nat) (lhs rhs : SymArg)
    (pd : PDst I.Reg I.VReg I.Cond .bool) (c : List I.Directive) (cl : FlagMask) :
    List I.Directive × FlagMask × Option FlagFact × Option I.Cond :=
  match I.gpr.cmpMemFlagsOut? co pd with
  | some lf =>
    let fl := some (.cmp w (if lf then lhs else rhs) (if lf then rhs else lhs) false)
    let ex := match pd with
      | .gpr _ => I.gpr.condOfCmp? (if lf then co else co.swap)
      | _ => none
    (c, cl, fl, ex)
  | none => (c, cl, killFlags I cl st.flags, none)

def opProducesZ32 (I : Isa) {sig : List Ty} : {rs : List Ty} → OpCode sig rs →
    Tup (PArg I.Reg I.VReg I.Cond) sig → Tup (PDst I.Reg I.VReg I.Cond) rs → Bool
  | [.bits n], code, pas, dsts =>
    Nat.beq n 32 && match dsts with
    | (.gpr _, ()) => I.gpr.zeroUpper32Op code pas dsts
    | _ => false
  | _, _, _, _ => false

def tryAddr (I : Isa) (st : SymState I) (vh : VariantHint) {α : Type}
    (a : Arg VNat i64) (k : AddrArg I.Reg → Option α) : Option α :=
  match a with
  | .imm c =>
    k (.imm c) <|>
      (findGprFor I true st.regs (.immBits 64 c)).bind fun r => k (.baseDisp r 0)
  | .var x =>
    let foldDisp := match vh, st.defs.find? x with
      | .disp off, some (.addImm64 base d) =>
        if d == off.toBitVec then
          (findGprFor I true st.regs (.var base)).bind fun rb => k (.baseDisp rb off)
        else none
      | _, _ => none
    foldDisp <|>
      ((findGprFor I true st.regs (.var x)).bind fun rx => k (.baseDisp rx 0)) <|>
      (match st.defs.find? x with
      | some (.addImm64 base d) =>
        (findGprFor I true st.regs (.var base)).bind fun rb =>
          k (.baseDisp rb (Int64.ofBitVec d))
      | some (.addrSum base idx sh d) =>
        (AddrScale.ofShift? sh).bind fun sc =>
          (findGprFor I true st.regs (.var base)).bind fun rb =>
            (findGprFor I true st.regs (.var idx)).bind fun ri =>
              k (.baseIdxDisp rb ri sc (Int64.ofBitVec d))
      | some (.imm64 c) => k (.imm c)
      | _ => none) <|>
      match addrDefOf I.gpr.addrCse st.defs x with
      | some (.addrSum base idx sh d) =>
        (AddrScale.ofShift? sh).bind fun sc =>
          (findGprFor I true st.regs (.var base)).bind fun rb =>
            (findGprFor I true st.regs (.var idx)).bind fun ri =>
              k (.baseIdxDisp rb ri sc (Int64.ofBitVec d))
      | _ => none

def tryTestMemVar (I : Isa) (st : SymState I) (neg : Bool) (n x : Nat)
    (other : Arg VNat (.bits n)) (pd : PDst I.Reg I.VReg I.Cond .bool) :
    Option (List I.Directive × FlagMask) :=
  match st.memDefs.find? x with
  | some (.bits m, addr) =>
    if Nat.beq m n then
      tryAddr I st .default addr fun aa =>
        tryArg I st [] (.bits n) other fun pb =>
          I.gpr.testMem n neg aa pb pd
    else none
  | _ => none

def tryTestFuse (I : Isa) (st : SymState I) (neg : Bool) (n t : Nat)
    (pd : PDst I.Reg I.VReg I.Cond .bool) : Option (List I.Directive × FlagMask) :=
  match st.defs.find? t with
  | some (.andVarImm w x c) =>
    if !Nat.beq w n then none
    else
      let ci : Arg VNat (.bits n) := .imm (c.setWidth n)
      tryTestMemVar I st neg n x ci pd <|>
        tryArg I st [] (.bits n) (.var x) fun pa =>
          I.gpr.testOp n neg pa (.imm (c.setWidth n)) pd
  | some (.andVarVar w x y) =>
    if !Nat.beq w n then none
    else
      tryTestMemVar I st neg n x (.var y) pd <|>
        tryTestMemVar I st neg n y (.var x) pd <|>
        tryArg I st [] (.bits n) (.var x) fun pa =>
          tryArg I st [] (.bits n) (.var y) fun pb =>
            I.gpr.testOp n neg pa pb pd
  | _ => none

def extCmpMemRes (I : Isa) (co : CmpOp) (pd : PDst I.Reg I.VReg I.Cond .bool)
    (d : List I.Directive) (cl : FlagMask) : List I.Directive × FlagMask × Option I.Cond :=
  let ex := match pd with
    | .gpr _ => (I.gpr.cmpMemFlagsOut? co pd).bind fun lf =>
      I.gpr.condOfCmp? (if lf then co else co.swap)
    | _ => none
  (d, cl, ex)

/-- Lower an unsigned/equality `< 32`-bit compare of `.gprZ` operands at width `32`
(omitting `ubfm #0, #7`/`#15`) when `GprIsa.widenZextCmp` is enabled. -/
def tryWidenZextCmp (I : Isa) (st : SymState I) (vh : VariantHint) (co : CmpOp) (n : Nat)
    (a b : Arg VNat (.bits n)) (pd : PDst I.Reg I.VReg I.Cond .bool) :
    Option (List I.Directive × FlagMask × Option FlagFact × Option I.Cond) :=
  if !(I.gpr.widenZextCmp && Nat.blt n 32 && cmpIsUnsignedOrEq co) then none
  else
    (widenZextArg32 I st.regs a).bind fun pa =>
      (widenZextArg32 I st.regs b).bind fun pb =>
        (I.gpr.op (.cmp co (.bits 32)) (pa, pb, ()) (pd, ()) vh).map fun (d, cl) =>
          let ex := match pd with
            | .gpr _ => (I.gpr.cmpFlagsOut? co 32 pa pb pd).bind fun lf =>
                I.gpr.condOfCmp? (if lf then co else co.swap)
            | _ => none
          (d, cl, killFlags I cl st.flags, ex)

def tryExtCmp (I : Isa) (st : SymState I) (vh : VariantHint) (co : CmpOp) (n t : Nat)
    (c : BitVec n) (pd : PDst I.Reg I.VReg I.Cond .bool) :
    Option (List I.Directive × FlagMask × Option FlagFact × Option I.Cond) :=
  let run {m : Nat} (x : Nat) (cm : BitVec m) :=
    let memTry := match st.memDefs.find? x with
      | some (.bits m', addr) =>
        if Nat.beq m' m then
          tryAddr I st .default addr fun aa =>
            (I.gpr.cmpMem co m aa (.imm cm) pd).map fun (d, cl) =>
              cmpMemRes I st co m (.var x) (.immBits m (cm.setWidth 64)) pd d cl
        else none
      | _ => none
    memTry <|>
      if I.supportsTestFuse then
        tryWidenZextCmp I st vh co m (.var x) (.imm cm) pd <|>
        tryGpr I st.regs (.var x) fun rx =>
          (I.gpr.op (.cmp co (.bits m)) (.gpr rx, .imm cm, ()) (pd, ()) vh).map fun (d, cl) =>
            let lf? := I.gpr.cmpFlagsOut? co m (.gpr rx) (.imm cm) pd
            let immS : SymArg := .immBits m (cm.setWidth 64)
            let fl := match lf? with
              | some lf =>
                some (.cmp m (if lf then .var x else immS) (if lf then immS else .var x) false)
              | none => killFlags I cl st.flags
            let ex := match pd with
              | .gpr _ => lf?.bind fun lf => I.gpr.condOfCmp? (if lf then co else co.swap)
              | _ => none
            (d, cl, fl, ex)
      else none
  match st.defs.find? t with
  | some (.sextVar m n' x) =>
    if !(Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsSignedOrEq co &&
         (c.truncate m).signExtend n == c) then none
    else run x (c.truncate m)
  | some (.zextVar m n' x) =>
    if !(Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsUnsignedOrEq co &&
         (c.truncate m).zeroExtend n == c) then none
    else run x (c.truncate m)
  | _ => none

def tryCmpMemVar (I : Isa) (st : SymState I) (co : CmpOp) (n x : Nat)
    (other : Arg VNat (.bits n)) (pd : PDst I.Reg I.VReg I.Cond .bool) :
    Option (List I.Directive × FlagMask) :=
  match st.memDefs.find? x with
  | some (.bits m, addr) =>
    if Nat.beq m n then
      tryAddr I st .default addr fun aa =>
        tryArg I st [] (.bits n) other fun pb =>
          I.gpr.cmpMem co n aa pb pd
    else none
  | _ => none

def isStdBitWidth (n : Nat) : Bool :=
  Nat.beq n 8 || Nat.beq n 16 || Nat.beq n 32 || Nat.beq n 64

def spAddr (I : Isa) (idx : Nat) : AddrArg I.Reg :=
  .baseDisp I.frame.sp (Int64.ofNat (8 * idx))

def findSlotGprGo (slots : Trie SlotEntry) (x : Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 =>
    match slots.find? i with
    | some (.gpr sas) =>
      if sas.any (symArgEq · (.var x)) then some i else findSlotGprGo slots x (i + 1) fuel
    | some (.gprZ sas) =>
      if sas.any (fun (sa, _) => symArgEq sa (.var x)) then some i
      else findSlotGprGo slots x (i + 1) fuel
    | _ => findSlotGprGo slots x (i + 1) fuel

def findSlotGpr (nslots : Nat) (slots : Trie SlotEntry) (x : Nat) : Option Nat :=
  findSlotGprGo slots x 0 nslots

def tryTestSlot (I : Isa) (h : I.Hints) (st : SymState I) (neg : Bool) (n t : Nat)
    (pd : PDst I.Reg I.VReg I.Cond .bool) : Option (List I.Directive × FlagMask) :=
  if !isStdBitWidth n then none
  else match st.defs.find? t with
    | some (.andVarImm w x c) =>
      if Nat.beq w n then
        (findSlotGpr h.nslots st.slots x).bind fun idx =>
          I.gpr.testMem n neg (spAddr I idx) (.imm (c.setWidth n)) pd
      else none
    | some (.andVarVar w x y) =>
      if Nat.beq w n then
        ((findSlotGpr h.nslots st.slots x).bind fun idx =>
          tryArg I st [] (.bits n) (.var y) fun pb =>
            I.gpr.testMem n neg (spAddr I idx) pb pd) <|>
        ((findSlotGpr h.nslots st.slots y).bind fun idx =>
          tryArg I st [] (.bits n) (.var x) fun pa =>
            I.gpr.testMem n neg (spAddr I idx) pa pd)
      else none
    | _ => none

def tryExtSlot (I : Isa) (h : I.Hints) (st : SymState I) (co : CmpOp) (n t : Nat) (c : BitVec n)
    (pd : PDst I.Reg I.VReg I.Cond .bool) : Option (List I.Directive × FlagMask) :=
  match st.defs.find? t with
  | some (.sextVar m n' x) =>
    if Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsSignedOrEq co &&
        (c.truncate m).signExtend n == c && isStdBitWidth m then
      (findSlotGpr h.nslots st.slots x).bind fun idx =>
        I.gpr.cmpMem co m (spAddr I idx) (.imm (c.truncate m)) pd
    else none
  | some (.zextVar m n' x) =>
    if Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsUnsignedOrEq co &&
        (c.truncate m).zeroExtend n == c && isStdBitWidth m then
      (findSlotGpr h.nslots st.slots x).bind fun idx =>
        I.gpr.cmpMem co m (spAddr I idx) (.imm (c.truncate m)) pd
    else none
  | _ => none

def tryAluSlot (I : Isa) (h : I.Hints) (st : SymState I) (n : Nat)
    (code : OpCode [.bits n, .bits n] [.bits n])
    (a b : Arg VNat (.bits n)) (rd : I.Reg) : Option (List I.Directive × FlagMask × Bool) :=
  if !isStdBitWidth n then none
  else
    let res :=
      (match a with
       | .var x => (findSlotGpr h.nslots st.slots x).bind fun idx =>
         tryArg I st [] (.bits n) b fun pb => I.gpr.aluMem n code false (spAddr I idx) pb rd
       | _ => none) <|>
      (match b with
       | .var y => (findSlotGpr h.nslots st.slots y).bind fun idx =>
         tryArg I st [] (.bits n) a fun pa => I.gpr.aluMem n code true (spAddr I idx) pa rd
       | _ => none)
    res.map fun (c, cl) => (c, cl, Nat.beq n 32 && I.gpr.zeroUpper32AluMem)

def trySlotOp (I : Isa) (h : I.Hints) (st : SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask × Bool × Option FlagFact × Option I.Cond) :=
  match sig, ts, code, args, dsts with
  | _, _, .cmp co (.bits n) .bool _, (a, b, ()), (pd, ()) =>
    if !Nat.ble n 64 then none
    else
      let tFuse :=
        if co == .eq || co == .ne then
          let neg := co == .ne
          let res? := match a, b with
            | .var t, .imm c => if c == 0#n then tryTestSlot I h st neg n t pd else none
            | .imm c, .var t => if c == 0#n then tryTestSlot I h st neg n t pd else none
            | _, _ => none
          res?.map fun (c, cl) => (c, cl, killFlags I cl st.flags, testBoolExtra? I neg cl pd)
        else none
      let eFuse := match a, b with
        | .var t, .imm c =>
          (tryExtSlot I h st co n t c pd).map fun (d, cl) =>
            let (d', cl', ex) := extCmpMemRes I co pd d cl
            (d', cl', killFlags I cl' st.flags, ex)
        | .imm c, .var t =>
          (tryExtSlot I h st co.swap n t c pd).map fun (d, cl) =>
            let (d', cl', ex) := extCmpMemRes I co.swap pd d cl
            (d', cl', killFlags I cl' st.flags, ex)
        | _, _ => none
      let mFuse :=
        if !isStdBitWidth n then none
        else
          (match a with
           | .var x => (findSlotGpr h.nslots st.slots x).bind fun idx =>
             tryArg I st [] (.bits n) b fun pb =>
               (I.gpr.cmpMem co n (spAddr I idx) pb pd).map fun (d, cl) =>
                 match toSymArg I (.bits n) b with
                 | some sb => cmpMemRes I st co n (.var x) sb pd d cl
                 | none => (d, cl, killFlags I cl st.flags, none)
           | _ => none) <|>
          (match b with
           | .var y => (findSlotGpr h.nslots st.slots y).bind fun idx =>
             tryArg I st [] (.bits n) a fun pa =>
               (I.gpr.cmpMem co.swap n (spAddr I idx) pa pd).map fun (d, cl) =>
                 match toSymArg I (.bits n) a with
                 | some sa => cmpMemRes I st co.swap n (.var y) sa pd d cl
                 | none => (d, cl, killFlags I cl st.flags, none)
           | _ => none)
      (tFuse <|> eFuse <|> mFuse).map fun (c, cl, fl, ex) => (c, cl, false, fl, ex)
  | _, _, .add (.bits n), (a, b, ()), (.gpr rd, ()) =>
    (tryAluSlot I h st n (.add (.bits n)) a b rd).map fun (c, cl, z32) =>
      (c, cl, z32, killFlags I cl st.flags, none)
  | _, _, .sub (.bits n), (a, b, ()), (.gpr rd, ()) =>
    (tryAluSlot I h st n (.sub (.bits n)) a b rd).map fun (c, cl, z32) =>
      (c, cl, z32, killFlags I cl st.flags, none)
  | _, _, .mul (.bits n), (a, b, ()), (.gpr rd, ()) =>
    (tryAluSlot I h st n (.mul (.bits n)) a b rd).map fun (c, cl, z32) =>
      (c, cl, z32, killFlags I cl st.flags, none)
  | _, _, .and (.bits n), (a, b, ()), (.gpr rd, ()) =>
    (tryAluSlot I h st n (.and (.bits n)) a b rd).map fun (c, cl, z32) =>
      (c, cl, z32, killFlags I cl st.flags, none)
  | _, _, .or  (.bits n), (a, b, ()), (.gpr rd, ()) =>
    (tryAluSlot I h st n (.or (.bits n)) a b rd).map fun (c, cl, z32) =>
      (c, cl, z32, killFlags I cl st.flags, none)
  | _, _, .xor (.bits n), (a, b, ()), (.gpr rd, ()) =>
    (tryAluSlot I h st n (.xor (.bits n)) a b rd).map fun (c, cl, z32) =>
      (c, cl, z32, killFlags I cl st.flags, none)
  | _, _, _, _, _ => none

def tryFuseCmp (I : Isa) (st : SymState I) (vh : VariantHint) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask × Option FlagFact × Option I.Cond) :=
  match sig, ts, code, args, dsts with
  | _, _, .cmp co (.bits n) .bool _, (a, b, ()), (pd, ()) =>
    if !Nat.ble n 64 then none
    else
      let tFuse :=
        if co == .eq || co == .ne then
          let neg := co == .ne
          let res? := match a, b with
            | .var t, .imm c => if c == 0#n then tryTestFuse I st neg n t pd else none
            | .imm c, .var t => if c == 0#n then tryTestFuse I st neg n t pd else none
            | _, _ => none
          res?.map fun (c, cl) => (c, cl, killFlags I cl st.flags, testBoolExtra? I neg cl pd)
        else none
      let eFuse := match a, b with
        | .var t, .imm c => tryExtCmp I st vh co n t c pd
        | .imm c, .var t => tryExtCmp I st vh co.swap n t c pd
        | _, _ => none
      let mFuse :=
        (match a with
         | .var x => (tryCmpMemVar I st co n x b pd).map fun (c, cl) =>
           match toSymArg I (.bits n) b with
           | some sb => cmpMemRes I st co n (.var x) sb pd c cl
           | none => (c, cl, killFlags I cl st.flags, none)
         | _ => none) <|>
        (match b with
         | .var y => (tryCmpMemVar I st co.swap n y a pd).map fun (c, cl) =>
           match toSymArg I (.bits n) a with
           | some sa => cmpMemRes I st co.swap n (.var y) sa pd c cl
           | none => (c, cl, killFlags I cl st.flags, none)
         | _ => none)
      let sFuse := match a, b with
        | .var x, .var y =>
          (shiftCmpGo I st co n x y pd).map fun (d, cl, lhsShift) =>
            let lf? := I.gpr.shiftCmpFlagsOut? co n lhsShift pd
            let fl := match lf? with
              | some lf =>
                some (.cmp n (if lf then .var x else .var y)
                  (if lf then .var y else .var x) false)
              | none => killFlags I cl st.flags
            let ex := match pd with
              | .gpr _ => lf?.bind fun lf => I.gpr.condOfCmp? (if lf then co else co.swap)
              | _ => none
            (d, cl, fl, ex)
        | _, _ => none
      let wFuse := tryWidenZextCmp I st vh co n a b pd
      tFuse <|> eFuse <|> mFuse <|> sFuse <|> wFuse
  | _, _, _, _, _ => none

/-- Fused `sext m n` of an elided `load (.bits m)` (`memDefs`) into one sign-extending load. -/
def tryLoadSext (I : Isa) (st : SymState I) (vh : VariantHint) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask) :=
  match sig, ts, code, args, dsts with
  | _, _, .sext m n, (.var x, ()), (.gpr rd, ()) =>
    match st.memDefs.find? x with
    | some (.bits m', addr) =>
      if Nat.beq m' m && Nat.ble n 64 then
        tryAddr I st vh addr (I.gpr.loadSext m n rd) <|>
          tryAddrZext I st addr (I.gpr.loadSextZextIdx m n rd)
      else none
    | _ => none
  | _, _, _, _, _ => none

def recordBoolDef (defs : Trie DefFact) {sig ts : List Ty} (code : OpCode sig ts)
    (args : Tup (Arg VNat) sig) : Option DefFact :=
  match sig, ts, code, args with
  | _, _, .cmp co (.bits n) .bool _, (a, b, ()) =>
    if !Nat.ble n 64 then none
    else
      let pair? := match a, b with
        | .var t, .imm c =>
          let (co0, c0) := normCmpZero1 co c
          if c0 == 0#n then some (co0, t) else none
        | .imm c, .var t =>
          let (co0, c0) := normCmpZero1 co.swap c
          if c0 == 0#n then some (co0, t) else none
        | _, _ => none
      pair?.map fun (co0, t) =>
        match defs.find? t with
        | some (.andVarImm w x mask) =>
          if (co0 == .eq || co0 == .ne) && Nat.beq w n then
            .testBitVar (co0 == .ne) w x mask
          else .cmpZeroVar co0 n t
        | some (.sextVar m n' x) =>
          if Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsSignedOrEq co0 then
            .cmpZeroVar co0 m x
          else .cmpZeroVar co0 n t
        | some (.zextVar m n' x) =>
          if Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsUnsignedOrEq co0 then
            .cmpZeroVar co0 m x
          else .cmpZeroVar co0 n t
        | _ => .cmpZeroVar co0 n t
  | _, _, _, _ => none

def extractLea64 (defs : Trie DefFact) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig →
    Option (Option Nat × Nat × AddrScale × Int64)
  | _, _, .add (.bits 64), (.var x, .imm c, ())
  | _, _, .add (.bits 64), (.imm c, .var x, ()) =>
    match defs.find? x with
    | some (.addrSum b idx 0 d) => some (some b, idx, .s1, Int64.ofBitVec (d + c))
    | _ =>
      match recordDef defs (.add (.bits 64)) (.var x, .imm c, ()) with
      | some (.scaleOff idx sh disp) =>
        if Nat.beq sh 0 then none
        else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
      | some (.addrSum b idx sh disp) =>
        if Nat.beq sh 0 && disp == 0#64 then none
        else (AddrScale.ofShift? sh).map fun sc => (some b, idx, sc, Int64.ofBitVec disp)
      | _ => none
  | _, _, .sub (.bits 64), (.var x, .imm c, ()) =>
    match defs.find? x with
    | some (.addrSum b idx 0 d) => some (some b, idx, .s1, Int64.ofBitVec (d - c))
    | _ =>
      match recordDef defs (.sub (.bits 64)) (.var x, .imm c, ()) with
      | some (.scaleOff idx sh disp) =>
        if Nat.beq sh 0 then none
        else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
      | some (.addrSum b idx sh disp) =>
        if Nat.beq sh 0 && disp == 0#64 then none
        else (AddrScale.ofShift? sh).map fun sc => (some b, idx, sc, Int64.ofBitVec disp)
      | _ => none
  | _, _, .add (.bits 64), (.var x, .var y, ()) =>
    match recordDef defs (.add (.bits 64)) (.var x, .var y, ()) with
    | some (.scaleOff idx sh disp) =>
      if Nat.beq sh 0 then none
      else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
    | some (.addrSum b idx sh disp) =>
      if Nat.beq sh 0 && disp == 0#64 then none
      else (AddrScale.ofShift? sh).map fun sc => (some b, idx, sc, Int64.ofBitVec disp)
    | _ => none
  | _, _, .shl (.bits 64), (.var x, .imm k, ()) =>
    let shlOk := match defs.find? x with
      | some (.addImm64 _ _) | some (.scaleOff _ _ _) => true
      | _ => false
    if !shlOk then none
    else
      match recordDef defs (.shl (.bits 64)) (.var x, .imm k, ()) with
      | some (.scaleOff idx sh disp) =>
        if Nat.beq sh 0 then none
        else (AddrScale.ofShift? sh).map fun sc => (none, idx, sc, Int64.ofBitVec disp)
      | _ => none
  | _, _, _, _ => none

def asScale32 (defs : Trie DefFact) (v : Nat) : Option (Nat × AddrScale × BitVec 32) :=
  let ofShl (idx sh : Nat) (disp : BitVec 32) : Option (Nat × AddrScale × BitVec 32) :=
    if Nat.beq sh 0 then none
    else (AddrScale.ofShift? sh).map (idx, ·, disp)
  match defs.find? v with
  | some (.shlVarImm 32 idx sh) => ofShl idx sh 0#32
  | some (.binVarImm 32 .add x c) =>
    match defs.find? x with
    | some (.shlVarImm 32 idx sh) => ofShl idx sh (c.setWidth 32)
    | _ => none
  | some (.binVarImm 32 .sub x c) =>
    match defs.find? x with
    | some (.shlVarImm 32 idx sh) => ofShl idx sh (-(c.setWidth 32))
    | _ => none
  | _ => none

def asBaseImm32 (defs : Trie DefFact) (v : Nat) : Nat × BitVec 32 :=
  match defs.find? v with
  | some (.binVarImm 32 .add x c) => (x, c.setWidth 32)
  | some (.binVarImm 32 .sub x c) => (x, -(c.setWidth 32))
  | _ => (v, 0#32)

def extractLea32 (defs : Trie DefFact) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig →
    Option (Option Nat × Nat × AddrScale × Int64)
  | _, _, .add (.bits 32), (.var x, .imm c, ())
  | _, _, .add (.bits 32), (.imm c, .var x, ()) =>
    match asScale32 defs x with
    | some (idx, sc, d) => some (none, idx, sc, Int64.ofBitVec ((d + c).signExtend 64))
    | none =>
      match defs.find? x with
      | some (.binVarVar 32 .add a b) =>
        match asScale32 defs a with
        | some (idx, sc, d) =>
          let (rb, d2) := asBaseImm32 defs b
          some (some rb, idx, sc, Int64.ofBitVec ((d + d2 + c).signExtend 64))
        | none =>
          match asScale32 defs b with
          | some (idx, sc, d) =>
            let (rb, d2) := asBaseImm32 defs a
            some (some rb, idx, sc, Int64.ofBitVec ((d + d2 + c).signExtend 64))
          | none =>
            let (ra, da) := asBaseImm32 defs a
            let (rb, db) := asBaseImm32 defs b
            some (some ra, rb, .s1, Int64.ofBitVec ((da + db + c).signExtend 64))
      | _ => none
  | _, _, .sub (.bits 32), (.var x, .imm c, ()) =>
    match asScale32 defs x with
    | some (idx, sc, d) => some (none, idx, sc, Int64.ofBitVec ((d - c).signExtend 64))
    | none =>
      match defs.find? x with
      | some (.binVarVar 32 .add a b) =>
        match asScale32 defs a with
        | some (idx, sc, d) =>
          let (rb, d2) := asBaseImm32 defs b
          some (some rb, idx, sc, Int64.ofBitVec ((d + d2 - c).signExtend 64))
        | none =>
          match asScale32 defs b with
          | some (idx, sc, d) =>
            let (rb, d2) := asBaseImm32 defs a
            some (some rb, idx, sc, Int64.ofBitVec ((d + d2 - c).signExtend 64))
          | none =>
            let (ra, da) := asBaseImm32 defs a
            let (rb, db) := asBaseImm32 defs b
            some (some ra, rb, .s1, Int64.ofBitVec ((da + db - c).signExtend 64))
      | _ => none
  | _, _, .add (.bits 32), (.var x, .var y, ()) =>
    match asScale32 defs x with
    | some (idx, sc, d1) =>
      let (rb, d2) := asBaseImm32 defs y
      some (some rb, idx, sc, Int64.ofBitVec ((d1 + d2).signExtend 64))
    | none =>
      match asScale32 defs y with
      | some (idx, sc, d1) =>
        let (rb, d2) := asBaseImm32 defs x
        some (some rb, idx, sc, Int64.ofBitVec ((d1 + d2).signExtend 64))
      | none =>
        let (rx, dx) := asBaseImm32 defs x
        let (ry, dy) := asBaseImm32 defs y
        if dx == 0#32 && dy == 0#32 then none
        else some (some rx, ry, .s1, Int64.ofBitVec ((dx + dy).signExtend 64))
  | _, _, .shl (.bits 32), (.var x, .imm k, ()) =>
    let kn := k.toNat
    if !Nat.blt kn 32 then none
    else
      match defs.find? x with
      | some (.binVarImm 32 .add b d) =>
        if Nat.beq kn 0 then none
        else (AddrScale.ofShift? kn).map fun sc =>
          (none, b, sc, Int64.ofBitVec (((d.setWidth 32) <<< kn).signExtend 64))
      | some (.binVarImm 32 .sub b d) =>
        if Nat.beq kn 0 then none
        else (AddrScale.ofShift? kn).map fun sc =>
          (none, b, sc, Int64.ofBitVec (((-(d.setWidth 32)) <<< kn).signExtend 64))
      | some (.shlVarImm 32 idx sh) =>
        if Nat.beq (sh + kn) 0 then none
        else (AddrScale.ofShift? (sh + kn)).map fun sc => (none, idx, sc, 0)
      | _ => none
  | _, _, _, _ => none

def tryLeaArith (I : Isa) (st : SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) : Option (List I.Directive × FlagMask × Bool) :=
  match ts, dsts with
  | [.bits w], (.gpr rd, ()) =>
    let ext? :=
      if Nat.beq w 64 then extractLea64 st.defs code args
      else if Nat.beq w 32 then extractLea32 st.defs code args
      else none
    (ext?.bind (fun (base?, idx, sc, disp) =>
      let rbOpt? : Option (Option I.Reg) := match base? with
        | some b => (findGprFor I true st.regs (.var b)).map some
        | none => some none
      rbOpt?.bind fun rb? =>
        (findGprFor I true st.regs (.var idx)).bind fun ri =>
          (I.gpr.leaArith w rb? ri sc disp rd).map fun (c, cl) =>
            (c, cl, Nat.beq w 32 && I.gpr.zeroUpper32LeaArith)) <|>
    tryLeaArithZext I st code args (ts := [.bits w]) (.gpr rd, ())) <|>
    tryShiftAlu I st w code args rd
  | _, _ => none

def normCmpOp {I : Isa} : {ts : List Ty} → Op VNat ts →
    Tup (PDst I.Reg I.VReg I.Cond) ts → Op VNat ts
  | [.bool], op, dsts =>
    let { sig := _, code, args } := op
    match code, args, dsts with
    | .cmp co (.bits n) .bool hpf, (a, b, ()), (pd, ()) =>
      let (co', a', b') := normCmpExpr co n a b
      let ok := match pd with
        | .gpr _ => true
        | .flag cd => I.gpr.condOfCmp? co' == some cd
        | .vec _ => false
      if ok then { code := .cmp co' (.bits n) .bool hpf, args := (a', b', ()) } else op
    | _, _, _ => op
  | _, op, _ => op

def cmpOpFlags? (I : Isa) (st : SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (pas : Tup (PArg I.Reg I.VReg I.Cond) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts)
    (nv : Nat) (cl : FlagMask) : Option FlagFact × Option I.Cond :=
  match ts, dsts, code, args, pas with
  | [.bool], (pd, ()), .cmp co (.bits w) .bool _, (a, b, ()), (pa, pb, ()) =>
    let fl := if Nat.ble w 64 then
      match I.gpr.cmpFlagsOut? co w pa pb pd, toSymArg I (.bits w) a, toSymArg I (.bits w) b with
      | some lf, some sa, some sb =>
        some (.cmp w (if lf then sa else sb) (if lf then sb else sa) false)
      | _, _, _ => killFlags I cl st.flags
      else killFlags I cl st.flags
    let ex := match pd with
      | .gpr _ =>
        if Nat.ble w 64 then
          (I.gpr.cmpFlagsOut? co w pa pb pd).bind fun lf =>
            I.gpr.condOfCmp? (if lf then co else co.swap)
        else none
      | _ => none
    (fl, ex)
  | [.bool], (.gpr rd, ()), c, _, ps =>
    (killFlags I cl st.flags, I.gpr.boolFlagOut? c ps (.gpr rd))
  | [.bits w], (pd, ()), c, _, _ =>
    let fl := if Nat.ble w 64 && !(cl == FlagMask.none) then
      match I.gpr.aluZeroOut? w c pd with
      | some eqNe => some (.cmp w (.var nv) (.immBits w 0#64) eqNe)
      | none => killFlags I cl st.flags
      else killFlags I cl st.flags
    (fl, none)
  | _, _, _, _, _ => (killFlags I cl st.flags, none)

def tryReuseFlagCmp (I : Isa) (st : SymState I) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask × Option FlagFact × Option I.Cond) :=
  match st.flags, sig, ts, code, args, dsts with
  | some (.cmp w lhs rhs eqNe), _, _, .cmp co (.bits n) .bool _, (a, b, ()), (pd, ()) =>
    (reuseCmpPair? I st.defs w lhs rhs n co a b).bind fun (coBase, sa, sb) =>
      let coUsed? :=
        if symArgEq sa lhs && symArgEq sb rhs then some coBase
        else if symArgEq sa rhs && symArgEq sb lhs then some coBase.swap
        else none
      coUsed?.bind fun coUsed =>
        if !(!eqNe || coUsed == .eq || coUsed == .ne) then none
        else
          (I.gpr.condOfCmp? coUsed).bind fun cc =>
            match pd with
            | .flag cd =>
              if cd == cc then
                some ([], FlagMask.none, some (.cmp w lhs rhs eqNe), none)
              else none
            | .gpr rd =>
              (I.gpr.op (.copy .bool) (.flag cc, ()) (.gpr rd, ()) .default).map fun (c, cl) =>
                (c, cl, killFlags I cl (some (.cmp w lhs rhs eqNe)),
                  if FlagMask.disjoint (I.gpr.condReads cc) cl then some cc else none)
            | .vec _ => none
  | _, _, _, _, _, _ => none

def lowerOpBody (I : Isa) (h : I.Hints) (nv ip : Nat) (st1 : SymState I) {ts : List Ty}
    (op : Op VNat ts) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × SymState I) :=
  let vh := h.variant.getD ip .default
  let dstGprs := tupDstGprs dsts; let dstVecs := tupDstVecs dsts
  let df? := recordDefC I.gpr.addrCse st1.defs op.code op.args
  let defs1 := match df? with
    | some df => st1.defs.insert nv df
    | none => st1.defs
  if elideZext32? I st1.regs st1.zeroExt32 op.code op.args dsts then
    -- no code: every register fact survives and the result shares `rd` canonically
    let regs1 := match ts, dsts with
      | [_], (.gpr rd, ()) => (.var nv, RegLoc.gprZ rd) :: st1.regs
      | _, _ => st1.regs
    some ([], { st1 with regs := regs1, defs := defs1 })
  else if elideTrunc? I st1.regs op.code op.args dsts then
    let regs1 := match ts, dsts with
      | [_], (.gpr rd, ()) => (.var nv, RegLoc.gpr rd) :: st1.regs
      | _, _ => st1.regs
    some ([], { st1 with regs := regs1, defs := defs1 })
  else
    let opN := normCmpOp (I := I) op dsts
    ((((tryReuseFlagCmp I st1 op.code op.args dsts <|>
        tryReuseFlagCmp I st1 opN.code opN.args dsts).map fun (c, cl, fl, ex) =>
      (c, cl, false, false, fl, ex)) <|>
    ((tryFuseCmp I st1 vh opN.code opN.args dsts).map fun (c, cl, fl, ex) =>
      (c, cl, false, false, fl, ex)) <|>
    ((tryLoadSext I st1 vh opN.code opN.args dsts).map fun (c, cl) =>
      (c, cl, false, false, killFlags I cl st1.flags, none)) <|>
    ((tryLeaArith I st1 opN.code opN.args dsts).map fun (c, cl, z32) =>
      (c, cl, false, z32, killFlags I cl st1.flags, none)) <|>
    ((tryMoviZero I h ip st1 opN.code opN.args dsts).map fun (c, cl, z32) =>
      (c, cl, false, z32, killFlags I cl st1.flags, none)) <|>
    (pickPArgs I st1 (tupDstFlags dsts) opN.args fun pas =>
      if dstVecs.isEmpty && (tupArgVecs pas).isEmpty then
        ((I.gpr.op opN.code pas dsts vh).map fun (c, cl) =>
          let (fl, ex) := cmpOpFlags? I st1 opN.code opN.args pas dsts nv cl
          (c, cl, false, opProducesZ32 I opN.code pas dsts, fl, ex)) <|>
        ((I.vec.vop opN.code pas dsts vh).map fun (c, cl) =>
          (c, cl, true, false, killFlags I cl st1.flags, none))
      else (I.vec.vop opN.code pas dsts vh).map fun (c, cl) =>
        (c, cl, true, false, killFlags I cl st1.flags, none)) <|>
    ((tryRematDirect I st1 df? dsts).map fun (c, cl) =>
      (c, cl, false, false, killFlags I cl st1.flags, none)) <|>
    ((tryRematCmpEqImm I st1 vh opN.code opN.args dsts).map fun (c, cl) =>
      (c, cl, false, false, killFlags I cl st1.flags, none)) <|>
    ((tryRematAdd64SameDst I st1 opN.code opN.args dsts).map fun (c, cl) =>
      (c, cl, false, false, killFlags I cl st1.flags, none)) <|>
    ((trySlotOp I h st1 opN.code opN.args dsts).map fun (c, cl, z32, fl, ex) =>
      (c, cl, false, z32, fl, ex))) :
      Option (List I.Directive × FlagMask × Bool × Bool × Option FlagFact × Option I.Cond)).map
      fun (code, clob, isVec, z32, flagsPost, extraBool?) =>
      let vClob := if isVec then dstVecs ++ I.vec.vecScratch else []
      let gClob := dstGprs ++ I.frame.scratch
      let killed := killRegs I gClob vClob clob st1.regs
      let zExt := killZeroExt gClob st1.zeroExt32
      let (regsBase, vw1, zExt1) :=
        if z32 then
          match ts, dsts with
          | [.bits 32], (.gpr rd, ()) =>
            ((.var nv, RegLoc.gprZ rd) :: killed, st1.vecWidths, rd :: zExt)
          | _, _ =>
            let (r, v) := bindDsts I dsts nv (killed, st1.vecWidths)
            (r, v, zExt)
        else
          let (r, v) := bindDsts I dsts nv (killed, st1.vecWidths)
          (r, v, zExt)
      let regs1 := match ts, extraBool? with
        | [.bool], some cc => (.var nv, RegLoc.flag cc) :: regsBase
        | _, _ => regsBase
      (code, { st1 with
        regs := regs1, defs := defs1, vecWidths := vw1, zeroExt32 := zExt1,
        flags := flagsPost })

def lowerOp (I : Isa) (h : I.Hints) (nv ip : Nat) (st1 : SymState I) {ts : List Ty}
    (op : Op VNat ts) (deferFuse : Bool := false) : Option (List I.Directive × SymState I) :=
  if deferFuse then
    ((recordBoolDef st1.defs op.code op.args).map fun df =>
      ([], { st1 with defs := st1.defs.insert nv df })) <|>
    ((recordDefC I.gpr.addrCse st1.defs op.code op.args).map fun df =>
      ([], { st1 with defs := st1.defs.insert nv df }))
  else if h.elide.getD ip false then
    match recordDefC I.gpr.addrCse st1.defs op.code op.args with
    | some df => some ([], { st1 with defs := st1.defs.insert nv df })
    | none => none
  else
    (resolveDsts I h ts nv).bind fun dsts =>
      lowerOpBody I h nv ip st1 op dsts <|>
        (findMissingRematArg I st1 op.args).bind fun (x, _, disp, rb) =>
          (rematTempCands I h.saved st1 dsts).findSome? fun tmp =>
            (rematAddImm64 I rb tmp disp).bind fun cPre =>
              let clob := tmp :: I.frame.scratch
              let stTmp := { st1 with
                regs := (.var x, .gpr tmp) :: killRegs I clob [] FlagMask.none st1.regs
                zeroExt32 := killZeroExt clob st1.zeroExt32 }
              (lowerOpBody I h nv ip stTmp op dsts).map fun (cOp, st2) =>
                (cPre ++ cOp, st2)

/-! ## Block Entry, Jumps, and Core PHOAS Lowering -/

def buildEntryBase (I : Isa) (nslots : Nat) (vw : Trie SlotWidth) :
    List (SymArg × I.Loc) → SymState I → Option (SymState I)
  | [], st => some st
  | (sa, .gpr r) :: rest, st =>
    if !(I.frame.scratch.contains r) then
      buildEntryBase I nslots vw rest { st with regs := (sa, .gpr r) :: st.regs }
    else none
  | (sa, .vec v) :: rest, st =>
    if !(I.vec.vecScratch.contains v) && (symArgWidth vw sa).isSome then
      buildEntryBase I nslots vw rest { st with regs := (sa, .vec v) :: st.regs } else none
  | (sa, .flag c) :: rest, st =>
    buildEntryBase I nslots vw rest { st with regs := (sa, .flag c) :: st.regs }
  | (sa, .slot i w) :: rest, st =>
    if !Nat.ble (i + w.slots) nslots then none
    else (addSlotEntry vw sa i w st.slots).bind fun slots' =>
      buildEntryBase I nslots vw rest { st with slots := slots' }

def bindBlockParams (I : Isa) (nslots : Nat) :
    (ts : List Ty) → List I.Loc → Nat → SymState I → Option (SymState I)
  | [], [], _, st => some st
  | t :: ts, loc :: locs, nv, st =>
    match loc with
    | .gpr r =>
      if !(I.frame.scratch.contains r) && isGprTy I t then
        bindBlockParams I nslots ts locs (nv + 1) { st with regs := (.var nv, .gpr r) :: st.regs }
      else none
    | .vec v => (vecWidth? I t).bind fun w =>
      if !(I.vec.vecScratch.contains v) then
        bindBlockParams I nslots ts locs (nv + 1)
          { st with regs := (.var nv, .vec v) :: st.regs, vecWidths := st.vecWidths.insert nv w }
      else none
    | .flag c => match t with
      | .bool =>
        bindBlockParams I nslots ts locs (nv + 1) { st with regs := (.var nv, .flag c) :: st.regs }
      | _ => none
    | .slot i w =>
      if !(Nat.ble (i + w.slots) nslots && (isGprTy I t || (vecWidth? I t).isSome)) then none
      else
        let vw' := match vecWidth? I t with
          | some wt => st.vecWidths.insert nv wt | none => st.vecWidths
        (addSlotEntry vw' (.var nv) i w st.slots).bind fun slots' =>
          bindBlockParams I nslots ts locs (nv + 1) { st with slots := slots', vecWidths := vw' }
  | _, _, _, _ => none

def bindAbiParams (I : Isa) :
    {ts : List Ty} → Tup (AbiReg I.Reg I.VReg) ts → Nat → SymState I → Option (SymState I)
  | [], (), _, st => some st
  | t :: _, (.gpr r, locs), nv, st =>
    if isGprTy I t then
      let zExt := if tyEq t (.bits 32) then r :: killZeroExt [r] st.zeroExt32 else st.zeroExt32
      bindAbiParams I locs (nv + 1)
        { st with regs := (.var nv, .gprZ r) :: st.regs, zeroExt32 := zExt }
    else none
  | t :: _, (.vec v, locs), nv, st => (vecWidth? I t).bind fun w =>
    bindAbiParams I locs (nv + 1)
      { st with regs := (.var nv, .vec v) :: st.regs, vecWidths := st.vecWidths.insert nv w }

def jumpTargets (I : Isa) :
    {ts : List Ty} → Tup (Arg VNat) ts → List I.Loc → Option (List (SymArg × I.Loc))
  | [], (), [] => some []
  | t :: _, (a, as), loc :: locs =>
    match toSymArg I t a, jumpTargets I as locs with
    | some sa, some rest => some ((sa, loc) :: rest)
    | _, _ => none
  | _, _, _ => none

def jumpLocOk (I : Isa) (nslots : Nat) : I.Loc → Bool
  | .gpr r => !(I.frame.scratch.contains r) | .vec v => !(I.vec.vecScratch.contains v)
  | .flag _ => true | .slot i w => Nat.ble (i + w.slots) nslots

def afterCallState (I : Isa) (saved : List I.Reg) (st : SymState I) : SymState I :=
  { st with
    regs := st.regs.filter fun (_, rl) =>
      match rl with | .gpr r | .gprZ r => saved.contains r | _ => false,
    memDefs := .empty,
    zeroExt32 := st.zeroExt32.filter saved.contains,
    flags := none }
def calleeAllowed (E : Ext) (f : Sym) (as bs : List Ty) : Bool :=
  E.callees.any fun (g, gas, gbs) => g == f && listTyEq gas as && listTyEq gbs bs
def prepend {I : Isa} (pre : List I.Directive) : Res I → Res I
  | .ok (c, nv, nl, ip) => .ok (pre ++ c, nv, nl, ip) | .error e => .error e
/-- Condition representation for `jnz`: flag, GPR, stack slot, or deferred compare/bit-test fusion.
-/
inductive JnzCond (I : Isa) where
  | flag (c : I.Cond)
  | gpr (r : I.Reg)
  | slot (idx : Nat)
  | cmpZero (co : CmpOp) (w : Nat) (r : I.Reg)
  | cmpZeroMem (co : CmpOp) (w x : Nat) (a : AddrArg I.Reg) (cc : I.Cond)
  | cmpZeroFlag (co : CmpOp) (w x : Nat) (r : I.Reg) (cc : I.Cond)
  | testImm (neg : Bool) (w : Nat) (r : I.Reg) (mask : BitVec w)

def findJnzCond (I : Isa) (nslots : Nat) (st : SymState I) (x : Nat) : Option (JnzCond I) :=
  (findFlagFor I st.regs (.var x)).map .flag <|>
    (match st.defs.find? x with
     | some (.cmpZeroVar co w y) => (cmpZeroFlagCond? I st.defs st.flags co w y).map .flag
     | _ => none) <|>
    (findGprFor I true st.regs (.var x)).map .gpr <|>
    (match st.defs.find? x with
     | some (.cmpZeroVar co w y) =>
       (match st.memDefs.find? y with
        | some (.bits m, addr) =>
          if Nat.beq m w && isStdBitWidth w then
            (I.gpr.condOfCmp? co).bind fun cc =>
              tryAddr I st .default addr fun aa =>
                (I.gpr.cmpMem co w aa (.imm 0#w) (.flag cc)).map fun _ => .cmpZeroMem co w y aa cc
          else none
        | _ => none) <|>
       (findGprFor I true st.regs (.var y)).bind fun r =>
         if widenZextCmp? I st.regs co w y r &&
             (I.gpr.cmpZeroJcc co 64 r (lname "" 0)).isSome then some (.cmpZero co 64 r)
         else if (I.gpr.cmpZeroJcc co w r (lname "" 0)).isSome then some (.cmpZero co w r)
         else if isStdBitWidth w then
           (I.gpr.condOfCmp? co).bind fun cc =>
             (I.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ()) (.flag cc, ()) .default).map
               fun _ => .cmpZeroFlag co w y r cc
         else none
     | some (.testBitVar neg w y c) =>
       (findGprFor I true st.regs (.var y)).map fun r => .testImm neg w r (c.setWidth w)
     | _ => none) <|>
    (findSlotGpr nslots st.slots x).map .slot

/-- `true` when `h.pre` at `ip` emits no moves or flag clears. -/
def preEmpty {I : Isa} (h : I.Hints) (ip : Nat) : Bool :=
  match h.pre.find? ip with
  | none => true
  | some ps => !ps.clearFlags && ps.moves.isEmpty

def zeroMoveJump? {rs : List Ty} (I : Isa) (h : I.Hints) (ip : Nat) (st : SymState I) :
    Expr VNat LNat rs → Option Nat
  | .jump j args =>
    if !preEmpty h ip then none
    else (h.entry.find? j).bind fun en => (jumpTargets I args en.ploc).bind fun argTgts =>
      if (en.live ++ argTgts).all
          (fun (sa, loc) => jumpLocOk I h.nslots loc && holdsLoc I st sa loc) then
        some j
      else none
  | _ => none

def tgtLab (fwd : Trie Nat) (j : Nat) : Nat := fwd.getD j j

def firstNonFwd {rs : List Ty} (fwd : Trie Nat) :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig → Nat → Option Nat → Option Nat
  | _, .nil, _, ft => ft
  | _, .cons _ bs, lid, ft =>
    if (fwd.find? lid).isSome then firstNonFwd fwd bs (lid + 1) ft else some lid

def jnzMode {rs : List Ty} (I : Isa) (h : I.Hints) (ipT ipE : Nat) (st : SymState I)
    (canInv : Bool) (t e : Expr VNat LNat rs) (ft : Option Nat)
    (fwd : Trie Nat := .empty) : Bool × Option Nat :=
  match zeroMoveJump? I h ipT st t, if canInv then zeroMoveJump? I h ipE st e else none with
  | some jt, some je => if ft == some (tgtLab fwd jt) then (true, some je) else (false, some jt)
  | some jt, none => (false, some jt)
  | none, some je => (true, some je)
  | none, none => (canInv && h.invertJnz.getD (ipE - 1) false, none)

def gprThread? {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (ipT : Nat) (st1 : SymState I)
    (r : I.Reg) (arm : Expr VNat LNat rs) (fwd : Trie Nat := .empty) : Option Nat :=
  match arm with
  | .jump j args =>
    let cl := (I.gpr.jnzGpr r (lname fn (tgtLab fwd j))).2
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] cl st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
      flags := killFlags I cl st1.flags }
    zeroMoveJump? (rs := rs) I h ipT stB (.jump j args)
  | _ => none

def threadFusedArm {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (ipA : Nat)
    (st1 : SymState I) (emit : Sym → Option (List I.Directive × FlagMask))
    (arm : Expr VNat LNat rs) (fwd : Trie Nat := .empty) :
    Option (Nat × List I.Directive × SymState I) :=
  match arm with
  | .jump j _ =>
    (emit (lname fn (tgtLab fwd j))).bind fun (br, cl) =>
      let stB := { st1 with
        regs := killRegs I I.frame.scratch [] cl st1.regs
        zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
        flags := killFlags I cl st1.flags }
      if zeroMoveJump? I h ipA stB arm == some j then some (j, br, stB) else none
  | _ => none

def fuseJnzChoice {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : SymState I) (t e : Expr VNat LNat rs) (ft : Option Nat)
    (emit : Bool → Sym → Option (List I.Directive × FlagMask))
    (fwd : Trie Nat := .empty) :
    Option (Bool × Option Nat × List I.Directive × SymState I) :=
  let invChoice := h.invertJnz.getD (ipE - 1) false
  (emit invChoice (lname fn nl)).map fun (brNl, clNl) =>
    let stNl := { st1 with
      regs := killRegs I I.frame.scratch [] clNl st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
      flags := killFlags I clNl st1.flags }
    let fwd? := threadFusedArm I h fn ipT st1 (emit false) t fwd
    let inv? := threadFusedArm I h fn ipE st1 (emit true) e fwd
    match fwd?, inv? with
    | some (jt, brF, stF), some (je, brI, stI) =>
      if ft == some (tgtLab fwd jt) then (true, some je, brI, stI) else (false, some jt, brF, stF)
    | some (jt, brF, stF), none => (false, some jt, brF, stF)
    | none, some (je, brI, stI) => (true, some je, brI, stI)
    | none, none => (invChoice, none, brNl, stNl)

def finishCmpJnz {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : SymState I) (t e : Expr VNat LNat rs) (ft : Option Nat) (fwd : Trie Nat)
    (cc : I.Cond) (cmpCode : List I.Directive) (cl : FlagMask) (fl : Option FlagFact) :
    Bool × Option Nat × List I.Directive × SymState I :=
  let stCmp := { st1 with
    regs := killRegs I I.frame.scratch [] cl st1.regs
    zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
    flags := fl }
  let stB := { stCmp with
    regs := killRegs I I.frame.scratch [] FlagMask.none stCmp.regs
    zeroExt32 := killZeroExt I.frame.scratch stCmp.zeroExt32
    flags := killFlags I FlagMask.none stCmp.flags }
  let p := jnzMode I h ipT ipE stB true t e ft fwd
  let sym := lname fn (match p.2 with | some j => tgtLab fwd j | none => nl)
  (p.1, p.2, cmpCode ++ I.gpr.jcc (if p.1 then I.gpr.negCond cc else cc) sym, stB)

/-- Branch selection for `jnz`: `(inverted?, threaded target, branch code, state after branch)`. -/
def jnzSetup {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : SymState I) (t e : Expr VNat LNat rs) (ft : Option Nat) (cond : JnzCond I)
    (fwd : Trie Nat := .empty) : Option (Bool × Option Nat × List I.Directive × SymState I) :=
  match cond with
  | .flag cc =>
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] FlagMask.none st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
      flags := killFlags I FlagMask.none st1.flags }
    let p := jnzMode I h ipT ipE stB true t e ft fwd
    let sym := lname fn (match p.2 with | some j => tgtLab fwd j | none => nl)
    some (p.1, p.2, I.gpr.jcc (if p.1 then I.gpr.negCond cc else cc) sym, stB)
  | .gpr r =>
    match I.gpr.jnzGprInv? with
    | some jnzFn =>
      fuseJnzChoice I h fn nl ipT ipE st1 t e ft (fun inv l => some (jnzFn r inv l)) fwd
    | none =>
      let tg := gprThread? I h fn ipT st1 r t fwd
      let p := I.gpr.jnzGpr r (lname fn (match tg with | some j => tgtLab fwd j | none => nl))
      let stB := { st1 with
        regs := killRegs I I.frame.scratch [] p.2 st1.regs
        zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
        flags := killFlags I p.2 st1.flags }
      some (false, tg, p.1, stB)
  | .slot idx =>
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] FlagMask.all st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
      flags := killFlags I FlagMask.all st1.flags }
    let p := jnzMode I h ipT ipE stB true t e ft fwd
    let sym := lname fn (match p.2 with | some j => tgtLab fwd j | none => nl)
    (I.gpr.jnzMem (spAddr I idx) p.1 sym).bind fun (br, cl) =>
      if cl == FlagMask.all then some (p.1, p.2, br, stB) else none
  | .cmpZero co w r =>
    fuseJnzChoice I h fn nl ipT ipE st1 t e ft (fun inv l =>
      I.gpr.cmpZeroJcc (if inv then co.neg else co) w r l) fwd
  | .cmpZeroMem co w x aa cc =>
    (I.gpr.cmpMem co w aa (.imm 0#w) (.flag cc)).map fun (cmpCode, cl) =>
      let fl := (cmpMemRes I st1 co w (.var x) (.immBits w 0#64) (.flag cc) cmpCode cl).2.2.1
      finishCmpJnz I h fn nl ipT ipE st1 t e ft fwd cc cmpCode cl fl
  | .cmpZeroFlag co w x r cc =>
    (I.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ()) (.flag cc, ()) .default).map
      fun (cmpCode, cl) =>
        let fl := if Nat.ble w 64 then
          match I.gpr.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
          | some lf => some (.cmp w (if lf then .var x else .immBits w 0#64)
                                     (if lf then .immBits w 0#64 else .var x) false)
          | none => killFlags I cl st1.flags
        else killFlags I cl st1.flags
        finishCmpJnz I h fn nl ipT ipE st1 t e ft fwd cc cmpCode cl fl
  | .testImm neg w r mask =>
    fuseJnzChoice I h fn nl ipT ipE st1 t e ft (fun inv l =>
      I.gpr.testJcc (if inv then !neg else neg) w r mask l) fwd

def finishJnzBranch {rs : List Ty} (I : Isa) (fn : Sym) (nl : Nat) (tgt? : Option Nat)
    (b_taken : Expr VNat LNat rs) (br c_ft c_taken : List I.Directive)
    (nv2 nl2 ip2 : Nat) : Res I :=
  match tgt? with
  | some j => match b_taken with
    | .jump j' _ =>
      if Nat.beq j' j && c_taken.isEmpty then .ok (br ++ c_ft, nv2, nl2, ip2)
      else .error "jnz: bad thread"
    | _ => .error "jnz: not jump"
  | none => .ok (br ++ c_ft ++ [I.frame.label (lname fn nl)] ++ c_taken, nv2, nl2, ip2)

def rmwFact (w : Nat) : DefFact → Option (RmwOp × Nat × Arg VNat (.bits w))
  | .addImm64 x d => if Nat.beq w 64 then some (.add, x, .imm (d.setWidth w)) else none
  | .addrSum x y sh d =>
    if Nat.beq w 64 && Nat.beq sh 0 && d == 0#64 then some (.add, x, .var y) else none
  | .binVarVar w' op x y => if Nat.beq w' w then some (op, x, .var y) else none
  | .binVarImm w' op x c => if Nat.beq w' w then some (op, x, .imm (c.setWidth w)) else none
  | .andVarVar w' x y => if Nat.beq w' w then some (.and, x, .var y) else none
  | .andVarImm w' x c => if Nat.beq w' w then some (.and, x, .imm (c.setWidth w)) else none
  | _ => none

def tryRmwHalf (I : Isa) (st1 : SymState I) (vh : VariantHint) (n : Nat)
    (op : RmwOp) (x : Nat) (other : Arg VNat (.bits n)) (addr : Arg VNat i64) :
    Option (List I.Directive × FlagMask) :=
  match st1.memDefs.find? x with
  | some (.bits m, loadAddr) =>
    if Nat.beq m n then
      tryAddr I st1 .default loadAddr fun aa1 =>
        tryAddr I st1 vh addr fun aa2 =>
          if aa1 == aa2 then
            tryArg I st1 [] (.bits n) other fun pb =>
              I.gpr.rmwMem n (op.toOpCode n) aa1 pb
          else none
    else none
  | _ => none

def tryRmwStore (I : Isa) (st1 : SymState I) (vh : VariantHint) :
    (t : Ty) → Arg VNat t → Arg VNat i64 → Option (List I.Directive × FlagMask)
  | .bits n, .var y, addr =>
    if !Nat.ble n 64 then none
    else
      match st1.defs.find? y with
      | some df =>
        (rmwFact n df).bind fun (op, x, rhs) =>
          tryRmwHalf I st1 vh n op x rhs addr <|>
            if op.isComm then
              match rhs with
              | .var z => tryRmwHalf I st1 vh n op z (.var x) addr
              | .imm _ => none
            else none
      | none => none
  | _, _, _ => none

def lowerStore (I : Isa) (st1 : SymState I) (vh : VariantHint) :
    (t : Ty) → Arg VNat t → Arg VNat i64 → Option (List I.Directive × SymState I)
  | .pair a b, v, addr =>
    (tryArg I st1 [] (.pair a b) v fun pa =>
      match pa with
      | .vec vs => tryAddr I st1 vh addr (I.vec.vstore (.pair a b) vs)
      | _ => none).map fun (c, clob) =>
      (c, { st1 with
            regs := killRegs I I.frame.scratch I.vec.vecScratch clob st1.regs
            memDefs := .empty
            zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
            flags := killFlags I clob st1.flags })
  | t, v, addr =>
    if !isGprTy I t then none
    else
      ((tryArg I st1 [] t v fun pa =>
         tryAddr I st1 vh addr (I.gpr.store t pa) <|>
         tryAddrZext I st1 addr (I.gpr.storeZextIdx t pa)) <|>
       tryRmwStore I st1 vh t v addr).map fun (c, clob) =>
        (c, { st1 with
              regs := killRegs I I.frame.scratch [] clob st1.regs
              memDefs := .empty
              zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
              flags := killFlags I clob st1.flags })

/-- `some (m, n, x)` when the operation is `sext m n (.var x)`. -/
def sextVar? : {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig → Option (Nat × Nat × Nat)
  | _, _, .sext m n, (.var x, ()) => some (m, n, x)
  | _, _, _, _ => none

/-- `some x` when the operation is `cmp co (.var x) (.imm _)` or `cmp co (.imm _) (.var x)`. -/
def cmpVarImm? : {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig → Option Nat
  | _, _, .cmp _ (.bits _) .bool _, (.var x, .imm _, ()) => some x
  | _, _, .cmp _ (.bits _) .bool _, (.imm _, .var x, ()) => some x
  | _, _, _, _ => none

def argHasVar {t : Ty} (a : Arg VNat t) (x : Nat) : Bool :=
  match a with | .var y => Nat.beq y x | .imm _ => false

/-- `true` when variable `x` occurs among the arguments `args`. -/
def argsHaveVar : {ts : List Ty} → Tup (Arg VNat) ts → Nat → Bool
  | [], (), _ => false
  | _ :: _, (a, as), x => argHasVar a x || argsHaveVar as x

/-- `true` when `e` is a jump whose target entry and arguments never mention variable `x`. -/
def jumpAvoids {rs : List Ty} {I : Isa} (h : I.Hints) (x : Nat) : Expr VNat LNat rs → Bool
  | .jump j args => !argsHaveVar args x &&
    match h.entry.find? j with
    | some en => en.live.all fun (sa, _) => !symArgEq sa (.var x)
    | none => false
  | _ => false

/-- `true` when `op` (results from `nv'`, at `ip'`, no pre-step, not elided) lowers through a
memory-operand fusion (`tryFuseCmp`/`tryLoadSext`) in state `st`. -/
def fusesLoad {ts : List Ty} (I : Isa) (h : I.Hints) (st : SymState I) (nv' ip' : Nat)
    (op : Op VNat ts) : Bool :=
  (h.pre.find? ip').isNone && !(h.elide.getD ip' false) &&
    match resolveDsts I h ts nv' with
    | some dsts =>
      let vh := h.variant.getD ip' .default
      (tryFuseCmp I st vh op.code op.args dsts).isSome ||
        (tryLoadSext I st vh op.code op.args dsts).isSome
    | none => false

/-- Untrusted lookahead deferring `load t a` (var `nv`, at `ip`) to its memory-operand consumers:
an immediately following `sext m n (.var nv)` into the same register (`tryLoadSext`), or
`cmp (.var nv) imm` into a flag (`tryFuseCmp`) feeding a `jnz` whose one arm is such a `sext` and
whose other arm is a jump never mentioning `nv`. Soundness is checked by the consumers. -/
def loadSextNext {rs : List Ty} (I : Isa) (h : I.Hints) (nv ip : Nat) (st : SymState I) (t : Ty)
    (a : Arg VNat i64) (e : Expr VNat LNat rs) : Bool :=
  let st' := { st with memDefs := st.memDefs.insert nv (t, a) }
  let sextAt : Nat → Nat → Expr VNat LNat rs → Bool := fun ip' nv' e' =>
    match e' with
    | .let_ op _ =>
      match sextVar? op.code op.args with
      | some (_, _, x) =>
        Nat.beq x nv && h.dest.find? nv' == h.dest.find? nv && fusesLoad I h st' nv' ip' op
      | none => false
    | _ => false
  isGprTy I t && (sextAt (ip + 1) (nv + 1) e ||
    match e with
    | .let_ op k =>
      cmpVarImm? op.code op.args == some nv &&
        (match h.dest.find? (nv + 1) with | some (.flag _) => true | _ => false) &&
        fusesLoad I h st' (nv + 1) (ip + 1) op &&
        match k (Tup.levels _ (nv + 1)) with
        | .jnz (.var cx) tt ee =>
          Nat.beq cx (nv + 1) && (h.pre.find? (ip + 2)).isNone &&
            ((jumpAvoids h nv tt && sextAt (ip + 3) (nv + 2) ee) ||
              (jumpAvoids h nv ee && sextAt (ip + 4) (nv + 2) tt))
        | _ => false
    | _ => false)

def lowerLoad (I : Isa) (h : I.Hints) (nv ip : Nat) (st1 : SymState I) (t : Ty) (a : Arg VNat i64)
    (fuse : Bool := false) : Option (List I.Directive × SymState I) :=
  if h.elide.getD ip false || fuse then
    if isGprTy I t then
      some ([], { st1 with memDefs := st1.memDefs.insert nv (t, a) })
    else none
  else
    let vh := h.variant.getD ip .default
    match h.dest.find? nv with
    | some (.gpr d) =>
      if !(isAllocGpr I h.saved d && isGprTy I t) then none
      else
        (tryAddr I st1 vh a (I.gpr.load t d) <|>
          tryAddrZext I st1 a (I.gpr.loadZextIdx t d)).map fun (c, clob) =>
        let isZ32 := I.gpr.zeroUpper32Load && tyEq t (.bits 32)
        let rl := if I.gpr.zeroExtLoad || isZ32 then RegLoc.gprZ d else .gpr d
        let zExt := killZeroExt (d :: I.frame.scratch) st1.zeroExt32
        let zExt1 := if isZ32 then d :: zExt else zExt
        (c, { st1 with
              regs := (.var nv, rl) :: killRegs I (d :: I.frame.scratch) [] clob st1.regs
              zeroExt32 := zExt1
              flags := killFlags I clob st1.flags })
    | some (.vec vd) => (vecWidth? I t).bind fun w =>
      if !isAllocVec I vd then none
      else (tryAddr I st1 vh a (I.vec.vload t vd)).map fun (c, clob) =>
        (c, { st1 with
              regs := (.var nv, .vec vd) ::
                killRegs I I.frame.scratch (vd :: I.vec.vecScratch) clob st1.regs
              vecWidths := st1.vecWidths.insert nv w
              zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
              flags := killFlags I clob st1.flags })
    | _ => none

/-- `true` when target `I` elides the stack frame completely for a 0-slot leaf function. -/
def isZeroLeaf (I : Isa) (h : I.Hints) (E : Ext) : Bool :=
  I.frame.leafZeroFrame && Nat.beq h.totalSlots 0 && E.callees.isEmpty

/-- Effective frame byte size (0 for a zero-frame leaf, else `I.frame.frameSize h.totalSlots`). -/
def effFrame (I : Isa) (h : I.Hints) (E : Ext) : Nat :=
  if isZeroLeaf I h E then 0 else I.frame.frameSize h.totalSlots

/-- Function prologue directives (`[]` for a zero-frame leaf). -/
def fnPrologue (I : Isa) (h : I.Hints) (E : Ext) : List I.Directive :=
  if isZeroLeaf I h E then [] else (I.frame.prologue h.totalSlots).1

/-- Function epilogue directives (`[]` for a zero-frame leaf). -/
def fnEpilogue (I : Isa) (h : I.Hints) (E : Ext) : List I.Directive :=
  if isZeroLeaf I h E then [] else (I.frame.epilogue h.totalSlots).1

def lowerTail {ts : List Ty} (I : Isa) (h : I.Hints) (E : Ext) (st1 : SymState I)
    (mc tail : List I.Directive)
    (args : Tup (Arg VNat) ts) (locs : Tup (AbiReg I.Reg I.VReg) ts) (nv nl ip : Nat) : Res I :=
  match abiTargets I args locs with
  | none => .error "tail: imm"
  | some tgts => match shuffle I h.nslots h.saved st1 tgts (h.deadFlags.getD ip false) with
    | none => .error "tail: shuffle"
    | some (sc, st') =>
      .ok (mc ++ sc ++ canonAbiCode I locs (abiSkips I st'.regs st'.zeroExt32 args locs) ++
        restoreCs I h.nslots h.saved ++ fnEpilogue I h E ++ tail, nv, nl, ip + 1)

mutual
/-- Instruction-pointer count consumed by `lowerExpr` on `e` starting at `(nv, nl)`. -/
def exprIpCount {rs : List Ty} : Expr VNat LNat rs → Nat → Nat → Nat × Nat × Nat
  | .let_ (ts := ts) _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCount (k (Tup.levels ts nv)) (nv + ts.length) nl
    (nv1, nl1, d + 1)
  | .load _ _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCount (k nv) (nv + 1) nl
    (nv1, nl1, d + 1)
  | .store _ _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCount k nv nl
    (nv1, nl1, d + 1)
  | .call (bs := bs) _ _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCount (k (Tup.levels bs nv)) (nv + bs.length) nl
    (nv1, nl1, d + 1)
  | .jnz (.imm b) t e, nv, nl =>
    let (nv1, nl1, d) := if b then exprIpCount t nv nl else exprIpCount e nv nl
    (nv1, nl1, d + 1)
  | .jnz (.var _) t e, nv, nl =>
    let (nv1, nl1, de) := exprIpCount e nv (nl + 1)
    let (nv2, nl2, dt) := exprIpCount t nv1 nl1
    (nv2, nl2, de + dt + 1)
  | .jump _ _, nv, nl | .ret _, nv, nl | .exit _ _, nv, nl | .hlt, nv, nl => (nv, nl, 1)
  | .group (sig := sig) bodies k, nv, nl =>
    let ls := Tup.levels sig nl
    let (nv1, nl1, dk) := exprIpCount (k ls) nv (nl + sig.length)
    let (nv2, nl2, db) := blocksIpCount (bodies ls) nv1 nl1
    (nv2, nl2, dk + db)

def blocksIpCount {rs : List Ty} :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig → Nat → Nat → Nat × Nat × Nat
  | _, .nil, nv, nl => (nv, nl, 0)
  | _, .cons (ts := ts) b bs, nv, nl =>
    let (nv1, nl1, db) := exprIpCount (b (Tup.levels ts nv)) (nv + ts.length) nl
    let (nv2, nl2, dbs) := blocksIpCount bs nv1 nl1
    (nv2, nl2, db + dbs)
end

/-- Instruction-pointer at which `lowerExpr` starts lowering the `then`-arm `t` of `jnz`. -/
def jnzIpT {rs : List Ty} (nv nl ip : Nat) (t e : Expr VNat LNat rs) : Nat :=
  match t with
  | .jump _ _ => ip + 1 + (exprIpCount e nv (nl + 1)).2.2
  | _ => ip + 1

mutual
def exprFreeOfVar {I : Isa} (h : I.Hints) (x : Nat) {rs : List Ty} :
    Expr VNat LNat rs → Nat → Bool
  | .let_ (ts := ts) op k, nv =>
    !argsHaveVar op.args x && exprFreeOfVar h x (k (Tup.levels ts nv)) (nv + ts.length)
  | .load _ a k, nv =>
    !argHasVar a x && exprFreeOfVar h x (k nv) (nv + 1)
  | .store v a k, nv =>
    !argHasVar v x && !argHasVar a x && exprFreeOfVar h x k nv
  | .call (bs := bs) _ args k, nv =>
    !argsHaveVar args x && exprFreeOfVar h x (k (Tup.levels bs nv)) (nv + bs.length)
  | .jnz c t e, nv =>
    !argHasVar c x && exprFreeOfVar h x t nv && exprFreeOfVar h x e nv
  | .jump j args, _ =>
    !argsHaveVar args x &&
      match h.entry.find? j with
      | some en => en.live.all fun (sa, _) => !symArgEq sa (.var x)
      | none => true
  | .ret vs, _ => !argsHaveVar vs x
  | .exit _ args, _ => !argsHaveVar args x
  | .hlt, _ => true
  | .group (sig := sig) bodies k, nv =>
    let ls := Tup.levels sig 0
    exprFreeOfVar h x (k ls) nv && blocksFreeOfVar h x (bodies ls) nv

def blocksFreeOfVar {I : Isa} (h : I.Hints) (x : Nat) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig → Nat → Bool
  | _, .nil, _ => true
  | _, .cons (ts := ts) b bs, nv =>
    exprFreeOfVar h x (b (Tup.levels ts nv)) (nv + ts.length) && blocksFreeOfVar h x bs nv
end

/-- Lookahead deferring `.cmp` against `0`/bit-test feeding a single-use `.jnz` via
`I.gpr.cmpZeroJcc` / `I.gpr.testJcc`. Single-use-ness (the flag is dead in both `jnz` arms) is read
in O(1) from the untrusted `h.deferJnz` hint (computed natively by `deferScan`) instead of
re-walking both arms with `exprFreeOfVar` inside the kernel (O(size²) per function). A wrong hint
can only change the `df` flag passed to `lowerOp`, which the lowering proofs treat as opaque. -/
def deferJnzNext {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nv nl ip : Nat)
    (st1 : SymState I) {ts : List Ty} (op : Op VNat ts) (k' : Expr VNat LNat rs) : Bool :=
  match ts, k' with
  | [.bool], .jnz (.var cx) _ _ =>
    Nat.beq cx nv && h.deferJnz.getD ip false &&
      match lowerOp I h nv ip st1 op true with
      | some (_, st2) =>
        match stepPre I h (ip + 1) st2 with
        | some (_, stAfter) =>
          match findJnzCond I h.nslots stAfter nv with
          | some (.flag _) => true
          | some (.cmpZero co w r) => (I.gpr.cmpZeroJcc co w r (lname fn nl)).isSome
          | some (.cmpZeroMem _ _ _ _ cc)
          | some (.cmpZeroFlag _ _ _ _ cc) => h.dest.find? nv != some (.flag cc)
          | some (.testImm neg w r mask) => (I.gpr.testJcc neg w r mask (lname fn nl)).isSome
          | _ => false
        | none => false
      | none => false
  | _, _ => false

def isLeaDeferCand {sig ts : List Ty} (shr : Bool) (code : OpCode sig ts) : Bool :=
  match ts, code with
  | [.bits w], .shl (.bits _) | [.bits w], .add (.bits _) | [.bits w], .sub (.bits _) =>
    Nat.beq w 32 || Nat.beq w 64
  | [.bits w], .lshr (.bits _) | [.bits w], .ashr (.bits _) =>
    shr && (Nat.beq w 32 || Nat.beq w 64)
  | [.bits 64], .zext 32 64 => true
  | _, _ => false

/-- Lookahead deferring shift/add/sub arithmetic feeding a single-use `tryLeaArith` consumer.
Single-use-ness (`nv` dead in the continuation after the consumer) is read in O(1) from the
untrusted `h.deferLea` hint (computed natively by `deferScan`) instead of an in-kernel
`exprFreeOfVar` walk of the rest of the block. -/
def deferLeaNext {rs : List Ty} (I : Isa) (h : I.Hints) (nv ip : Nat)
    (st1 : SymState I) {ts : List Ty} (op : Op VNat ts) (k' : Expr VNat LNat rs) : Bool :=
  if !isLeaDeferCand I.gpr.deferShiftAlu op.code then false
  else
    match ts, k' with
    | [_], .let_ (ts := ts2) op2 _k2 =>
      match recordDefC I.gpr.addrCse st1.defs op.code op.args with
      | some df =>
        match stepPre I h (ip + 1) { st1 with defs := st1.defs.insert nv df } with
        | some (_, stAfter) =>
          match resolveDsts I h ts2 (nv + 1) with
          | some dsts2 =>
            ((tryLeaArith I stAfter op2.code op2.args dsts2).isSome ||
              (tryShiftCmpFuse I stAfter op2.code op2.args dsts2).isSome) &&
              h.deferLea.getD ip false
          | none => false
        | none => false
      | none => false
    | _, _ => false

/-- Accumulator of `deferScan`: `(deferJnz, deferLea)` hint tries. -/
abbrev DeferAcc := Trie Bool × Trie Bool

mutual
/-- Untrusted prepass computing `Hints.deferJnz` / `Hints.deferLea`, i.e. exactly the
`exprFreeOfVar` lookaheads `deferJnzNext` / `deferLeaNext` used to re-walk inside the kernel
(O(size²) per function):
* at every `let [.bool] …; jnz (.var nv) t e` site, whether `nv` is dead in both arms;
* at every `let [_] op …; let op2 k2` site with `isLeaDeferCand op.code`, whether `nv` is dead in
  the continuation `k2`.
Both are keyed by the first `let`'s `ip`; the walk follows `(nv, nl, ip)` exactly like
`exprIpCount` / `lowerExpr`. Returns `(acc, nv', nl', ip')`. -/
def deferScan {I : Isa} (h : I.Hints) {rs : List Ty} :
    Expr VNat LNat rs → Nat → Nat → Nat → DeferAcc → DeferAcc × Nat × Nat × Nat
  | .let_ (ts := ts) op k, nv, nl, ip, acc =>
    let k' := k (Tup.levels ts nv)
    let accJ := match ts, k' with
      | [.bool], .jnz (.var cx) t e =>
        if Nat.beq cx nv && exprFreeOfVar h nv t (nv + 1) && exprFreeOfVar h nv e (nv + 1) then
          acc.1.insert ip true
        else acc.1
      | _, _ => acc.1
    let accL := if !isLeaDeferCand I.gpr.deferShiftAlu op.code then acc.2 else
      match ts, k' with
      | [_], .let_ (ts := ts2) _ k2 =>
        if exprFreeOfVar h nv (k2 (Tup.levels ts2 (nv + 1))) (nv + 1 + ts2.length) then
          acc.2.insert ip true
        else acc.2
      | _, _ => acc.2
    deferScan h k' (nv + ts.length) nl (ip + 1) (accJ, accL)
  | .load _ _ k, nv, nl, ip, acc => deferScan h (k nv) (nv + 1) nl (ip + 1) acc
  | .store _ _ k, nv, nl, ip, acc => deferScan h k nv nl (ip + 1) acc
  | .call (bs := bs) _ _ k, nv, nl, ip, acc =>
    deferScan h (k (Tup.levels bs nv)) (nv + bs.length) nl (ip + 1) acc
  | .jnz (.imm b) t e, nv, nl, ip, acc =>
    if b then deferScan h t nv nl (ip + 1) acc else deferScan h e nv nl (ip + 1) acc
  | .jnz (.var _) t e, nv, nl, ip, acc =>
    let (acc1, nv1, nl1, ip1) := deferScan h e nv (nl + 1) (ip + 1) acc
    deferScan h t nv1 nl1 ip1 acc1
  | .jump _ _, nv, nl, ip, acc | .ret _, nv, nl, ip, acc | .exit _ _, nv, nl, ip, acc
  | .hlt, nv, nl, ip, acc => (acc, nv, nl, ip + 1)
  | .group (sig := sig) bodies k, nv, nl, ip, acc =>
    let ls := Tup.levels sig nl
    let (acc1, nv1, nl1, ip1) := deferScan h (k ls) nv (nl + sig.length) ip acc
    deferScanBlocks h (bodies ls) nv1 nl1 ip1 acc1

def deferScanBlocks {I : Isa} (h : I.Hints) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig → Nat → Nat → Nat → DeferAcc →
      DeferAcc × Nat × Nat × Nat
  | _, .nil, nv, nl, ip, acc => (acc, nv, nl, ip)
  | _, .cons (ts := ts) b bs, nv, nl, ip, acc =>
    let (acc1, nv1, nl1, ip1) := deferScan h (b (Tup.levels ts nv)) (nv + ts.length) nl ip acc
    deferScanBlocks h bs nv1 nl1 ip1 acc1
end

/-- Fill `h.deferJnz` / `h.deferLea` for `f` (the mid-end function later passed to `lowerFn`). -/
def addDeferHints {I : Isa} (h : I.Hints) (f : Fn) : I.Hints :=
  let r := deferScan h (f.body VNat LNat (Tup.levels f.as 0)) f.as.length 0 0 (.empty, .empty)
  { h with deferJnz := r.1.1, deferLea := r.1.2 }

def blockTrampoline? {rs : List Ty} (I : Isa) (h : I.Hints)
    (defs : Trie DefFact) (vw : Trie SlotWidth)
    (lid nv ip : Nat) {ts : List Ty} (b : Tup VNat ts → Expr VNat LNat rs) : Option Nat :=
  match h.entry.find? lid with
  | none => none
  | some en =>
    if !entryScopeOk nv en then none
    else match buildEntryBase I h.nslots vw en.live
        { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
      | none => none
      | some baseSt =>
        match bindBlockParams I h.nslots ts en.ploc nv baseSt with
        | none => none
        | some initSt =>
          match b (Tup.levels ts nv) with
          | .jump j' args' =>
            match stepPre I h ip initSt, h.entry.find? j' with
            | some ([], st1), some en' =>
              match jumpTargets I args' en'.ploc with
              | none => none
              | some argTgts =>
                let tgts := en'.live ++ argTgts
                if !(tgts.all fun (_, loc) => jumpLocOk I h.nslots loc) then none
                else match shuffle I h.nslots h.saved st1 tgts with
                  | some ([], _) => some j'
                  | _ => none
            | _, _ => none
          | _ => none

def collectRawFwds {rs : List Ty} (I : Isa) (h : I.Hints)
    (defs : Trie DefFact) (vw : Trie SlotWidth)
    (fwd : Trie Nat) (fwdTgts : Trie Bool) :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig → Nat → Nat → Nat → Nat →
    Trie Nat → List Nat → Trie Nat × List Nat
  | _, .nil, _, _, _, _, raw, lids => (raw, lids)
  | _, .cons (ts := ts) b bs, lid, nv, nl, ip, raw, lids =>
    let raw1_lids :=
      if (fwd.find? lid).isNone && !(fwdTgts.getD lid false) then
        match blockTrampoline? I h defs vw lid nv ip b with
        | some j' => (raw.insert lid j', lid :: lids)
        | none => (raw, lids)
      else (raw, lids)
    let (nv1, nl1, d) := exprIpCount (b (Tup.levels ts nv)) (nv + ts.length) nl
    collectRawFwds I h defs vw fwd fwdTgts bs (lid + 1) nv1 nl1 (ip + d) raw1_lids.1 raw1_lids.2

def resolveTrampoline (raw fwd : Trie Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, cur =>
    match raw.find? cur with
    | none => some (fwd.getD cur cur)
    | some nxt => resolveTrampoline raw fwd fuel nxt

def findGroupFwds {rs : List Ty} (I : Isa) (h : I.Hints) (st : SymState I)
    {sig : List (List Ty)} (bodies : Blocks VNat LNat rs sig)
    (k : Expr VNat LNat rs) (nv nl ip : Nat)
    (fwd : Trie Nat) (fwdTgts : Trie Bool) : Trie Nat × Trie Bool :=
  let (nv1, nl1, d) := exprIpCount k nv (nl + sig.length)
  let (raw, lids) :=
    collectRawFwds I h st.defs st.vecWidths fwd fwdTgts bodies nl nv1 nl1 (ip + d) .empty []
  lids.foldl
    (fun (f, ft) lid =>
      match resolveTrampoline raw fwd (sig.length + 1) lid with
      | some m =>
        if (raw.find? m).isNone && (fwd.find? m).isNone && m != lid then
          (f.insert lid m, ft.insert m true)
        else (f, ft)
      | none => (f, ft))
    (fwd, fwdTgts)

mutual
def lowerExpr (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    Expr VNat LNat rs → Nat → Nat → Nat → SymState I → Option Nat →
    (fwd : Trie Nat := .empty) → (fwdTgts : Trie Bool := .empty) → Res I
  | .let_ (ts := ts) op k, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "let: pre"
    | some (mc, st1) =>
      let k' := k (Tup.levels ts nv)
      let df := deferJnzNext I h fn nv nl ip st1 op k' || deferLeaNext I h nv ip st1 op k'
      match lowerOp I h nv ip st1 op df with
      | none => .error "let: op"
      | some (c, st2) =>
        prepend (mc ++ c) (lowerExpr I h E fn k' (nv + ts.length) nl (ip + 1) st2 ft fwd fwdTgts)
  | .load t a k, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "load: pre"
    | some (mc, st1) =>
      match lowerLoad I h nv ip st1 t a (loadSextNext I h nv ip st1 t a (k nv)) with
      | none => .error "load: dst/addr"
      | some (c, st2) =>
        prepend (mc ++ c) (lowerExpr I h E fn (k nv) (nv + 1) nl (ip + 1) st2 ft fwd fwdTgts)
  | .store (t := t) v a k, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "store: pre"
    | some (mc, st1) => match lowerStore I st1 (h.variant.getD ip .default) t v a with
      | none => .error "store: op/addr"
      | some (c, st2) => prepend (mc ++ c) (lowerExpr I h E fn k nv nl (ip + 1) st2 ft fwd fwdTgts)
  | .call f (as := as) (bs := bs) args k, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "call: pre"
    | some (mc, st1) =>
      if !calleeAllowed E f as bs then .error "call: callee"
      else match I.assignArgs as, I.assignRets bs with
        | some argLocs, some retLocs => match abiTargets I args argLocs with
          | none => .error "call: imm"
          | some tgts => match shuffle I h.nslots h.saved st1 tgts (h.deadFlags.getD ip false) with
            | none => .error "call: shuffle"
            | some (sc, st2) => match bindAbiParams I retLocs nv (afterCallState I h.saved st2) with
              | none => .error "call: ret bind"
              | some st4 =>
                prepend (mc ++ sc ++
                    canonAbiCode I argLocs (abiSkips I st2.regs st2.zeroExt32 args argLocs) ++
                    I.frame.call f)
                  (lowerExpr I h E fn (k (Tup.levels bs nv)) (nv + bs.length) nl (ip + 1) st4 ft
                    fwd fwdTgts)
        | _, _ => .error "call: abi"
  | .jnz (.imm b) t e, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "jnz: pre"
    | some (mc, st1) =>
      prepend mc (if b then lowerExpr I h E fn t nv nl (ip + 1) st1 ft fwd fwdTgts
                  else lowerExpr I h E fn e nv nl (ip + 1) st1 ft fwd fwdTgts)
  | .jnz (.var cx) t e, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "jnz: pre"
    | some (mc, st1) => match findJnzCond I h.nslots st1 cx with
      | none => .error "jnz: cond"
      | some cond =>
        match jnzSetup I h fn nl (jnzIpT nv nl ip t e) (ip + 1) st1 t e ft cond fwd with
        | none => .error "jnz: setup"
        | some (inv, tgt?, br, stBr) =>
          let ftT := match tgt? with | some j => some (tgtLab fwd j) | none => ft
          let ftF := match tgt? with | some _ => ft | none => none
          match lowerExpr I h E fn e nv (nl + 1) (ip + 1) stBr
              (if inv then ftT else ftF) fwd fwdTgts with
          | .error err => .error err
          | .ok (ce, nv1, nl1, ip1) =>
            match lowerExpr I h E fn t nv1 nl1 ip1 stBr
                (if inv then ftF else ftT) fwd fwdTgts with
            | .error err => .error err
            | .ok (ct, nv2, nl2, ip2) =>
              prepend mc (if inv then finishJnzBranch I fn nl tgt? e br ct ce nv2 nl2 ip2
                          else finishJnzBranch I fn nl tgt? t br ce ct nv2 nl2 ip2)
  | .jump j args, nv, nl, ip, st, ft, fwd, _ =>
    match stepPre I h ip st, h.entry.find? j with
    | some (mc, st1), some en => match jumpTargets I args en.ploc with
      | none => .error "jump: arity"
      | some argTgts =>
        let tgts := en.live ++ argTgts
        if !(tgts.all fun (_, loc) => jumpLocOk I h.nslots loc) then .error "jump: loc"
        else match shuffle I h.nslots h.saved st1 tgts (h.deadFlags.getD ip false) with
          | none => .error "jump: shuffle"
          | some (sc, _) =>
            let jt := tgtLab fwd j
            .ok (mc ++ sc ++ (if ft == some jt then [] else I.gpr.jmp (lname fn jt)),
                 nv, nl, ip + 1)
    | _, _ => .error "jump: pre/entry"
  | .ret vs, nv, nl, ip, st, _, _, _ =>
    match stepPre I h ip st, I.assignRets rs with
    | some (mc, st1), some retLocs => lowerTail I h E st1 mc I.frame.ret vs retLocs nv nl ip
    | _, _ => .error "ret: pre/abi"
  | .exit f (as := as) args, nv, nl, ip, st, _, _, _ =>
    match stepPre I h ip st, I.assignArgs as with
    | some (mc, st1), some argLocs =>
      if !E.exits.contains f then .error "exit: target"
      else lowerTail I h E st1 mc (I.frame.exitJmp f) args argLocs nv nl ip
    | _, _ => .error "exit: pre/abi"
  | .hlt, nv, nl, ip, _, _, _, _ => .ok ([], nv, nl, ip + 1)
  | .group (sig := sig) bodies k, nv, nl, ip, st, ft, fwd, fwdTgts =>
    let ls := Tup.levels sig nl
    let (fwd', tgts') := findGroupFwds I h st (bodies ls) (k ls) nv nl ip fwd fwdTgts
    let ftK := firstNonFwd fwd' (bodies ls) nl ft
    match lowerExpr I h E fn (k ls) nv (nl + sig.length) ip st ftK fwd' tgts' with
    | .error err => .error err
    | .ok (ck, nv1, nl1, ip1) =>
      prepend ck (lowerBlocks I h E fn (bodies ls) nl nv1 nl1 ip1 st.defs st.vecWidths ft
        fwd' tgts')

def lowerBlocks (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig →
    Nat → Nat → Nat → Nat → Trie DefFact → Trie SlotWidth → Option Nat →
    (fwd : Trie Nat := .empty) → (fwdTgts : Trie Bool := .empty) → Res I
  | _, .nil, _, nv, nl, ip, _, _, _, _, _ => .ok ([], nv, nl, ip)
  | _, .cons (ts := ts) b bs, lid, nv, nl, ip, defs, vw, ft, fwd, fwdTgts =>
    match fwd.find? lid with
    | some fwdTgt =>
      match blockTrampoline? I h defs vw lid nv ip b with
      | some j' =>
        if !(Nat.beq (tgtLab fwd j') fwdTgt && (fwd.find? fwdTgt).isNone) then .error "block: fwd"
        else lowerBlocks I h E fn bs (lid + 1) (nv + ts.length) nl (ip + 1) defs vw ft fwd fwdTgts
      | none => .error "block: fwd"
    | none =>
      match h.entry.find? lid with
      | none => .error "block: entry"
      | some en =>
        if !entryScopeOk nv en then .error "block: scope"
        else match buildEntryBase I h.nslots vw en.live
            { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
          | none => .error "block: live"
          | some baseSt => match bindBlockParams I h.nslots ts en.ploc nv baseSt with
            | none => .error "block: plocs"
            | some initSt =>
              let ftB := firstNonFwd fwd bs (lid + 1) ft
              match lowerExpr I h E fn (b (Tup.levels ts nv)) (nv + ts.length) nl ip initSt ftB
                  fwd fwdTgts with
              | .error err => .error err
              | .ok (cb, nv1, nl1, ip1) =>
                prepend (I.frame.label (lname fn lid) :: cb)
                  (lowerBlocks I h E fn bs (lid + 1) nv1 nl1 ip1 defs vw ft fwd fwdTgts)
end

def lowerFn (I : Isa) (h : I.Hints) (E : Ext) (f : Fn) : Except String (List I.Directive) :=
  if !(listNodup h.saved && h.saved.all (I.frame.calleeSaved.contains ·)) then .error "fn: saved"
  else match I.assignArgs f.as, I.assignRets f.rs with
    | some argLocs, some _ =>
      match bindAbiParams I argLocs 0
        { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
      | none => .error "fn: abi bind"
      | some st0 =>
        match lowerExpr I h E f.name (f.body VNat LNat (Tup.levels f.as 0))
            f.as.length 0 0 st0 none with
        | .ok (c, _, _, _) =>
          .ok (I.frame.label f.name :: (fnPrologue I h E ++ saveCs I h.nslots h.saved ++ c))
        | .error e => .error e
    | _, _ => .error "fn: abi"

/-- No directive of `c` is a label. -/
def NoLab (I : Isa) (c : List I.Directive) : Prop := ∀ l, I.frame.label l ∉ c

/-- Target-side side condition for `LabelsUnique`: `label` is injective and no `Isa` snippet emits
a label directive. -/
structure LabelClean (I : Isa) : Prop where
  label_inj : ∀ a b, I.frame.label a = I.frame.label b → a = b
  (mov : ∀ d s, NoLab I (I.gpr.mov d s)) (movi : ∀ d c, NoLab I (I.gpr.movi d c))
  (setcc : ∀ d c, NoLab I (I.gpr.setcc d c)) (jmp : ∀ l, NoLab I (I.gpr.jmp l))
  (jcc : ∀ c l, NoLab I (I.gpr.jcc c l)) (jnzGpr : ∀ r l, NoLab I (I.gpr.jnzGpr r l).1)
  jnzGprInv : ∀ fn r inv l, I.gpr.jnzGprInv? = some fn → NoLab I (fn r inv l).1 :=
    by intro _ _ _ _ h; cases h
  op : ∀ {sig rs : List Ty} (code : OpCode sig rs) pas dsts vh c cl,
    I.gpr.op code pas dsts vh = some (c, cl) → NoLab I c
  testOp : ∀ w neg pa pb pd c cl, I.gpr.testOp w neg pa pb pd = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ h; cases h
  cmpMem : ∀ co w a pb pd c cl, I.gpr.cmpMem co w a pb pd = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ h; cases h
  testMem : ∀ w neg a pb pd c cl, I.gpr.testMem w neg a pb pd = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ h; cases h
  loadSext : ∀ m n r a c cl, I.gpr.loadSext m n r a = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ h; cases h
  cmpZeroJcc : ∀ co w r l c cl, I.gpr.cmpZeroJcc co w r l = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ h; cases h
  testJcc : ∀ neg w r mask l c cl, I.gpr.testJcc neg w r mask l = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ h; cases h
  aluMem : ∀ w code memRhs a pb rd c cl,
    I.gpr.aluMem w code memRhs a pb rd = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ _ h; cases h
  jnzMem : ∀ a inv l c cl, I.gpr.jnzMem a inv l = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ h; cases h
  rmwMem : ∀ w code a pb c cl, I.gpr.rmwMem w code a pb = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ h; cases h
  leaArith : ∀ w base? idx sc disp rd c cl,
    I.gpr.leaArith w base? idx sc disp rd = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ _ h; cases h
  loadZextIdx : ∀ t rd base idx sc disp c cl,
    I.gpr.loadZextIdx t rd base idx sc disp = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ _ h; cases h
  loadSextZextIdx : ∀ m n rd base idx sc disp c cl,
    I.gpr.loadSextZextIdx m n rd base idx sc disp = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ _ _ h; cases h
  storeZextIdx : ∀ t pa base idx sc disp c cl,
    I.gpr.storeZextIdx t pa base idx sc disp = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ _ h; cases h
  leaArithZext : ∀ base? idx sh disp rd c cl,
    I.gpr.leaArithZext base? idx sh disp rd = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ h; cases h
  shiftAlu : ∀ w code ra rb sh n rd c cl,
    I.gpr.shiftAlu w code ra rb sh n rd = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ _ _ h; cases h
  shiftCmp : ∀ o w ra rb sh n lhsShift pd c cl,
    I.gpr.shiftCmp o w ra rb sh n lhsShift pd = some (c, cl) → NoLab I c :=
    by intro _ _ _ _ _ _ _ _ _ _ h; cases h
  moviDeadFlags : ∀ fn d c, I.gpr.moviDeadFlags? = some fn → NoLab I (fn d c).1 :=
    by intro _ _ _ h; cases h
  (load : ∀ t r a c cl, I.gpr.load t r a = some (c, cl) → NoLab I c)
  (store : ∀ t pa a c cl, I.gpr.store t pa a = some (c, cl) → NoLab I c)
  (clearFlags : NoLab I I.gpr.clearFlags) (vmov : ∀ w d s, NoLab I (I.vec.vmov w d s))
  (vmovi : ∀ w d c code, I.vec.vmovi w d c = some code → NoLab I code)
  (vslotSt : ∀ w i s, NoLab I (I.vec.vslotSt w i s))
  (vslotLd : ∀ w d i, NoLab I (I.vec.vslotLd w d i))
  vop : ∀ {sig rs : List Ty} (code : OpCode sig rs) pas dsts vh c cl,
    I.vec.vop code pas dsts vh = some (c, cl) → NoLab I c
  (vload : ∀ t d a c cl, I.vec.vload t d a = some (c, cl) → NoLab I c)
  (vstore : ∀ t s a c cl, I.vec.vstore t s a = some (c, cl) → NoLab I c)
  (prologue : ∀ n, NoLab I (I.frame.prologue n).1)
  (epilogue : ∀ n, NoLab I (I.frame.epilogue n).1)
  (slotSt : ∀ i r, NoLab I (I.frame.slotSt i r)) (slotLd : ∀ r i, NoLab I (I.frame.slotLd r i))
  saveRegs : ∀ fn base rs, I.frame.saveRegs? = some fn → NoLab I (fn base rs) :=
    by intro _ _ _ h; cases h
  restoreRegs : ∀ fn base rs, I.frame.restoreRegs? = some fn → NoLab I (fn base rs) :=
    by intro _ _ _ h; cases h
  (canonAbi : ∀ t r, NoLab I (I.frame.canonAbi t r).1) (call : ∀ f, NoLab I (I.frame.call f))
  (exitJmp : ∀ f, NoLab I (I.frame.exitJmp f)) (ret : NoLab I I.frame.ret)

/-- Frame size in bytes required by `hints` on target `T`. -/
abbrev frame (T : Target) (hints : T.toIsa.Hints) : Nat :=
  T.frame.frameSize hints.totalSlots

end Rega
end LeanQbe.T
