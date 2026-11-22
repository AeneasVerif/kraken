module

public import LeanQbe.T.Target

/-!
# PHOAS-First Checked Lowering (`T7a`, Locks `L1`–`L10`, Guardrails 1–5)

Direct structural lowering of `Expr VNat LNat rs` / `Blocks VNat LNat rs sig` (zero `TFlat`/`denote`)
consuming untrusted literal `LeanQbe.T.Trie` `Hints`: bounded `regs`, `O(log N)` multi-granule
`slots : Trie SlotEntry` with 15-granule overlap clearing, lexical `defs : Trie DefFact` (`L9`) and
`vecWidths : Trie SlotWidth`, sequential `nv` (`h.dest` keyed by `x : Nat`), `entryScopeOk nv`,
read-only flag cache (`L3`–`L6`), `PreStep.clearFlags` (`L7`), `canonAbi`, pure `Bool` comparisons,
and monotone `nl` label counter.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

abbrev VNat : Ty → Type := fun _ => Nat
abbrev LNat : List Ty → Type := fun _ => Nat

inductive RegLoc (Reg VReg Cond : Type) where
  | gpr (r : Reg) | vec (v : VReg) | flag (c : Cond)
  deriving DecidableEq, Repr

inductive SlotEntry where
  | gpr (sas : List SymArg)
  | vec (w : SlotWidth) (sas : List SymArg)
  deriving DecidableEq, Repr

def SlotEntry.slots : SlotEntry → Nat
  | .gpr _ => 1 | .vec w _ => w.slots

inductive DefFact where
  | addImm64 (base : Nat) (disp : BitVec 64)
  | imm64 (c : BitVec 64)
  deriving DecidableEq, Repr

structure SymState (I : Isa) where
  regs : List (SymArg × RegLoc I.Reg I.VReg I.Cond)
  slots : Trie SlotEntry
  defs : Trie DefFact
  vecWidths : Trie SlotWidth

structure Ext where
  callees : List (Sym × List Ty × List Ty) := []
  exits : List Sym := []
  deriving DecidableEq, Repr, Inhabited

abbrev Res (I : Isa) := Except String (List I.Directive × Nat × Nat × Nat)

/-! ## Pure `Bool` Equalities, Labels, and Bank Predicates (Guardrail 2) -/

def slotWidthEq : SlotWidth → SlotWidth → Bool
  | .w64, .w64 | .w128, .w128 | .w256, .w256 | .w512, .w512 => true
  | _, _ => false

def symArgEq : SymArg → SymArg → Bool
  | .var x, .var y => Nat.beq x y
  | .immBool a, .immBool b => Bool.beq a b
  | .immBits w1 c1, .immBits w2 c2 => Nat.beq w1 w2 && c1 == c2
  | .immVec w1 c1, .immVec w2 c2 => slotWidthEq w1 w2 && c1 == c2
  | _, _ => false

def regLocEq {I : Isa} : RegLoc I.Reg I.VReg I.Cond → RegLoc I.Reg I.VReg I.Cond → Bool
  | .gpr a, .gpr b => a == b | .vec a, .vec b => a == b | .flag a, .flag b => a == b
  | _, _ => false

def locEq {I : Isa} : I.Loc → I.Loc → Bool
  | .gpr a, .gpr b => a == b | .vec a, .vec b => a == b | .flag a, .flag b => a == b
  | .slot i w1, .slot j w2 => Nat.beq i j && slotWidthEq w1 w2
  | _, _ => false

def tyEq : Ty → Ty → Bool
  | .bool, .bool => true | .bits m, .bits n => Nat.beq m n | .float f, .float g => f == g
  | .pair a1 b1, .pair a2 b2 => tyEq a1 a2 && tyEq b1 b2 | _, _ => false

def listTyEq : List Ty → List Ty → Bool
  | [], [] => true | x :: xs, y :: ys => tyEq x y && listTyEq xs ys | _, _ => false

def natDigits : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc := Char.ofNat (48 + n % 10) :: acc
    if Nat.ble 10 n then natDigits fuel (n / 10) acc else acc

def lname (fn : Sym) (n : Nat) : Sym := fn ++ ".L" ++ String.ofList (natDigits (n + 1) n [])

def isGprTy (I : Isa) : Ty → Bool
  | .bool => true | .bits n => I.frame.bitWidths.contains n && Nat.ble n 64 | _ => false

def vecWidth? (I : Isa) : Ty → Option SlotWidth
  | .pair a b =>
    match I.vec.vecSlotWidth (.pair a b) with
    | some w => if Nat.ble (Ty.pair a b).size w.bits then some w else none
    | none => none
  | _ => none

def isAllocGpr (I : Isa) (saved : List I.Reg) (r : I.Reg) : Bool :=
  I.frame.allocatable.contains r || saved.contains r ||
    I.frame.argRegs.contains r || I.frame.retRegs.contains r

def isMoveGpr (I : Isa) (saved : List I.Reg) (r : I.Reg) : Bool :=
  isAllocGpr I saved r || I.frame.scratch.contains r

def isAllocVec (I : Isa) (v : I.VReg) : Bool :=
  I.vec.vecAllocatable.contains v || I.vec.vecArgRegs.contains v || I.vec.vecRetRegs.contains v

def isMoveVec (I : Isa) (v : I.VReg) : Bool := isAllocVec I v || I.vec.vecScratch.contains v

def toSymArg (I : Isa) : (t : Ty) → Arg VNat t → Option SymArg
  | _, .var x => some (.var x)
  | .bool, .imm b => some (.immBool b)
  | .bits n, .imm c => if Nat.ble n 64 then some (.immBits n (c.setWidth 64)) else none
  | .pair a b, .imm c =>
    (vecWidth? I (.pair a b)).map fun w => .immVec w ((toBits (.pair a b) c).setWidth 512)
  | .float _, .imm _ => none

def symArgWidth (vw : Trie SlotWidth) : SymArg → Option SlotWidth
  | .var x => vw.find? x | .immVec w _ => some w | _ => none

def symArgMatchesGpr (stored target : SymArg) : Bool :=
  if symArgEq stored target then true
  else match stored, target with
    | .immBits w' c, .immBits w k => Nat.beq w' 64 && Nat.ble w 64 && c == k
    | .immBits w' c, .immBool b => Nat.beq w' 64 && c == (if b then 1#64 else 0#64)
    | _, _ => false

def symArgScopeOk (nv : Nat) : SymArg → Bool
  | .var x => Nat.ble (x + 1) nv | _ => true

def entryScopeOk {I : Isa} (nv : Nat) (en : Entry I.Reg I.VReg I.Cond) : Bool :=
  en.live.all fun (sa, _) => symArgScopeOk nv sa

/-! ## Generic Kill Rule (`L5`) and Multi-Granule Slot Updates (`L10`) -/

def keepRegLoc (I : Isa) (gClob : List I.Reg) (vClob : List I.VReg) (fClob : FlagMask) :
    RegLoc I.Reg I.VReg I.Cond → Bool
  | .gpr r => !(gClob.contains r)
  | .vec v => !(vClob.contains v)
  | .flag c => FlagMask.disjoint (I.gpr.condReads c) fClob

def killRegs (I : Isa) (gClob : List I.Reg) (vClob : List I.VReg) (fClob : FlagMask)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) :
    List (SymArg × RegLoc I.Reg I.VReg I.Cond) :=
  R.filter fun p => keepRegLoc I gClob vClob fClob p.2

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

/-! ## Checked Moves and `PreStep` (`L3`, `L4`, `L7`, `L10`) -/

def gprEntries {I : Isa} (r : I.Reg) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : List SymArg :=
  R.filterMap fun (sa, rl) => match rl with | .gpr r' => if r' == r then some sa else none | _ => none

def vecEntries {I : Isa} (vw : Trie SlotWidth) (w : SlotWidth) (v : I.VReg)
    (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : List SymArg :=
  R.filterMap fun (sa, rl) =>
    match rl with
    | .vec v' =>
      if v' == v then
        match symArgWidth vw sa with | some wsa => if Nat.ble wsa.bits w.bits then some sa else none | none => none
      else none
    | _ => none

def flagEntries {I : Isa} (c : I.Cond) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : List SymArg :=
  R.filterMap fun (sa, rl) => match rl with | .flag c' => if c' == c then some sa else none | _ => none

def execMove (I : Isa) (nslots : Nat) (saved : List I.Reg) (mv : I.Move) (st : SymState I) :
    Option (List I.Directive × SymState I) :=
  match mv with
  | .mov d s =>
    if !isMoveGpr I saved d then none
    else if d == s then some (I.gpr.mov d s, st)
    else some (I.gpr.mov d s,
      { st with regs := (gprEntries s st.regs).map (·, .gpr d) ++ killRegs I [d] [] FlagMask.none st.regs })
  | .movi d c =>
    if !isMoveGpr I saved d then none
    else some (I.gpr.movi d c,
      { st with regs := (.immBits 64 c, .gpr d) :: killRegs I (d :: I.frame.scratch) [] FlagMask.none st.regs })
  | .ld d i =>
    if !(isAllocGpr I saved d && Nat.ble (i + 1) nslots) then none
    else
      let copied := match st.slots.find? i with | some (.gpr sas) => sas.map (·, .gpr d) | _ => []
      some (I.frame.slotLd d i,
        { st with regs := copied ++ killRegs I (d :: I.frame.scratch) [] FlagMask.none st.regs })
  | .st i s =>
    if !(!(I.frame.scratch.contains s) && Nat.ble (i + 1) nslots) then none
    else some (I.frame.slotSt i s,
      { st with regs := killRegs I I.frame.scratch [] FlagMask.none st.regs,
                slots := (clearSlotRange i 1 st.slots).insert i (.gpr (gprEntries s st.regs)) })
  | .setcc d c =>
    if !isAllocGpr I saved d then none
    else some (I.gpr.setcc d c,
      { st with regs := (flagEntries c st.regs).map (·, .gpr d) ++
                        killRegs I (d :: I.frame.scratch) [] FlagMask.none st.regs })
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
          { st with regs := (.immVec w c, .vec d) ::
                            killRegs I I.frame.scratch (d :: I.vec.vecScratch) FlagMask.none st.regs })
  | .vld w d i =>
    if !(isAllocVec I d && Nat.ble (i + w.slots) nslots) then none
    else
      let copied := match st.slots.find? i with
        | some (.vec w' sas) => if slotWidthEq w' w then sas.map (·, .vec d) else [] | _ => []
      some (I.vec.vslotLd w d i,
        { st with regs := copied ++ killRegs I I.frame.scratch (d :: I.vec.vecScratch) FlagMask.none st.regs })
  | .vst w i s =>
    if !(!(I.vec.vecScratch.contains s) && Nat.ble (i + w.slots) nslots) then none
    else some (I.vec.vslotSt w i s,
      { st with regs := killRegs I I.frame.scratch I.vec.vecScratch FlagMask.none st.regs,
                slots := (clearSlotRange i w.slots st.slots).insert i (.vec w (vecEntries st.vecWidths w s st.regs)) })

def execMoves (I : Isa) (nslots : Nat) (saved : List I.Reg) :
    List I.Move → SymState I → Option (List I.Directive × SymState I)
  | [], st => some ([], st)
  | mv :: mvs, st => (execMove I nslots saved mv st).bind fun (c1, st1) =>
      (execMoves I nslots saved mvs st1).map fun (c2, st2) => (c1 ++ c2, st2)

def execClearFlags (I : Isa) (st : SymState I) : List I.Directive × SymState I :=
  (I.gpr.clearFlags, { st with regs := I.gpr.zeroFlags.map (.immBool false, .flag ·) ++
                                       killRegs I I.frame.scratch [] FlagMask.all st.regs })

def stepPre (I : Isa) (h : I.Hints) (ip : Nat) (st : SymState I) : Option (List I.Directive × SymState I) :=
  match h.pre.find? ip with
  | none => some ([], st)
  | some ps => (execMoves I h.nslots h.saved ps.moves st).map fun (mc, st1) =>
      if ps.clearFlags then let (cc, st2) := execClearFlags I st1; (mc ++ cc, st2) else (mc, st1)

/-! ## Target Presence Checking and Untrusted Parallel-Move Shuffle -/

def holdsLoc (I : Isa) (st : SymState I) (sa : SymArg) : I.Loc → Bool
  | .gpr r => st.regs.any fun (sa', rl) => match rl with | .gpr r' => r' == r && symArgMatchesGpr sa' sa | _ => false
  | .vec v => st.regs.any fun (sa', rl) => match rl with | .vec v' => v' == v && symArgEq sa' sa | _ => false
  | .flag c => st.regs.any fun (sa', rl) => match rl with | .flag c' => c' == c && symArgEq sa' sa | _ => false
  | .slot i w =>
    match symArgWidth st.vecWidths sa with
    | some wsa =>
      Nat.ble wsa.bits w.bits &&
      match st.slots.find? i with | some (.vec w' sas) => slotWidthEq w' w && sas.any (symArgEq · sa) | _ => false
    | none =>
      slotWidthEq w .w64 &&
      match st.slots.find? i with | some (.gpr sas) => sas.any (symArgMatchesGpr · sa) | _ => false

def findGprFor (I : Isa) (noScr : Bool) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (sa : SymArg) : Option I.Reg :=
  R.findSome? fun (sa', rl) =>
    match rl with | .gpr r => if (!noScr || !(I.frame.scratch.contains r)) && symArgMatchesGpr sa' sa then some r else none | _ => none

def findVecFor (I : Isa) (noScr : Bool) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (sa : SymArg) : Option I.VReg :=
  R.findSome? fun (sa', rl) =>
    match rl with | .vec v => if (!noScr || !(I.vec.vecScratch.contains v)) && symArgEq sa' sa then some v else none | _ => none

def findFlagFor (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (sa : SymArg) : Option I.Cond :=
  R.findSome? fun (sa', rl) => match rl with | .flag c => if symArgEq sa' sa then some c else none | _ => none

def findSlotFor (nslots : Nat) (slots : Trie SlotEntry) (sa : SymArg) : Option (Nat × SlotWidth) :=
  let rec go (i : Nat) : Nat → Option (Nat × SlotWidth)
    | 0 => none
    | fuel + 1 =>
      match slots.find? i with
      | some (.gpr sas) => if sas.any (symArgMatchesGpr · sa) then some (i, .w64) else go (i + 1) fuel
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

def isVarSymArg : SymArg → Bool | .var _ => true | _ => false

def locBlocked (I : Isa) (st : SymState I) (pend : List (SymArg × I.Loc)) (d : I.Loc) : Bool :=
  pend.any fun (sa, d') =>
    !(locEq d' d) && isVarSymArg sa &&
    match d with
    | .gpr r =>
      st.regs.all (fun (sa', rl) => !symArgEq sa' sa || regLocEq rl (.gpr r)) &&
      st.regs.any (fun (sa', rl) => symArgEq sa' sa && regLocEq rl (.gpr r))
    | .vec v =>
      st.regs.all (fun (sa', rl) => !symArgEq sa' sa || regLocEq rl (.vec v)) &&
      st.regs.any (fun (sa', rl) => symArgEq sa' sa && regLocEq rl (.vec v))
    | _ => false

def rangesOverlap (i1 k1 i2 k2 : Nat) : Bool := Nat.ble (i1 + 1) (i2 + k2) && Nat.ble (i2 + 1) (i1 + k1)

def slotBusy (I : Isa) (st : SymState I) (pend : List (SymArg × I.Loc)) (i k : Nat) : Bool :=
  pend.any (fun (_, loc) => match loc with | .slot j w => rangesOverlap i k j w.slots | _ => false) ||
  let rec scan (j : Nat) : Nat → Bool
    | 0 => false
    | fuel + 1 =>
      (match st.slots.find? j with | some se => rangesOverlap i k j se.slots | none => false) ||
      scan (j + 1) fuel
  scan (i - 7) (k + 7)

def findFreeSlot (I : Isa) (nslots : Nat) (st : SymState I) (pend : List (SymArg × I.Loc)) (k : Nat) : Option Nat :=
  let rec go (i : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 => if Nat.ble (i + k) nslots && !(slotBusy I st pend i k) then some i else go (i + 1) fuel
  go 0 nslots

def maxSlotWidth (a b : SlotWidth) : SlotWidth := if Nat.ble a.bits b.bits then b else a

def vecWidthAt (I : Isa) (st : SymState I) (vd : I.VReg) : SlotWidth :=
  st.regs.foldl (fun w (sa, rl) => match rl with
    | .vec v => if v == vd then match symArgWidth st.vecWidths sa with | some ws => maxSlotWidth w ws | none => w else w
    | _ => w) .w64

def pmoveAux (I : Isa) (nslots : Nat) (saved : List I.Reg) :
    Nat → SymState I → List (SymArg × I.Loc) → List I.Move → List I.Move
  | 0, _, _, acc => acc.reverse
  | fuel + 1, st, targets, acc =>
    match targets.filter fun (sa, loc) => !holdsLoc I st sa loc with
    | [] => acc.reverse
    | pend =>
      let goMv (mv : I.Move) : List I.Move :=
        match execMove I nslots saved mv st with
        | some (_, st') => pmoveAux I nslots saved fuel st' pend (mv :: acc)
        | none => acc.reverse
      let step (sa : SymArg) (loc : I.Loc) : List I.Move :=
        match moveFor I nslots st sa loc with | some mv => goMv mv | none => acc.reverse
      match pend.find? fun (sa, loc) => isVarSymArg sa && !(locBlocked I st pend loc) with
      | some (sa, loc) => step sa loc
      | none =>
        match pend.find? fun (sa, loc) => isVarSymArg sa && match loc with | .gpr _ => true | _ => false with
        | some (_, .gpr d) =>
          match I.frame.scratch.find? fun tmp => !(locBlocked I st pend (.gpr tmp)) with
          | some tmp => goMv (.mov tmp d)
          | none =>
            match findFreeSlot I nslots st pend 1 with
            | some sl => if !(I.frame.scratch.contains d) then goMv (.st sl d) else acc.reverse
            | none => acc.reverse
        | _ =>
          match pend.find? fun (sa, loc) => isVarSymArg sa && match loc with | .vec _ => true | _ => false with
          | some (_, .vec vd) =>
            let w := vecWidthAt I st vd
            match I.vec.vecScratch.find? fun vtmp => !(locBlocked I st pend (.vec vtmp)) with
            | some vtmp => goMv (.vmov w vtmp vd)
            | none =>
              match findFreeSlot I nslots st pend w.slots with
              | some sl => if !(I.vec.vecScratch.contains vd) then goMv (.vst w sl vd) else acc.reverse
              | none => acc.reverse
          | _ => match pend.head? with | some (sa, loc) => step sa loc | none => acc.reverse

def shuffle (I : Isa) (nslots : Nat) (saved : List I.Reg) (st : SymState I)
    (tgts : List (SymArg × I.Loc)) : Option (List I.Directive × SymState I) :=
  if tgts.all fun (sa, loc) => holdsLoc I st sa loc then some ([], st)
  else
    let mvs := pmoveAux I nslots saved (2 * tgts.length + 4) st tgts []
    match execMoves I nslots saved mvs st with
    | none => none
    | some (code, st') => if tgts.all fun (sa, loc) => holdsLoc I st' sa loc then some (code, st') else none

/-! ## ABI Helpers, `L9` Defs, and Operand/Destination Resolution -/

def abiTargets (I : Isa) :
    {ts : List Ty} → Tup (Arg VNat) ts → Tup (AbiReg I.Reg I.VReg) ts → Option (List (SymArg × I.Loc))
  | [], (), () => some []
  | t :: _, (a, as), (loc, locs) =>
    match toSymArg I t a, abiTargets I as locs with
    | some sa, some rest => some ((sa, match loc with | .gpr r => .gpr r | .vec v => .vec v) :: rest)
    | _, _ => none

def canonAbiCode (I : Isa) : {ts : List Ty} → Tup (AbiReg I.Reg I.VReg) ts → List I.Directive
  | [], () => []
  | t :: _, (.gpr r, locs) => (I.frame.canonAbi t r).1 ++ canonAbiCode I locs
  | _ :: _, (.vec _, locs) => canonAbiCode I locs

def saveCs (I : Isa) (base : Nat) : List I.Reg → List I.Directive
  | [] => [] | r :: rs => I.frame.slotSt base r ++ saveCs I (base + 1) rs

def restoreCs (I : Isa) (base : Nat) : List I.Reg → List I.Directive
  | [] => [] | r :: rs => I.frame.slotLd r base ++ restoreCs I (base + 1) rs

def recordDef : {sig rs : List Ty} → OpCode sig rs → Tup (Arg VNat) sig → Option DefFact
  | _, _, .add (.bits n), (a, b, ()) =>
    if !Nat.beq n 64 then none else match a, b with
      | .var x, .imm c | .imm c, .var x => some (.addImm64 x (c.setWidth 64))
      | _, _ => none
  | _, _, .sub (.bits n), (.var x, .imm c, ()) =>
    if Nat.beq n 64 then some (.addImm64 x (-(c.setWidth 64))) else none
  | _, _, .copy (.bits n), (.imm c, ()) =>
    if Nat.beq n 64 then some (.imm64 (c.setWidth 64)) else none
  | _, _, _, _ => none

def tupDstFlags {I : Isa} : {ts : List Ty} → Tup (PDst I.Reg I.VReg I.Cond) ts → List I.Cond
  | [], () => [] | _ :: _, (.flag c, ds) => c :: tupDstFlags ds | _ :: _, (_, ds) => tupDstFlags ds

def resolveDsts (I : Isa) (h : I.Hints) : (ts : List Ty) → Nat → Option (Tup (PDst I.Reg I.VReg I.Cond) ts)
  | [], _ => some ()
  | t :: ts, nv =>
    match h.dest.find? nv, resolveDsts I h ts (nv + 1) with
    | some (.gpr r), some rest => if isAllocGpr I h.saved r && isGprTy I t then some (.gpr r, rest) else none
    | some (.vec v), some rest => if isAllocVec I v && (vecWidth? I t).isSome then some (.vec v, rest) else none
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
  (R.findSome? fun (sa', rl) => match rl with | .flag c => if symArgEq sa' sa then k c else none | _ => none)

def tryGpr (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) {α : Type}
    (sa : SymArg) (k : I.Reg → Option α) : Option α :=
  R.findSome? fun (sa', rl) =>
    match rl with | .gpr r => if !(I.frame.scratch.contains r) && symArgMatchesGpr sa' sa then k r else none | _ => none

def tryVec (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) {α : Type}
    (sa : SymArg) (k : I.VReg → Option α) : Option α :=
  R.findSome? fun (sa', rl) =>
    match rl with | .vec v => if !(I.vec.vecScratch.contains v) && symArgEq sa' sa then k v else none | _ => none

def tryArg (I : Isa) (st : SymState I) (pref : List I.Cond) {α : Type}
    (t : Ty) (a : Arg VNat t) (k : PArg I.Reg I.VReg I.Cond t → Option α) : Option α :=
  match t, a with
  | .bool, .var x => tryFlag I st.regs pref (.var x) (k ∘ .flag) <|> tryGpr I st.regs (.var x) (k ∘ .gpr)
  | .bool, .imm b =>
    tryFlag I st.regs pref (.immBool b) (k ∘ .flag) <|> k (.imm b) <|> tryGpr I st.regs (.immBool b) (k ∘ .gpr)
  | .bits _, .var x => tryGpr I st.regs (.var x) (k ∘ .gpr)
  | .bits n, .imm c =>
    k (.imm c) <|> if Nat.ble n 64 then tryGpr I st.regs (.immBits n (c.setWidth 64)) (k ∘ .gpr) else none
  | .pair _ _, .var x => tryVec I st.regs (.var x) (k ∘ .vec)
  | .pair a b, .imm c =>
    k (.imm c) <|> match vecWidth? I (.pair a b) with
      | none => none | some w => tryVec I st.regs (.immVec w ((toBits (.pair a b) c).setWidth 512)) (k ∘ .vec)
  | .float _, _ => none

def pickPArgs (I : Isa) (st : SymState I) (pref : List I.Cond) {α : Type} :
    {sig : List Ty} → Tup (Arg VNat) sig → (Tup (PArg I.Reg I.VReg I.Cond) sig → Option α) → Option α
  | [], (), k => k ()
  | t :: _, (a, as), k => tryArg I st pref t a fun pa => pickPArgs I st pref as fun pas => k (pa, pas)

def lowerOp (I : Isa) (h : I.Hints) (nv ip : Nat) (st1 : SymState I) {ts : List Ty}
    (op : Op VNat ts) : Option (List I.Directive × SymState I) :=
  if h.elide.getD ip false then
    match recordDef op.code op.args with
    | some df => some ([], { st1 with defs := st1.defs.insert nv df })
    | none => none
  else
    (resolveDsts I h ts nv).bind fun dsts =>
      let vh := h.variant.getD ip .default
      let dstGprs := tupDstGprs dsts; let dstVecs := tupDstVecs dsts
      (pickPArgs I st1 (tupDstFlags dsts) op.args fun pas =>
        if dstVecs.isEmpty && (tupArgVecs pas).isEmpty then
          ((I.gpr.op op.code pas dsts vh).map fun (c, cl) => (c, cl, false)) <|>
          ((I.vec.vop op.code pas dsts vh).map fun (c, cl) => (c, cl, true))
        else (I.vec.vop op.code pas dsts vh).map fun (c, cl) =>
          (c, cl, true)).map fun (code, clob, isVec) =>
          let vClob := if isVec then dstVecs ++ I.vec.vecScratch else []
          let killed := killRegs I (dstGprs ++ I.frame.scratch) vClob clob st1.regs
          let (regs1, vw1) := bindDsts I dsts nv (killed, st1.vecWidths)
          let defs1 := match recordDef op.code op.args with
            | some df => st1.defs.insert nv df
            | none => st1.defs
          (code, { regs := regs1, slots := st1.slots, defs := defs1, vecWidths := vw1 })

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
      match st.defs.find? x with
      | some (.addImm64 base d) =>
        (findGprFor I true st.regs (.var base)).bind fun rb =>
          k (.baseDisp rb (Int64.ofBitVec d))
      | some (.imm64 c) => k (.imm c)
      | _ => none

/-! ## Block Entry, Jumps, and Core PHOAS Lowering -/

def buildEntryBase (I : Isa) (nslots : Nat) (vw : Trie SlotWidth) :
    List (SymArg × I.Loc) → SymState I → Option (SymState I)
  | [], st => some st
  | (sa, .gpr r) :: rest, st =>
    if !(I.frame.scratch.contains r) then buildEntryBase I nslots vw rest { st with regs := (sa, .gpr r) :: st.regs } else none
  | (sa, .vec v) :: rest, st =>
    if !(I.vec.vecScratch.contains v) && (symArgWidth vw sa).isSome then
      buildEntryBase I nslots vw rest { st with regs := (sa, .vec v) :: st.regs } else none
  | (sa, .flag c) :: rest, st => buildEntryBase I nslots vw rest { st with regs := (sa, .flag c) :: st.regs }
  | (sa, .slot i w) :: rest, st =>
    if !Nat.ble (i + w.slots) nslots then none
    else (addSlotEntry vw sa i w st.slots).bind fun slots' => buildEntryBase I nslots vw rest { st with slots := slots' }

def bindBlockParams (I : Isa) (nslots : Nat) :
    (ts : List Ty) → List I.Loc → Nat → SymState I → Option (SymState I)
  | [], [], _, st => some st
  | t :: ts, loc :: locs, nv, st =>
    match loc with
    | .gpr r =>
      if !(I.frame.scratch.contains r) && isGprTy I t then
        bindBlockParams I nslots ts locs (nv + 1) { st with regs := (.var nv, .gpr r) :: st.regs } else none
    | .vec v => (vecWidth? I t).bind fun w =>
      if !(I.vec.vecScratch.contains v) then
        bindBlockParams I nslots ts locs (nv + 1) { st with regs := (.var nv, .vec v) :: st.regs, vecWidths := st.vecWidths.insert nv w }
      else none
    | .flag c => match t with
      | .bool => bindBlockParams I nslots ts locs (nv + 1) { st with regs := (.var nv, .flag c) :: st.regs }
      | _ => none
    | .slot i w =>
      if !(Nat.ble (i + w.slots) nslots && (isGprTy I t || (vecWidth? I t).isSome)) then none
      else
        let vw' := match vecWidth? I t with | some wt => st.vecWidths.insert nv wt | none => st.vecWidths
        (addSlotEntry vw' (.var nv) i w st.slots).bind fun slots' =>
          bindBlockParams I nslots ts locs (nv + 1) { st with slots := slots', vecWidths := vw' }
  | _, _, _, _ => none

def bindAbiParams (I : Isa) : {ts : List Ty} → Tup (AbiReg I.Reg I.VReg) ts → Nat → SymState I → Option (SymState I)
  | [], (), _, st => some st
  | t :: _, (.gpr r, locs), nv, st =>
    if isGprTy I t then bindAbiParams I locs (nv + 1) { st with regs := (.var nv, .gpr r) :: st.regs } else none
  | t :: _, (.vec v, locs), nv, st => (vecWidth? I t).bind fun w =>
    bindAbiParams I locs (nv + 1) { st with regs := (.var nv, .vec v) :: st.regs, vecWidths := st.vecWidths.insert nv w }

def jumpTargets (I : Isa) : {ts : List Ty} → Tup (Arg VNat) ts → List I.Loc → Option (List (SymArg × I.Loc))
  | [], (), [] => some []
  | t :: _, (a, as), loc :: locs =>
    match toSymArg I t a, jumpTargets I as locs with | some sa, some rest => some ((sa, loc) :: rest) | _, _ => none
  | _, _, _ => none

def jumpLocOk (I : Isa) (nslots : Nat) : I.Loc → Bool
  | .gpr r => !(I.frame.scratch.contains r) | .vec v => !(I.vec.vecScratch.contains v)
  | .flag _ => true | .slot i w => Nat.ble (i + w.slots) nslots

def afterCallState (I : Isa) (saved : List I.Reg) (st : SymState I) : SymState I :=
  { st with regs := st.regs.filter fun (_, rl) => match rl with | .gpr r => saved.contains r | _ => false }
def calleeAllowed (E : Ext) (f : Sym) (as bs : List Ty) : Bool :=
  E.callees.any fun (g, gas, gbs) => g == f && listTyEq gas as && listTyEq gbs bs
def prepend {I : Isa} (pre : List I.Directive) : Res I → Res I
  | .ok (c, nv, nl, ip) => .ok (pre ++ c, nv, nl, ip) | .error e => .error e
def findJnzCond (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (x : Nat) : Option (Sum I.Cond I.Reg) :=
  (findFlagFor I R (.var x)).map .inl <|> (findGprFor I true R (.var x)).map .inr

def zeroMoveJump? {rs : List Ty} (I : Isa) (h : I.Hints) (st : SymState I) : Expr VNat LNat rs → Option Nat
  | .jump j args => (h.entry.find? j).bind fun en => (jumpTargets I args en.ploc).bind fun argTgts =>
      if (en.live ++ argTgts).all (fun (sa, loc) => jumpLocOk I h.nslots loc && holdsLoc I st sa loc) then some j else none
  | _ => none

def jnzMode {rs : List Ty} (I : Isa) (h : I.Hints) (st : SymState I)
    (canInv : Bool) (t e : Expr VNat LNat rs) (ft : Option Nat) : Bool × Option Nat :=
  match zeroMoveJump? I h st t, if canInv then zeroMoveJump? I h st e else none with
  | some jt, some je => if ft == some jt then (true, some je) else (false, some jt)
  | some jt, none => (false, some jt) | none, some je => (true, some je) | none, none => (false, none)

def gprThread? {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (st1 : SymState I) (r : I.Reg) :
    Expr VNat LNat rs → Option Nat
  | .jump j args =>
    zeroMoveJump? (rs := rs) I h
      { st1 with regs := killRegs I I.frame.scratch [] (I.gpr.jnzGpr r (lname fn j)).2 st1.regs } (.jump j args)
  | _ => none

/-- Branch selection for `jnz`: `(inverted?, threaded target, branch code, state after branch)`. -/
def jnzSetup {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl : Nat) (st1 : SymState I)
    (t e : Expr VNat LNat rs) (ft : Option Nat) :
    Sum I.Cond I.Reg → Bool × Option Nat × List I.Directive × SymState I
  | .inl cc =>
    let stB := { st1 with regs := killRegs I I.frame.scratch [] FlagMask.none st1.regs }
    let p := jnzMode I h stB true t e ft
    (p.1, p.2, I.gpr.jcc (if p.1 then I.gpr.negCond cc else cc) (lname fn (p.2.getD nl)), stB)
  | .inr r =>
    let tg := gprThread? I h fn st1 r t
    let p := I.gpr.jnzGpr r (lname fn (tg.getD nl))
    (false, tg, p.1, { st1 with regs := killRegs I I.frame.scratch [] p.2 st1.regs })

def finishJnzBranch {rs : List Ty} (I : Isa) (fn : Sym) (nl : Nat) (tgt? : Option Nat)
    (b_taken : Expr VNat LNat rs) (br c_ft c_taken : List I.Directive) (nv2 nl2 ip2 : Nat) : Res I :=
  match tgt? with
  | some j => match b_taken with
    | .jump j' _ => if Nat.beq j' j && c_taken.isEmpty then .ok (br ++ c_ft, nv2, nl2, ip2) else .error "jnz: bad thread"
    | _ => .error "jnz: not jump"
  | none => .ok (br ++ c_ft ++ [I.frame.label (lname fn nl)] ++ c_taken, nv2, nl2, ip2)

def lowerStore (I : Isa) (st1 : SymState I) (vh : VariantHint) :
    (t : Ty) → Arg VNat t → Arg VNat i64 → Option (List I.Directive × SymState I)
  | .pair a b, v, addr =>
    (tryArg I st1 [] (.pair a b) v fun pa =>
      match pa with | .vec vs => tryAddr I st1 vh addr (I.vec.vstore (.pair a b) vs) | _ => none).map fun (c, clob) =>
      (c, { st1 with regs := killRegs I I.frame.scratch I.vec.vecScratch clob st1.regs })
  | t, v, addr =>
    if !isGprTy I t then none
    else (tryArg I st1 [] t v fun pa => tryAddr I st1 vh addr (I.gpr.store t pa)).map fun (c, clob) =>
      (c, { st1 with regs := killRegs I I.frame.scratch [] clob st1.regs })

def lowerLoad (I : Isa) (h : I.Hints) (nv ip : Nat) (st1 : SymState I) (t : Ty) (a : Arg VNat i64) :
    Option (List I.Directive × SymState I) :=
  let vh := h.variant.getD ip .default
  match h.dest.find? nv with
  | some (.gpr d) =>
    if !(isAllocGpr I h.saved d && isGprTy I t) then none
    else (tryAddr I st1 vh a (I.gpr.load t d)).map fun (c, clob) =>
      (c, { st1 with regs := (.var nv, .gpr d) :: killRegs I (d :: I.frame.scratch) [] clob st1.regs })
  | some (.vec vd) => (vecWidth? I t).bind fun w =>
    if !isAllocVec I vd then none
    else (tryAddr I st1 vh a (I.vec.vload t vd)).map fun (c, clob) =>
      (c, { st1 with regs := (.var nv, .vec vd) :: killRegs I I.frame.scratch (vd :: I.vec.vecScratch) clob st1.regs,
                     vecWidths := st1.vecWidths.insert nv w })
  | _ => none

def lowerTail {ts : List Ty} (I : Isa) (h : I.Hints) (st1 : SymState I) (mc tail : List I.Directive)
    (args : Tup (Arg VNat) ts) (locs : Tup (AbiReg I.Reg I.VReg) ts) (nv nl ip : Nat) : Res I :=
  match abiTargets I args locs with
  | none => .error "tail: imm"
  | some tgts => match shuffle I h.nslots h.saved st1 tgts with
    | none => .error "tail: shuffle"
    | some (sc, _) =>
      .ok (mc ++ sc ++ canonAbiCode I locs ++ restoreCs I h.nslots h.saved ++
        (I.frame.epilogue h.totalSlots).1 ++ tail, nv, nl, ip + 1)

mutual
def lowerExpr (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    Expr VNat LNat rs → Nat → Nat → Nat → SymState I → Option Nat → Res I
  | .let_ (ts := ts) op k, nv, nl, ip, st, ft =>
    match stepPre I h ip st with
    | none => .error "let: pre"
    | some (mc, st1) => match lowerOp I h nv ip st1 op with
      | none => .error "let: op"
      | some (c, st2) => prepend (mc ++ c) (lowerExpr I h E fn (k (Tup.levels ts nv)) (nv + ts.length) nl (ip + 1) st2 ft)
  | .load t a k, nv, nl, ip, st, ft =>
    match stepPre I h ip st with
    | none => .error "load: pre"
    | some (mc, st1) => match lowerLoad I h nv ip st1 t a with
      | none => .error "load: dst/addr"
      | some (c, st2) => prepend (mc ++ c) (lowerExpr I h E fn (k nv) (nv + 1) nl (ip + 1) st2 ft)
  | .store (t := t) v a k, nv, nl, ip, st, ft =>
    match stepPre I h ip st with
    | none => .error "store: pre"
    | some (mc, st1) => match lowerStore I st1 (h.variant.getD ip .default) t v a with
      | none => .error "store: op/addr"
      | some (c, st2) => prepend (mc ++ c) (lowerExpr I h E fn k nv nl (ip + 1) st2 ft)
  | .call f (as := as) (bs := bs) args k, nv, nl, ip, st, ft =>
    match stepPre I h ip st with
    | none => .error "call: pre"
    | some (mc, st1) =>
      if !calleeAllowed E f as bs then .error "call: callee"
      else match I.assignArgs as, I.assignRets bs with
        | some argLocs, some retLocs => match abiTargets I args argLocs with
          | none => .error "call: imm"
          | some tgts => match shuffle I h.nslots h.saved st1 tgts with
            | none => .error "call: shuffle"
            | some (sc, st2) => match bindAbiParams I retLocs nv (afterCallState I h.saved st2) with
              | none => .error "call: ret bind"
              | some st4 =>
                prepend (mc ++ sc ++ canonAbiCode I argLocs ++ I.frame.call f)
                  (lowerExpr I h E fn (k (Tup.levels bs nv)) (nv + bs.length) nl (ip + 1) st4 ft)
        | _, _ => .error "call: abi"
  | .jnz (.imm b) t e, nv, nl, ip, st, ft =>
    match stepPre I h ip st with
    | none => .error "jnz: pre"
    | some (mc, st1) =>
      prepend mc (if b then lowerExpr I h E fn t nv nl (ip + 1) st1 ft else lowerExpr I h E fn e nv nl (ip + 1) st1 ft)
  | .jnz (.var cx) t e, nv, nl, ip, st, ft =>
    match stepPre I h ip st with
    | none => .error "jnz: pre"
    | some (mc, st1) => match findJnzCond I st1.regs cx with
      | none => .error "jnz: cond"
      | some cond =>
        let (inv, tgt?, br, stBr) := jnzSetup I h fn nl st1 t e ft cond
        let ftT := match tgt? with | some j => some j | none => ft
        let ftF := match tgt? with | some _ => ft | none => none
        match lowerExpr I h E fn e nv (nl + 1) (ip + 1) stBr (if inv then ftT else ftF) with
        | .error err => .error err
        | .ok (ce, nv1, nl1, ip1) => match lowerExpr I h E fn t nv1 nl1 ip1 stBr (if inv then ftF else ftT) with
          | .error err => .error err
          | .ok (ct, nv2, nl2, ip2) =>
            prepend mc (if inv then finishJnzBranch I fn nl tgt? e br ct ce nv2 nl2 ip2
                        else finishJnzBranch I fn nl tgt? t br ce ct nv2 nl2 ip2)
  | .jump j args, nv, nl, ip, st, ft =>
    match stepPre I h ip st, h.entry.find? j with
    | some (mc, st1), some en => match jumpTargets I args en.ploc with
      | none => .error "jump: arity"
      | some argTgts =>
        let tgts := en.live ++ argTgts
        if !(tgts.all fun (_, loc) => jumpLocOk I h.nslots loc) then .error "jump: loc"
        else match shuffle I h.nslots h.saved st1 tgts with
          | none => .error "jump: shuffle"
          | some (sc, _) => .ok (mc ++ sc ++ (if ft == some j then [] else I.gpr.jmp (lname fn j)), nv, nl, ip + 1)
    | _, _ => .error "jump: pre/entry"
  | .ret vs, nv, nl, ip, st, _ =>
    match stepPre I h ip st, I.assignRets rs with
    | some (mc, st1), some retLocs => lowerTail I h st1 mc I.frame.ret vs retLocs nv nl ip
    | _, _ => .error "ret: pre/abi"
  | .exit f (as := as) args, nv, nl, ip, st, _ =>
    match stepPre I h ip st, I.assignArgs as with
    | some (mc, st1), some argLocs =>
      if !E.exits.contains f then .error "exit: target"
      else lowerTail I h st1 mc (I.frame.exitJmp f) args argLocs nv nl ip
    | _, _ => .error "exit: pre/abi"
  | .hlt, nv, nl, ip, _, _ => .ok ([], nv, nl, ip + 1)
  | .group (sig := sig) bodies k, nv, nl, ip, st, ft =>
    let ls := Tup.levels sig nl
    let ftK := match sig with | [] => ft | _ :: _ => some nl
    match lowerExpr I h E fn (k ls) nv (nl + sig.length) ip st ftK with
    | .error err => .error err
    | .ok (ck, nv1, nl1, ip1) => prepend ck (lowerBlocks I h E fn (bodies ls) nl nv1 nl1 ip1 st.defs st.vecWidths ft)

def lowerBlocks (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig →
    Nat → Nat → Nat → Nat → Trie DefFact → Trie SlotWidth → Option Nat → Res I
  | _, .nil, _, nv, nl, ip, _, _, _ => .ok ([], nv, nl, ip)
  | _, .cons (ts := ts) b bs, lid, nv, nl, ip, defs, vw, ft =>
    match h.entry.find? lid with
    | none => .error "block: entry"
    | some en =>
      if !entryScopeOk nv en then .error "block: scope"
      else match buildEntryBase I h.nslots vw en.live ⟨[], .empty, defs, vw⟩ with
        | none => .error "block: live"
        | some baseSt => match bindBlockParams I h.nslots ts en.ploc nv baseSt with
          | none => .error "block: plocs"
          | some initSt =>
            let ftB := match bs with | .nil => ft | .cons _ _ => some (lid + 1)
            match lowerExpr I h E fn (b (Tup.levels ts nv)) (nv + ts.length) nl ip initSt ftB with
            | .error err => .error err
            | .ok (cb, nv1, nl1, ip1) =>
              prepend (I.frame.label (lname fn lid) :: cb) (lowerBlocks I h E fn bs (lid + 1) nv1 nl1 ip1 defs vw ft)
end

def lowerFn (I : Isa) (h : I.Hints) (E : Ext) (f : Fn) : Except String (List I.Directive) :=
  if !(listNodup h.saved && h.saved.all (I.frame.calleeSaved.contains ·)) then .error "fn: saved"
  else match I.assignArgs f.as, I.assignRets f.rs with
    | some argLocs, some _ => match bindAbiParams I argLocs 0 ⟨[], .empty, .empty, .empty⟩ with
      | none => .error "fn: abi bind"
      | some st0 => match lowerExpr I h E f.name (f.body VNat LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none with
        | .ok (c, _, _, _) => .ok (I.frame.label f.name :: ((I.frame.prologue h.totalSlots).1 ++ saveCs I h.nslots h.saved ++ c))
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
  op : ∀ {sig rs : List Ty} (code : OpCode sig rs) pas dsts vh c cl,
    I.gpr.op code pas dsts vh = some (c, cl) → NoLab I c
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
  (canonAbi : ∀ t r, NoLab I (I.frame.canonAbi t r).1) (call : ∀ f, NoLab I (I.frame.call f))
  (exitJmp : ∀ f, NoLab I (I.frame.exitJmp f)) (ret : NoLab I I.frame.ret)

/-- Frame size in bytes required by `hints` on target `T`. -/
abbrev frame (T : Target) (hints : T.toIsa.Hints) : Nat :=
  T.frame.frameSize hints.totalSlots

end Rega
end LeanQbe.T
