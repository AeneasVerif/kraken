module

public import LeanQbe.T.Target

/-!
# PHOAS-First Checked Register-Allocation Lowering (`Rega`)

Direct structural lowering of `Expr VNat LNat rs` / `Blocks VNat LNat rs sig` (zero `TFlat`/`denote`)
consuming untrusted literal `LeanQbe.T.Trie` `Hints`: bounded `regs`, `O(log N)` multi-granule
`slots : Trie SlotEntry` with 15-granule overlap clearing, lexical `defs : Trie DefFact` and
`vecWidths : Trie SlotWidth`, sequential `nv` (`h.dest` keyed by `x : Nat`), `entryScopeOk nv`,
read-only flag cache, `PreStep.clearFlags`, `canonAbi` (skipped by `abiSkips`
for canonical `.gprZ`/exact-immediate registers), `loadSext` fusion, pure `Bool` comparisons, and
monotone `nl` label counter.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

abbrev VNat : Ty → Type := fun _ => Nat
abbrev LNat : List Ty → Type := fun _ => Nat

inductive RegLoc (Reg VReg Cond : Type) where
  | gpr (r : Reg) | gprZ (r : Reg) | vec (v : VReg) | flag (c : Cond)
  deriving DecidableEq, Repr

inductive SlotEntry where
  | gpr (sas : List SymArg)
  | gprZ (sas : List (SymArg × Bool))
  | vec (w : SlotWidth) (sas : List SymArg)
  deriving DecidableEq, Repr

def SlotEntry.slots : SlotEntry → Nat
  | .gpr _ | .gprZ _ => 1 | .vec w _ => w.slots

inductive RmwOp where
  | add | sub | and | or | xor
  deriving DecidableEq, Repr

def RmwOp.toOpCode (w : Nat) : RmwOp → OpCode [.bits w, .bits w] [.bits w]
  | .add => .add (.bits w)
  | .sub => .sub (.bits w)
  | .and => .and (.bits w)
  | .or  => .or  (.bits w)
  | .xor => .xor (.bits w)

def RmwOp.isComm : RmwOp → Bool
  | .add | .and | .or | .xor => true
  | .sub => false

inductive DefFact where
  | addImm64 (base : Nat) (disp : BitVec 64)
  | scaleOff (idx : Nat) (sh : Nat) (disp : BitVec 64)
  | addrSum (base idx : Nat) (sh : Nat) (disp : BitVec 64)
  | imm64 (c : BitVec 64)
  | andVarVar (w x y : Nat)
  | andVarImm (w x : Nat) (c : BitVec 64)
  | binVarVar (w : Nat) (op : RmwOp) (x y : Nat)
  | binVarImm (w : Nat) (op : RmwOp) (x : Nat) (c : BitVec 64)
  | sextVar (m n x : Nat)
  | zextVar (m n x : Nat)
  | cmpZeroVar (co : CmpOp) (w x : Nat)
  | testBitVar (neg : Bool) (w x : Nat) (c : BitVec 64)
  | shlVarImm (w x sh : Nat)
  deriving DecidableEq, Repr

def DefFact.isAddr : DefFact → Bool
  | .imm64 _ | .addImm64 _ _ | .scaleOff _ _ _ | .addrSum _ _ _ _ => true
  | _ => false

structure SymState (I : Isa) where
  regs : List (SymArg × RegLoc I.Reg I.VReg I.Cond)
  slots : Trie SlotEntry
  defs : Trie DefFact
  vecWidths : Trie SlotWidth
  memDefs : Trie (Ty × Arg VNat i64) := .empty
  zeroExt32 : List I.Reg := []

structure Ext where
  callees : List (Sym × List Ty × List Ty) := []
  exits : List Sym := []
  deriving DecidableEq, Repr, Inhabited

abbrev Res (I : Isa) := Except String (List I.Directive × Nat × Nat × Nat)

/-! ## Pure `Bool` Equalities, Labels, and Bank Predicates -/

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
  | .gpr a, .gpr b | .gprZ a, .gprZ b => a == b
  | .vec a, .vec b => a == b
  | .flag a, .flag b => a == b
  | _, _ => false

def regLocMatchesGpr {I : Isa} (rl : RegLoc I.Reg I.VReg I.Cond) (r : I.Reg) : Bool :=
  match rl with
  | .gpr r' | .gprZ r' => r' == r
  | _ => false

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

def gprEntries {I : Isa} (r : I.Reg) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) : List SymArg :=
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
      some (I.gpr.movi d c,
        { st with
          regs := (.immBits 64 c, .gpr d) :: killRegs I clob [] FlagMask.none st.regs
          zeroExt32 := zExt })
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
    List I.Move → SymState I → Option (List I.Directive × SymState I)
  | [], st => some ([], st)
  | mv :: mvs, st => (execMove I nslots saved mv st).bind fun (c1, st1) =>
      (execMoves I nslots saved mvs st1).map fun (c2, st2) => (c1 ++ c2, st2)

def execClearFlags (I : Isa) (st : SymState I) : List I.Directive × SymState I :=
  (I.gpr.clearFlags, { st with
    regs := I.gpr.zeroFlags.map (.immBool false, .flag ·) ++
            killRegs I I.frame.scratch [] FlagMask.all st.regs
    zeroExt32 := killZeroExt I.frame.scratch st.zeroExt32 })

def stepPre (I : Isa) (h : I.Hints) (ip : Nat) (st : SymState I) : Option (List I.Directive × SymState I) :=
  match h.pre.find? ip with
  | none => some ([], st)
  | some ps => (execMoves I h.nslots h.saved ps.moves st).map fun (mc, st1) =>
      if ps.clearFlags then let (cc, st2) := execClearFlags I st1; (mc ++ cc, st2) else (mc, st1)

/-! ## Target Presence Checking and Untrusted Parallel-Move Shuffle -/

def holdsLoc (I : Isa) (st : SymState I) (sa : SymArg) : I.Loc → Bool
  | .gpr r => st.regs.any fun (sa', rl) =>
    match rl with | .gpr r' | .gprZ r' => r' == r && symArgMatchesGpr sa' sa | _ => false
  | .vec v => st.regs.any fun (sa', rl) => match rl with | .vec v' => v' == v && symArgEq sa' sa | _ => false
  | .flag c => st.regs.any fun (sa', rl) => match rl with | .flag c' => c' == c && symArgEq sa' sa | _ => false
  | .slot i w =>
    match symArgWidth st.vecWidths sa with
    | some wsa =>
      Nat.ble wsa.bits w.bits &&
      match st.slots.find? i with | some (.vec w' sas) => slotWidthEq w' w && sas.any (symArgEq · sa) | _ => false
    | none =>
      slotWidthEq w .w64 &&
      match st.slots.find? i with
      | some (.gpr sas) => sas.any (symArgMatchesGpr · sa)
      | some (.gprZ sas) => sas.any fun (sa', _) => symArgMatchesGpr sa' sa
      | _ => false

def findGprFor (I : Isa) (noScr : Bool) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond)) (sa : SymArg) : Option I.Reg :=
  R.findSome? fun (sa', rl) =>
    match rl with
    | .gpr r | .gprZ r =>
      if (!noScr || !(I.frame.scratch.contains r)) && symArgMatchesGpr sa' sa then some r else none
    | _ => none

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

def isVarSymArg : SymArg → Bool | .var _ => true | _ => false

def locBlocked (I : Isa) (st : SymState I) (pend : List (SymArg × I.Loc)) (d : I.Loc) : Bool :=
  pend.any fun (sa, d') =>
    !(locEq d' d) && isVarSymArg sa &&
    match d with
    | .gpr r =>
      st.regs.all (fun (sa', rl) => !symArgEq sa' sa || regLocMatchesGpr rl r) &&
      st.regs.any (fun (sa', rl) => symArgEq sa' sa && regLocMatchesGpr rl r)
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

/-! ## ABI Helpers, Lexical Defs, and Operand/Destination Resolution -/

def abiTargets (I : Isa) :
    {ts : List Ty} → Tup (Arg VNat) ts → Tup (AbiReg I.Reg I.VReg) ts → Option (List (SymArg × I.Loc))
  | [], (), () => some []
  | t :: _, (a, as), (loc, locs) =>
    match toSymArg I t a, abiTargets I as locs with
    | some sa, some rest => some ((sa, match loc with | .gpr r => .gpr r | .vec v => .vec v) :: rest)
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
    match rl with
    | .gpr r | .gprZ r =>
      if !(I.frame.scratch.contains r) && symArgMatchesGpr sa' sa then k r else none
    | _ => none

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

def hasVarGprZ (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (x : Nat) (rd : I.Reg) : Bool :=
  R.any fun (sa, rl) => symArgEq sa (.var x) && regLocEq rl (.gprZ rd)

/-- `.zext m n` of a `.gprZ rd` (or zero-extended 32-bit in `rd`) into the same `rd` is a no-op. -/
def elideZext32? (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (zeroExt : List I.Reg) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig →
    Tup (PDst I.Reg I.VReg I.Cond) ts → Bool
  | _, _, .zext m n, (.var x, ()), (.gpr rd, ()) =>
    Nat.ble n 64 && I.gpr.elideZext32 &&
      (hasVarGprZ I R x rd || (Nat.beq m 32 && zeroExt.contains rd && hasVarGpr I R x rd))
  | _, _, _, _, _ => false

def opProducesZ32 (I : Isa) {sig : List Ty} : {rs : List Ty} → OpCode sig rs →
    Tup (PArg I.Reg I.VReg I.Cond) sig → Tup (PDst I.Reg I.VReg I.Cond) rs → Bool
  | [.bits n], code, pas, dsts =>
    Nat.beq n 32 && match dsts with
    | (.gpr _, ()) => I.gpr.zeroUpper32Op code pas dsts
    | _ => false
  | _, _, _, _ => false

def cmpIsSignedOrEq : CmpOp → Bool
  | .eq | .ne | .slt | .sle | .sgt | .sge => true
  | _ => false

def cmpIsUnsignedOrEq : CmpOp → Bool
  | .eq | .ne | .ult | .ule | .ugt | .uge => true
  | _ => false

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
      | some (.addrSum base idx sh d) =>
        (AddrScale.ofShift? sh).bind fun sc =>
          (findGprFor I true st.regs (.var base)).bind fun rb =>
            (findGprFor I true st.regs (.var idx)).bind fun ri =>
              k (.baseIdxDisp rb ri sc (Int64.ofBitVec d))
      | some (.imm64 c) => k (.imm c)
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

def tryExtCmp (I : Isa) (st : SymState I) (vh : VariantHint) (co : CmpOp) (n t : Nat)
    (c : BitVec n) (pd : PDst I.Reg I.VReg I.Cond .bool) : Option (List I.Directive × FlagMask) :=
  match st.defs.find? t with
  | some (.sextVar m n' x) =>
    if !(Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsSignedOrEq co &&
         (c.truncate m).signExtend n == c) then none
    else
      let cm : BitVec m := c.truncate m
      let memTry := match st.memDefs.find? x with
        | some (.bits m', addr) =>
          if Nat.beq m' m then
            tryAddr I st .default addr fun aa => I.gpr.cmpMem co m aa (.imm cm) pd
          else none
        | _ => none
      memTry <|>
        if I.supportsTestFuse then
          tryGpr I st.regs (.var x) fun rx =>
            I.gpr.op (.cmp co (.bits m)) (.gpr rx, .imm cm, ()) (pd, ()) vh
        else none
  | some (.zextVar m n' x) =>
    if !(Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && cmpIsUnsignedOrEq co &&
         (c.truncate m).zeroExtend n == c) then none
    else
      let cm : BitVec m := c.truncate m
      let memTry := match st.memDefs.find? x with
        | some (.bits m', addr) =>
          if Nat.beq m' m then
            tryAddr I st .default addr fun aa => I.gpr.cmpMem co m aa (.imm cm) pd
          else none
        | _ => none
      memTry <|>
        if I.supportsTestFuse then
          tryGpr I st.regs (.var x) fun rx =>
            I.gpr.op (.cmp co (.bits m)) (.gpr rx, .imm cm, ()) (pd, ()) vh
        else none
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
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) : Option (List I.Directive × FlagMask × Bool) :=
  match sig, ts, code, args, dsts with
  | _, _, .cmp co (.bits n) .bool _, (a, b, ()), (pd, ()) =>
    if !Nat.ble n 64 then none
    else
      let tFuse :=
        if co == .eq || co == .ne then
          let neg := co == .ne
          match a, b with
          | .var t, .imm c => if c == 0#n then tryTestSlot I h st neg n t pd else none
          | .imm c, .var t => if c == 0#n then tryTestSlot I h st neg n t pd else none
          | _, _ => none
        else none
      let eFuse := match a, b with
        | .var t, .imm c => tryExtSlot I h st co n t c pd
        | .imm c, .var t => tryExtSlot I h st co.swap n t c pd
        | _, _ => none
      let mFuse :=
        if !isStdBitWidth n then none
        else
          (match a with
           | .var x => (findSlotGpr h.nslots st.slots x).bind fun idx =>
             tryArg I st [] (.bits n) b fun pb => I.gpr.cmpMem co n (spAddr I idx) pb pd
           | _ => none) <|>
          (match b with
           | .var y => (findSlotGpr h.nslots st.slots y).bind fun idx =>
             tryArg I st [] (.bits n) a fun pa => I.gpr.cmpMem co.swap n (spAddr I idx) pa pd
           | _ => none)
      (tFuse <|> eFuse <|> mFuse).map fun (c, cl) => (c, cl, false)
  | _, _, .add (.bits n), (a, b, ()), (.gpr rd, ()) =>
    tryAluSlot I h st n (.add (.bits n)) a b rd
  | _, _, .sub (.bits n), (a, b, ()), (.gpr rd, ()) =>
    tryAluSlot I h st n (.sub (.bits n)) a b rd
  | _, _, .mul (.bits n), (a, b, ()), (.gpr rd, ()) =>
    tryAluSlot I h st n (.mul (.bits n)) a b rd
  | _, _, .and (.bits n), (a, b, ()), (.gpr rd, ()) =>
    tryAluSlot I h st n (.and (.bits n)) a b rd
  | _, _, .or  (.bits n), (a, b, ()), (.gpr rd, ()) =>
    tryAluSlot I h st n (.or (.bits n)) a b rd
  | _, _, .xor (.bits n), (a, b, ()), (.gpr rd, ()) =>
    tryAluSlot I h st n (.xor (.bits n)) a b rd
  | _, _, _, _, _ => none

def tryFuseCmp (I : Isa) (st : SymState I) (vh : VariantHint) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask) :=
  match sig, ts, code, args, dsts with
  | _, _, .cmp co (.bits n) .bool _, (a, b, ()), (pd, ()) =>
    if !Nat.ble n 64 then none
    else
      let tFuse :=
        if co == .eq || co == .ne then
          let neg := co == .ne
          match a, b with
          | .var t, .imm c => if c == 0#n then tryTestFuse I st neg n t pd else none
          | .imm c, .var t => if c == 0#n then tryTestFuse I st neg n t pd else none
          | _, _ => none
        else none
      let eFuse := match a, b with
        | .var t, .imm c => tryExtCmp I st vh co n t c pd
        | .imm c, .var t => tryExtCmp I st vh co.swap n t c pd
        | _, _ => none
      let mFuse :=
        (match a with | .var x => tryCmpMemVar I st co n x b pd | _ => none) <|>
        (match b with | .var y => tryCmpMemVar I st co.swap n y a pd | _ => none)
      tFuse <|> eFuse <|> mFuse
  | _, _, _, _, _ => none

/-- Fused `sext m n` of an elided `load (.bits m)` (`memDefs`) into one sign-extending load. -/
def tryLoadSext (I : Isa) (st : SymState I) (vh : VariantHint) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig) (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask) :=
  match sig, ts, code, args, dsts with
  | _, _, .sext m n, (.var x, ()), (.gpr rd, ()) =>
    match st.memDefs.find? x with
    | some (.bits m', addr) =>
      if Nat.beq m' m && Nat.ble n 64 then tryAddr I st vh addr (I.gpr.loadSext m n rd) else none
    | _ => none
  | _, _, _, _, _ => none

def normZeroCmp : CmpOp → CmpOp
  | .ugt => .ne
  | .ule => .eq
  | o => o

def recordBoolDef (defs : Trie DefFact) {sig ts : List Ty} (code : OpCode sig ts)
    (args : Tup (Arg VNat) sig) : Option DefFact :=
  match sig, ts, code, args with
  | _, _, .cmp co (.bits n) .bool _, (a, b, ()) =>
    if !Nat.ble n 64 then none
    else
      let pair? := match a, b with
        | .var t, .imm c => if c == 0#n then some (normZeroCmp co, t) else none
        | .imm c, .var t => if c == 0#n then some (normZeroCmp co.swap, t) else none
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
    ext?.bind fun (base?, idx, sc, disp) =>
      let rbOpt? : Option (Option I.Reg) := match base? with
        | some b => (findGprFor I true st.regs (.var b)).map some
        | none => some none
      rbOpt?.bind fun rb? =>
        (findGprFor I true st.regs (.var idx)).bind fun ri =>
          (I.gpr.leaArith w rb? ri sc disp rd).map fun (c, cl) =>
            (c, cl, Nat.beq w 32 && I.gpr.zeroUpper32LeaArith)
  | _, _ => none

def lowerOp (I : Isa) (h : I.Hints) (nv ip : Nat) (st1 : SymState I) {ts : List Ty}
    (op : Op VNat ts) (deferFuse : Bool := false) : Option (List I.Directive × SymState I) :=
  if deferFuse then
    ((recordBoolDef st1.defs op.code op.args).map fun df =>
      ([], { st1 with defs := st1.defs.insert nv df })) <|>
    ((recordDef st1.defs op.code op.args).map fun df =>
      ([], { st1 with defs := st1.defs.insert nv df }))
  else if h.elide.getD ip false then
    match recordDef st1.defs op.code op.args with
    | some df => some ([], { st1 with defs := st1.defs.insert nv df })
    | none => none
  else
    (resolveDsts I h ts nv).bind fun dsts =>
      let vh := h.variant.getD ip .default
      let dstGprs := tupDstGprs dsts; let dstVecs := tupDstVecs dsts
      let defs1 := match recordDef st1.defs op.code op.args with
        | some df => st1.defs.insert nv df
        | none => st1.defs
      if elideZext32? I st1.regs st1.zeroExt32 op.code op.args dsts then
        -- no code: every register fact survives and the result shares `rd` canonically
        let regs1 := match ts, dsts with
          | [_], (.gpr rd, ()) => (.var nv, RegLoc.gprZ rd) :: st1.regs
          | _, _ => st1.regs
        some ([], { st1 with regs := regs1, defs := defs1 })
      else
        ((((tryFuseCmp I st1 vh op.code op.args dsts).map fun (c, cl) =>
          (c, cl, false, false)) <|>
        ((tryLoadSext I st1 vh op.code op.args dsts).map fun (c, cl) =>
          (c, cl, false, false)) <|>
        ((tryLeaArith I st1 op.code op.args dsts).map fun (c, cl, z32) =>
          (c, cl, false, z32)) <|>
        (pickPArgs I st1 (tupDstFlags dsts) op.args fun pas =>
          if dstVecs.isEmpty && (tupArgVecs pas).isEmpty then
            ((I.gpr.op op.code pas dsts vh).map fun (c, cl) =>
              (c, cl, false, opProducesZ32 I op.code pas dsts)) <|>
            ((I.vec.vop op.code pas dsts vh).map fun (c, cl) => (c, cl, true, false))
          else (I.vec.vop op.code pas dsts vh).map fun (c, cl) =>
            (c, cl, true, false)) <|>
        ((trySlotOp I h st1 op.code op.args dsts).map fun (c, cl, z32) =>
          (c, cl, false, z32))) : Option (List I.Directive × FlagMask × Bool × Bool)).map
          fun (code, clob, isVec, z32) =>
          let vClob := if isVec then dstVecs ++ I.vec.vecScratch else []
          let gClob := dstGprs ++ I.frame.scratch
          let killed := killRegs I gClob vClob clob st1.regs
          let zExt := killZeroExt gClob st1.zeroExt32
          let (regs1, vw1, zExt1) :=
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
          (code, { st1 with regs := regs1, defs := defs1, vecWidths := vw1, zeroExt32 := zExt1 })

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
    if isGprTy I t then
      let zExt := if tyEq t (.bits 32) then r :: killZeroExt [r] st.zeroExt32 else st.zeroExt32
      bindAbiParams I locs (nv + 1)
        { st with regs := (.var nv, .gprZ r) :: st.regs, zeroExt32 := zExt }
    else none
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
  { st with
    regs := st.regs.filter fun (_, rl) =>
      match rl with | .gpr r | .gprZ r => saved.contains r | _ => false,
    memDefs := .empty,
    zeroExt32 := st.zeroExt32.filter saved.contains }
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
  | testImm (neg : Bool) (w : Nat) (r : I.Reg) (mask : BitVec w)

def findJnzCond (I : Isa) (nslots : Nat) (st : SymState I) (x : Nat) : Option (JnzCond I) :=
  (findFlagFor I st.regs (.var x)).map .flag <|>
    (findGprFor I true st.regs (.var x)).map .gpr <|>
    (match st.defs.find? x with
     | some (.cmpZeroVar co w y) =>
       (findGprFor I true st.regs (.var y)).map fun r => .cmpZero co w r
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

def jnzMode {rs : List Ty} (I : Isa) (h : I.Hints) (ipT ipE : Nat) (st : SymState I)
    (canInv : Bool) (t e : Expr VNat LNat rs) (ft : Option Nat) : Bool × Option Nat :=
  match zeroMoveJump? I h ipT st t, if canInv then zeroMoveJump? I h ipE st e else none with
  | some jt, some je => if ft == some jt then (true, some je) else (false, some jt)
  | some jt, none => (false, some jt)
  | none, some je => (true, some je)
  | none, none => (canInv && h.invertJnz.getD (ipE - 1) false, none)

def gprThread? {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (ipT : Nat) (st1 : SymState I)
    (r : I.Reg) : Expr VNat LNat rs → Option Nat
  | .jump j args =>
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] (I.gpr.jnzGpr r (lname fn j)).2 st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 }
    zeroMoveJump? (rs := rs) I h ipT stB (.jump j args)
  | _ => none

def threadFusedArm {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (ipA : Nat)
    (st1 : SymState I) (emit : Sym → Option (List I.Directive × FlagMask))
    (arm : Expr VNat LNat rs) : Option (Nat × List I.Directive × SymState I) :=
  match arm with
  | .jump j _ =>
    (emit (lname fn j)).bind fun (br, cl) =>
      let stB := { st1 with
        regs := killRegs I I.frame.scratch [] cl st1.regs
        zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 }
      if zeroMoveJump? I h ipA stB arm == some j then some (j, br, stB) else none
  | _ => none

def fuseJnzChoice {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : SymState I) (t e : Expr VNat LNat rs) (ft : Option Nat)
    (emit : Bool → Sym → Option (List I.Directive × FlagMask)) :
    Option (Bool × Option Nat × List I.Directive × SymState I) :=
  let invChoice := h.invertJnz.getD (ipE - 1) false
  (emit invChoice (lname fn nl)).map fun (brNl, clNl) =>
    let stNl := { st1 with
      regs := killRegs I I.frame.scratch [] clNl st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 }
    let fwd? := threadFusedArm I h fn ipT st1 (emit false) t
    let inv? := threadFusedArm I h fn ipE st1 (emit true) e
    match fwd?, inv? with
    | some (jt, brF, stF), some (je, brI, stI) =>
      if ft == some jt then (true, some je, brI, stI) else (false, some jt, brF, stF)
    | some (jt, brF, stF), none => (false, some jt, brF, stF)
    | none, some (je, brI, stI) => (true, some je, brI, stI)
    | none, none => (invChoice, none, brNl, stNl)

/-- Branch selection for `jnz`: `(inverted?, threaded target, branch code, state after branch)`. -/
def jnzSetup {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : SymState I) (t e : Expr VNat LNat rs) (ft : Option Nat) :
    JnzCond I → Option (Bool × Option Nat × List I.Directive × SymState I)
  | .flag cc =>
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] FlagMask.none st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 }
    let p := jnzMode I h ipT ipE stB true t e ft
    some (p.1, p.2, I.gpr.jcc (if p.1 then I.gpr.negCond cc else cc)
      (lname fn (p.2.getD nl)), stB)
  | .gpr r =>
    let tg := gprThread? I h fn ipT st1 r t
    let p := I.gpr.jnzGpr r (lname fn (tg.getD nl))
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] p.2 st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 }
    some (false, tg, p.1, stB)
  | .slot idx =>
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] FlagMask.all st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 }
    let p := jnzMode I h ipT ipE stB true t e ft
    (I.gpr.jnzMem (spAddr I idx) p.1 (lname fn (p.2.getD nl))).bind fun (br, cl) =>
      if cl == FlagMask.all then some (p.1, p.2, br, stB) else none
  | .cmpZero co w r =>
    fuseJnzChoice I h fn nl ipT ipE st1 t e ft fun inv l =>
      I.gpr.cmpZeroJcc (if inv then co.neg else co) w r l
  | .testImm neg w r mask =>
    fuseJnzChoice I h fn nl ipT ipE st1 t e ft fun inv l =>
      I.gpr.testJcc (if inv then !neg else neg) w r mask l

def finishJnzBranch {rs : List Ty} (I : Isa) (fn : Sym) (nl : Nat) (tgt? : Option Nat)
    (b_taken : Expr VNat LNat rs) (br c_ft c_taken : List I.Directive) (nv2 nl2 ip2 : Nat) : Res I :=
  match tgt? with
  | some j => match b_taken with
    | .jump j' _ => if Nat.beq j' j && c_taken.isEmpty then .ok (br ++ c_ft, nv2, nl2, ip2) else .error "jnz: bad thread"
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
      match pa with | .vec vs => tryAddr I st1 vh addr (I.vec.vstore (.pair a b) vs) | _ => none).map fun (c, clob) =>
      (c, { st1 with
            regs := killRegs I I.frame.scratch I.vec.vecScratch clob st1.regs
            memDefs := .empty
            zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 })
  | t, v, addr =>
    if !isGprTy I t then none
    else
      ((tryArg I st1 [] t v fun pa => tryAddr I st1 vh addr (I.gpr.store t pa)) <|>
       tryRmwStore I st1 vh t v addr).map fun (c, clob) =>
        (c, { st1 with
              regs := killRegs I I.frame.scratch [] clob st1.regs
              memDefs := .empty
              zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 })

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
      else (tryAddr I st1 vh a (I.gpr.load t d)).map fun (c, clob) =>
        let isZ32 := I.gpr.zeroUpper32Load && tyEq t (.bits 32)
        let rl := if I.gpr.zeroExtLoad || isZ32 then RegLoc.gprZ d else .gpr d
        let zExt := killZeroExt (d :: I.frame.scratch) st1.zeroExt32
        let zExt1 := if isZ32 then d :: zExt else zExt
        (c, { st1 with
              regs := (.var nv, rl) :: killRegs I (d :: I.frame.scratch) [] clob st1.regs
              zeroExt32 := zExt1 })
    | some (.vec vd) => (vecWidth? I t).bind fun w =>
      if !isAllocVec I vd then none
      else (tryAddr I st1 vh a (I.vec.vload t vd)).map fun (c, clob) =>
        (c, { st1 with
              regs := (.var nv, .vec vd) ::
                killRegs I I.frame.scratch (vd :: I.vec.vecScratch) clob st1.regs
              vecWidths := st1.vecWidths.insert nv w
              zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32 })
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
  | some tgts => match shuffle I h.nslots h.saved st1 tgts with
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
          | some (.cmpZero co w r) => (I.gpr.cmpZeroJcc co w r (lname fn nl)).isSome
          | some (.testImm neg w r mask) => (I.gpr.testJcc neg w r mask (lname fn nl)).isSome
          | _ => false
        | none => false
      | none => false
  | _, _ => false

def isLeaDeferCand {sig ts : List Ty} (code : OpCode sig ts) : Bool :=
  match ts, code with
  | [.bits w], .shl (.bits _) | [.bits w], .add (.bits _) | [.bits w], .sub (.bits _) =>
    Nat.beq w 32 || Nat.beq w 64
  | _, _ => false

/-- Lookahead deferring shift/add/sub arithmetic feeding a single-use `tryLeaArith` consumer.
Single-use-ness (`nv` dead in the continuation after the consumer) is read in O(1) from the
untrusted `h.deferLea` hint (computed natively by `deferScan`) instead of an in-kernel
`exprFreeOfVar` walk of the rest of the block. -/
def deferLeaNext {rs : List Ty} (I : Isa) (h : I.Hints) (nv ip : Nat)
    (st1 : SymState I) {ts : List Ty} (op : Op VNat ts) (k' : Expr VNat LNat rs) : Bool :=
  if !isLeaDeferCand op.code then false
  else
    match ts, k' with
    | [_], .let_ (ts := ts2) op2 _k2 =>
      match recordDef st1.defs op.code op.args with
      | some df =>
        match stepPre I h (ip + 1) { st1 with defs := st1.defs.insert nv df } with
        | some (_, stAfter) =>
          match resolveDsts I h ts2 (nv + 1) with
          | some dsts2 =>
            (tryLeaArith I stAfter op2.code op2.args dsts2).isSome &&
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
    let accL := if !isLeaDeferCand op.code then acc.2 else
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

mutual
def lowerExpr (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    Expr VNat LNat rs → Nat → Nat → Nat → SymState I → Option Nat → Res I
  | .let_ (ts := ts) op k, nv, nl, ip, st, ft =>
    match stepPre I h ip st with
    | none => .error "let: pre"
    | some (mc, st1) =>
      let k' := k (Tup.levels ts nv)
      let df := deferJnzNext I h fn nv nl ip st1 op k' || deferLeaNext I h nv ip st1 op k'
      match lowerOp I h nv ip st1 op df with
      | none => .error "let: op"
      | some (c, st2) =>
        prepend (mc ++ c) (lowerExpr I h E fn k' (nv + ts.length) nl (ip + 1) st2 ft)
  | .load t a k, nv, nl, ip, st, ft =>
    match stepPre I h ip st with
    | none => .error "load: pre"
    | some (mc, st1) =>
      match lowerLoad I h nv ip st1 t a (loadSextNext I h nv ip st1 t a (k nv)) with
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
                prepend (mc ++ sc ++
                    canonAbiCode I argLocs (abiSkips I st2.regs st2.zeroExt32 args argLocs) ++
                    I.frame.call f)
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
    | some (mc, st1) => match findJnzCond I h.nslots st1 cx with
      | none => .error "jnz: cond"
      | some cond =>
        match jnzSetup I h fn nl (jnzIpT nv nl ip t e) (ip + 1) st1 t e ft cond with
        | none => .error "jnz: setup"
        | some (inv, tgt?, br, stBr) =>
          let ftT := match tgt? with | some j => some j | none => ft
          let ftF := match tgt? with | some _ => ft | none => none
          match lowerExpr I h E fn e nv (nl + 1) (ip + 1) stBr (if inv then ftT else ftF) with
          | .error err => .error err
          | .ok (ce, nv1, nl1, ip1) =>
            match lowerExpr I h E fn t nv1 nl1 ip1 stBr (if inv then ftF else ftT) with
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
    | some (mc, st1), some retLocs => lowerTail I h E st1 mc I.frame.ret vs retLocs nv nl ip
    | _, _ => .error "ret: pre/abi"
  | .exit f (as := as) args, nv, nl, ip, st, _ =>
    match stepPre I h ip st, I.assignArgs as with
    | some (mc, st1), some argLocs =>
      if !E.exits.contains f then .error "exit: target"
      else lowerTail I h E st1 mc (I.frame.exitJmp f) args argLocs nv nl ip
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
      else match buildEntryBase I h.nslots vw en.live
          { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
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
    | some argLocs, some _ =>
      match bindAbiParams I argLocs 0
        { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
      | none => .error "fn: abi bind"
      | some st0 => match lowerExpr I h E f.name (f.body VNat LNat (Tup.levels f.as 0)) f.as.length 0 0 st0 none with
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
