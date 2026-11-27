module

public import LeanQbe.T.RegaDefs
public import LeanQbe.T.RegaZero
public import LeanQbe.T.RegaZext

/-!
# Wave 6.2-A Checked Helpers (`RegaW62`)

Pure symbolic-allocator helpers for:
* `OPT-7b` scratch-constant preservation (`killScr`, `moveKeepsScr`);
* `OPT-10a` cross-block `.gprZ` / `.gprZ`-slot verification (`holdsZLoc`, `entryZOk`,
  `buildEntryBaseZ`, `bindBlockParamsZ`);
* `OPT-10b` canonical zero-extension op elision (`elideRegOp?`) and `64->32/16/8` load
  truncation fusion (`tryLoadTrunc`);
* `OPT-7c` GPR-preferred immediate selection (`tryArgPref`, `pickPArgsCode`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-! ## Scratch-Constant Invariant Helpers (`OPT-7b`) -/

/-- Drop any scratch-constant entries whose registers appear in `gClob`. -/
def killScr {Reg : Type} [DecidableEq Reg] (gClob : List Reg)
    (scr : List (Reg × BitVec 64)) : List (Reg × BitVec 64) :=
  scr.filter fun (r, _) => !(gClob.contains r)

/-- Scratch-constant map surviving `mv` (`mov` to a non-scratch register keeps all scratch
constants; any other move conservatively drops scratch entries). -/
def moveKeepsScr (I : Isa) (mv : I.Move)
    (scr : List (I.Reg × BitVec 64)) : List (I.Reg × BitVec 64) :=
  match mv with
  | .mov d _ => if I.frame.scratch.contains d then [] else killScr [d] scr
  | _ => []

/-! ## Cross-Block `.gprZ` Entry Checking (`OPT-10a`) -/

/-- `true` when `R` maps `.var x` to canonical `.gprZ r`. -/
def holdsVarGprZ (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (x : Nat) (r : I.Reg) : Bool :=
  R.any fun (sa', rl) => symArgEq sa' (.var x) && regLocEq rl (.gprZ r)

/-- `true` when `st` guarantees `AbiGprHolds` for `sa` placed at `loc` (either `.gpr r` or
64-bit stack slot `.slot i .w64`). -/
def holdsZLoc (I : Isa) (st : SymState I) (sa : SymArg) : I.Loc → Bool
  | .gpr r =>
    match sa with
    | .var x => holdsVarGprZ I st.regs x r
    | .immBits _ c =>
      st.regs.any fun (sa', rl) =>
        symArgEq sa' (.immBits 64 c) && regLocMatchesGpr rl r
    | .immBool b =>
      st.regs.any fun (sa', rl) =>
        symArgEq sa' (.immBits 64 (if b then 1#64 else 0#64)) && regLocMatchesGpr rl r
    | .immVec _ _ => false
  | .slot i w =>
    if !slotWidthEq w .w64 then false
    else match sa with
      | .var x =>
        match st.slots.find? i with
        | some (.gprZ sas) => sas.any fun (sa', z) => z && symArgEq sa' (.var x)
        | _ => false
      | _ => false
  | .vec _ | .flag _ => false

/-- Check `en.liveZ` and `en.plocZ` against post-shuffle state `st` and incoming `argTgts`. -/
def entryZOk (I : Isa) (st : SymState I) (en : Entry I.Reg I.VReg I.Cond)
    (argTgts : List (SymArg × I.Loc)) : Bool :=
  let rec goLive : List (SymArg × I.Loc) → List Bool → Bool
    | [], _ | _, [] => true
    | (sa, loc) :: rest, z :: zs => (!z || holdsZLoc I st sa loc) && goLive rest zs
  let rec goArg : List (SymArg × I.Loc) → List Bool → Bool
    | [], _ | _, [] => true
    | (sa, loc) :: rest, z :: zs => (!z || holdsZLoc I st sa loc) && goArg rest zs
  goLive en.live en.liveZ && goArg argTgts en.plocZ

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
      | some (.gprZ sas) => some (slots.insert i (.gprZ ((sa, false) :: sas)))
      | _ => some ((clearSlotRange i 1 slots).insert i (.gpr [sa]))

/-- Add a `.gprZ` entry into a 64-bit slot in `slots` (clearing overlaps if overwriting non-GPR). -/
def addSlotZEntry (vw : Trie SlotWidth) (sa : SymArg) (z : Bool) (i : Nat) (w : SlotWidth)
    (slots : Trie SlotEntry) : Option (Trie SlotEntry) :=
  match symArgWidth vw sa with
  | some _ => none
  | none =>
    if !slotWidthEq w .w64 then none
    else match slots.find? i with
      | some (.gprZ sas) => some (slots.insert i (.gprZ ((sa, z) :: sas)))
      | some (.gpr sas) =>
        some (slots.insert i (.gprZ ((sa, z) :: sas.map (·, false))))
      | _ => some ((clearSlotRange i 1 slots).insert i (.gprZ [(sa, z)]))

/-- Variant of `buildEntryBase` that restores `.gprZ` facts flagged in `liveZ`. -/
def buildEntryBaseZ (I : Isa) (nslots : Nat) (vw : Trie SlotWidth) :
    List (SymArg × I.Loc) → List Bool → SymState I → Option (SymState I)
  | [], _, st => some st
  | (sa, .gpr r) :: rest, zs, st =>
    if !(I.frame.scratch.contains r) then
      let isZ := zs.headD false && match sa with | .var _ => true | _ => false
      let rl := if isZ then RegLoc.gprZ r else .gpr r
      buildEntryBaseZ I nslots vw rest zs.tail { st with regs := (sa, rl) :: st.regs }
    else none
  | (sa, .vec v) :: rest, zs, st =>
    if !(I.vec.vecScratch.contains v) && (symArgWidth vw sa).isSome then
      buildEntryBaseZ I nslots vw rest zs.tail { st with regs := (sa, .vec v) :: st.regs }
    else none
  | (sa, .flag c) :: rest, zs, st =>
    buildEntryBaseZ I nslots vw rest zs.tail { st with regs := (sa, .flag c) :: st.regs }
  | (sa, .slot i w) :: rest, zs, st =>
    if !Nat.ble (i + w.slots) nslots then none
    else
      let isZ := zs.headD false && match sa with | .var _ => true | _ => false
      let res :=
        if isZ && (symArgWidth vw sa).isNone && slotWidthEq w .w64 then
          addSlotZEntry vw sa true i w st.slots
        else addSlotEntry vw sa i w st.slots
      res.bind fun slots' =>
        buildEntryBaseZ I nslots vw rest zs.tail { st with slots := slots' }

/-- Variant of `bindBlockParams` that restores `.gprZ` facts flagged in `plocZ`. -/
def bindBlockParamsZ (I : Isa) (nslots : Nat) :
    (ts : List Ty) → List I.Loc → List Bool → Nat → SymState I → Option (SymState I)
  | [], [], _, _, st => some st
  | t :: ts, loc :: locs, zs, nv, st =>
    let isZ := zs.headD false
    match loc with
    | .gpr r =>
      if !(I.frame.scratch.contains r) && isGprTy I t then
        let rl := if isZ then RegLoc.gprZ r else .gpr r
        let zExt :=
          if isZ && tyEq t (.bits 32) then r :: killZeroExt [r] st.zeroExt32
          else killZeroExt [r] st.zeroExt32
        bindBlockParamsZ I nslots ts locs zs.tail (nv + 1)
          { st with regs := (.var nv, rl) :: st.regs, zeroExt32 := zExt }
      else none
    | .vec v => (vecWidth? I t).bind fun w =>
      if !(I.vec.vecScratch.contains v) then
        bindBlockParamsZ I nslots ts locs zs.tail (nv + 1)
          { st with regs := (.var nv, .vec v) :: st.regs, vecWidths := st.vecWidths.insert nv w }
      else none
    | .flag c => match t with
      | .bool =>
        bindBlockParamsZ I nslots ts locs zs.tail (nv + 1)
          { st with regs := (.var nv, .flag c) :: st.regs }
      | _ => none
    | .slot i w =>
      if !(Nat.ble (i + w.slots) nslots && (isGprTy I t || (vecWidth? I t).isSome)) then none
      else
        let vw' := match vecWidth? I t with
          | some wt => st.vecWidths.insert nv wt | none => st.vecWidths
        let res :=
          if isZ && (vecWidth? I t).isNone && slotWidthEq w .w64 then
            addSlotZEntry vw' (.var nv) true i w st.slots
          else addSlotEntry vw' (.var nv) i w st.slots
        res.bind fun slots' =>
          bindBlockParamsZ I nslots ts locs zs.tail (nv + 1)
            { st with slots := slots', vecWidths := vw' }
  | _, _, _, _, _ => none

/-! ## Unified Zero-Cost Same-Register Op Elision (`OPT-10b`) -/

/-- `true` when `R` maps `.var x` to `.gpr rd` or `.gprZ rd`. -/
def hasVarGprW (I : Isa) (R : List (SymArg × RegLoc I.Reg I.VReg I.Cond))
    (x : Nat) (rd : I.Reg) : Bool :=
  R.any fun (sa, rl) => symArgEq sa (.var x) && regLocMatchesGpr rl rd

/-- Attempt to elide a same-register `.zext`, `.trunc`, `.ofBool`, `.copy`, or `.bitcast` op,
returning `some (rd, isGprZ, addZ32)` where `isGprZ` marks canonical `.gprZ rd` and `addZ32`
adds `rd` to `zeroExt32`. -/
def elideRegOp? (I : Isa) (st : SymState I) :
    {sig ts : List Ty} → OpCode sig ts → Tup (Arg VNat) sig →
    Tup (PDst I.Reg I.VReg I.Cond) ts → Option (I.Reg × Bool × Bool)
  | _, _, .zext m n, (.var x, ()), (.gpr rd, ()) =>
    if Nat.ble n 64 && I.gpr.elideZext32 &&
        (holdsVarGprZ I st.regs x rd ||
          (Nat.beq m 32 && st.zeroExt32.contains rd && hasVarGprW I st.regs x rd)) then
      some (rd, true, Nat.beq n 32)
    else none
  | _, _, .trunc m n, (.var x, ()), (.gpr rd, ()) =>
    if !(Nat.ble n m && Nat.ble n 64 && hasVarGprW I st.regs x rd) then none
    else if I.gpr.elideZext32 && Nat.beq n 32 &&
        I.gpr.zeroUpper32Op (.trunc m n) (.gpr rd, ()) (.gpr rd, ()) then
      if st.zeroExt32.contains rd then some (rd, true, true) else none
    else
      let isZ := Nat.beq n 32 && st.zeroExt32.contains rd
      some (rd, isZ, isZ)
  | _, _, .ofBool n, (.var x, ()), (.gpr rd, ()) =>
    if Nat.blt 0 n && Nat.ble n 64 && holdsVarGprZ I st.regs x rd then some (rd, true, Nat.beq n 32)
    else none
  | _, _, .copy (.bits n), (.var x, ()), (.gpr rd, ()) =>
    if !Nat.ble n 64 then none
    else if holdsVarGprZ I st.regs x rd then some (rd, true, Nat.beq n 32)
    else if !hasVarGprW I st.regs x rd then none
    else if I.gpr.elideZext32 && Nat.beq n 32 &&
        I.gpr.zeroUpper32Op (.copy (.bits 32)) (.gpr rd, ()) (.gpr rd, ()) then
      if st.zeroExt32.contains rd then some (rd, true, true) else none
    else
      let isZ := Nat.beq n 32 && st.zeroExt32.contains rd
      some (rd, isZ, isZ)
  | _, _, .copy .bool, (.var x, ()), (.gpr rd, ()) =>
    if holdsVarGprZ I st.regs x rd then some (rd, true, false)
    else if hasVarGprW I st.regs x rd &&
        !I.gpr.zeroExtOp (.copy .bool) (.gpr rd, ()) (.gpr rd, ()) then
      some (rd, false, false)
    else none
  | _, _, .bitcast (.bits m) (.bits n) hsz, (.var x, ()), (.gpr rd, ()) =>
    if !(Nat.beq m n && Nat.ble n 64) then none
    else if holdsVarGprZ I st.regs x rd then some (rd, true, Nat.beq n 32)
    else if !hasVarGprW I st.regs x rd then none
    else if I.gpr.elideZext32 && Nat.beq n 32 &&
        I.gpr.zeroUpper32Op (.bitcast (.bits m) (.bits n) hsz) (.gpr rd, ()) (.gpr rd, ()) then
      if st.zeroExt32.contains rd then some (rd, true, true) else none
    else
      let isZ := Nat.beq n 32 && st.zeroExt32.contains rd
      some (rd, isZ, isZ)
  | _, _, _, _, _ => none

/-! ## GPR-Preferred Immediate Operands (`OPT-7c`) -/

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

/-- `tryArg`, consulting `preferReg` on `.bits n, .imm c` to try a live GPR before inline imm. -/
def tryArgPref (I : Isa) (st : SymState I) (pref : List I.Cond) (preferReg : Bool) {α : Type}
    (t : Ty) (a : Arg VNat t) (k : PArg I.Reg I.VReg I.Cond t → Option α) : Option α :=
  match t, a with
  | .bool, .var x =>
    tryFlag I st.regs pref (.var x) (fun c => k (.flag c)) <|>
      tryGpr I st.regs (.var x) (fun r => k (.gpr r))
  | .bool, .imm b =>
    tryFlag I st.regs pref (.immBool b) (fun c => k (.flag c)) <|> k (.imm b) <|>
      tryGpr I st.regs (.immBool b) (fun r => k (.gpr r))
  | .bits _, .var x => tryGpr I st.regs (.var x) (fun r => k (.gpr r))
  | .bits n, .imm c =>
    if Nat.ble n 64 && preferReg then
      tryGpr I st.regs (.immBits n (c.setWidth 64)) (fun r => k (.gpr r)) <|> k (.imm c)
    else
      k (.imm c) <|>
        if Nat.ble n 64 then tryGpr I st.regs (.immBits n (c.setWidth 64)) (fun r => k (.gpr r))
        else none
  | .pair _ _, .var x => tryVec I st.regs (.var x) (fun v => k (.vec v))
  | .pair a b, .imm c =>
    k (.imm c) <|> match vecWidth? I (.pair a b) with
      | none => none
      | some w =>
        tryVec I st.regs (.immVec w ((toBits (.pair a b) c).setWidth 512)) (fun v => k (.vec v))
  | .float _, _ => none

/-- `pickPArgs` variant consulting `I.gpr.preferRegImm?` for `code`. -/
def pickPArgsCode (I : Isa) (st : SymState I) (pref : List I.Cond) {sig₀ rs₀ : List Ty}
    (code : OpCode sig₀ rs₀) {α : Type} :
    {sig : List Ty} → Tup (Arg VNat) sig →
    (Tup (PArg I.Reg I.VReg I.Cond) sig → Option α) → Option α
  | [], (), k => k ()
  | t :: _, (a, as), k =>
    let pReg := match t, a, I.gpr.preferRegImm? with
      | .bits n, .imm c, some fn => fn code n (c.setWidth 64)
      | _, _, _ => false
    tryArgPref I st pref pReg t a fun pa =>
      pickPArgsCode I st pref code as fun pas => k (pa, pas)

/-! ## Factored Helpers from `Rega.lean` -/

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

def recordAddScale (defs : Trie DefFact) (dfx : DefFact) (dfy? : Option DefFact) (y : Nat) :
    Option DefFact :=
  match dfx with
  | .scaleOff idx sh d1 =>
    if Nat.ble sh 3 then
      match dfy? with
      | some (.addImm64 b d2) =>
        if isScaledAddrSum defs b then some (.addrSum y idx sh d1)
        else some (.addrSum b idx sh (d1 + d2))
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
    let s1 := dfx?.bind (recordAddScale defs · dfy? y)
    let s2 := dfy?.bind (recordAddScale defs · dfx? x)
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
  | _, _, .neg (.bits n), (.var x, ()) =>
    if Nat.ble n 64 then some (.negVar n x) else none
  | _, _, _, _ => none

/-- `recordDef`, except that under `cse` an `x ± c` over a scaled `addrSum` `x` is recorded as
`addImm64 x (±c)` (`recordDef` over empty facts), keeping `x` as the shared base register. -/
def recordDefC (cse : Bool) (defs : Trie DefFact) {sig rs : List Ty} (code : OpCode sig rs)
    (args : Tup (Arg VNat) sig) : Option DefFact :=
  if addrCseHit defs code args && cse then recordDef .empty code args
  else recordDef defs code args

/-! ## Shared `tryArg`, `tryAddr`, and Scratch-Aware / Narrowing Lowering Helpers -/

@[reducible] def tryArg (I : Isa) (st : SymState I) (pref : List I.Cond) {α : Type}
    (t : Ty) (a : Arg VNat t) (k : PArg I.Reg I.VReg I.Cond t → Option α) : Option α :=
  tryArgPref I st pref false t a k

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

/-- Scratch-constant-aware GPR load lowering (`loadScr?`/`loadZextIdxScr?` with fallback). -/
def lowerLoadScr (I : Isa) (st1 : SymState I) (vh : VariantHint) (t : Ty) (d : I.Reg)
    (a : Arg VNat i64) : Option (List I.Directive × FlagMask × List (I.Reg × BitVec 64)) :=
  (I.gpr.loadScr?.bind fun fn => tryAddr I st1 vh a (fn st1.scrConsts t d)) <|>
    (I.gpr.loadZextIdxScr?.bind fun fn => tryAddrZext I st1 a (fn st1.scrConsts t d)) <|>
    ((tryAddr I st1 vh a (I.gpr.load t d) <|>
      tryAddrZext I st1 a (I.gpr.loadZextIdx t d)).map fun (c, cl) => (c, cl, []))

/-- Scratch-constant-aware GPR store lowering (`storeScr?`/`storeZextIdxScr?` with fallback). -/
def lowerStoreScr (I : Isa) (st1 : SymState I) (vh : VariantHint) (t : Ty)
    (pa : PArg I.Reg I.VReg I.Cond t) (a : Arg VNat i64) :
    Option (List I.Directive × FlagMask × List (I.Reg × BitVec 64)) :=
  (I.gpr.storeScr?.bind fun fn => tryAddr I st1 vh a (fn st1.scrConsts t pa)) <|>
    (I.gpr.storeZextIdxScr?.bind fun fn => tryAddrZext I st1 a (fn st1.scrConsts t pa)) <|>
    ((tryAddr I st1 vh a (I.gpr.store t pa) <|>
      tryAddrZext I st1 a (I.gpr.storeZextIdx t pa)).map fun (c, cl) => (c, cl, []))

/-- `true` when `code` is an integer comparison `.cmp` producing `.bool`. -/
def isCmpOp {sig rs : List Ty} (code : OpCode sig rs) : Bool :=
  match sig, code with
  | [.bits _, .bits _], .cmp _ (.bits _) .bool _ => true
  | _, _ => false

/-- Whether scalar `op` must bypass `opScr?` so flag-output specs (`boolFlagOut?`/`aluZeroOut?`) hold. -/
def usePlainOp (I : Isa) {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg I.Reg I.VReg I.Cond) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) rs) : Bool :=
  match rs with
  | [.bool] =>
    match dsts with
    | (.gpr rd, ()) => !isCmpOp code && (I.gpr.boolFlagOut? code pas (.gpr rd)).isSome
    | _ => false
  | [.bits w] => Nat.ble w 64 && (I.gpr.aluZeroOut? w code dsts.1).isSome
  | _ => false

/-- Scratch-constant-aware scalar `op` lowering (`opScr?` when present, else `op`). -/
def lowerOpScr (I : Isa) (st1 : SymState I) (vh : VariantHint) {sig rs : List Ty}
    (code : OpCode sig rs) (pas : Tup (PArg I.Reg I.VReg I.Cond) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) rs) :
    Option (List I.Directive × FlagMask × List (I.Reg × BitVec 64)) :=
  if usePlainOp I code pas dsts then
    (I.gpr.op code pas dsts vh).map fun (c, cl) => (c, cl, [])
  else match I.gpr.opScr? with
    | some fn => fn st1.scrConsts code pas dsts vh
    | none => (I.gpr.op code pas dsts vh).map fun (c, cl) => (c, cl, [])

/-- Fuse `.trunc m n` of an elided `.load (.bits m)` (`memDefs`) into a narrow `.bits n` load. -/
def tryLoadTrunc (I : Isa) (st : SymState I) (vh : VariantHint) {sig ts : List Ty}
    (code : OpCode sig ts) (args : Tup (Arg VNat) sig)
    (dsts : Tup (PDst I.Reg I.VReg I.Cond) ts) :
    Option (List I.Directive × FlagMask × Bool × Bool × List (I.Reg × BitVec 64)) :=
  match sig, ts, code, args, dsts with
  | _, _, .trunc m n, (.var x, ()), (.gpr rd, ()) =>
    if !((Nat.beq m 16 || Nat.beq m 32 || Nat.beq m 64) &&
        (Nat.beq n 8 || Nat.beq n 16 || Nat.beq n 32) && Nat.blt n m && isGprTy I (.bits n)) then
      none
    else match st.memDefs.find? x with
      | some (.bits m', addr) =>
        if Nat.beq m' m then
          (lowerLoadScr I st vh (.bits n) rd addr).map fun (c, cl, scr) =>
            let isZ32 := Nat.beq n 32 && I.gpr.zeroUpper32Load
            (c, cl, I.gpr.zeroExtLoad || isZ32, isZ32, scr)
        else none
      | _ => none
  | _, _, _, _, _ => none

/-- Lower dead-low `umulw`/`smulw` via `I.gpr.mulHi?`, targeting `h.dest.find? (nv + 1)`. -/
def tryMulHi (I : Isa) (h : I.Hints) (st1 : SymState I) (nv : Nat)
    {sig ts : List Ty} (code : OpCode sig ts) (args : Tup (Arg VNat) sig) :
    Option (List I.Directive × FlagMask × I.Reg) :=
  match I.gpr.mulHi?, sig, ts, code, args with
  | some fn, _, _, .umulw n, (a, b, ()) =>
    match h.dest.find? (nv + 1) with
    | some (.gpr dhi) =>
      if isAllocGpr I h.saved dhi && isGprTy I (.bits n) then
        tryArg I st1 [] (.bits n) a fun pa =>
          tryArg I st1 [] (.bits n) b fun pb =>
            (fn false n pa pb dhi).map fun (c, cl) => (c, cl, dhi)
      else none
    | _ => none
  | some fn, _, _, .smulw n, (a, b, ()) =>
    match h.dest.find? (nv + 1) with
    | some (.gpr dhi) =>
      if isAllocGpr I h.saved dhi && isGprTy I (.bits n) then
        tryArg I st1 [] (.bits n) a fun pa =>
          tryArg I st1 [] (.bits n) b fun pb =>
            (fn true n pa pb dhi).map fun (c, cl) => (c, cl, dhi)
      else none
    | _ => none
  | _, _, _, _, _ => none

end Rega
end LeanQbe.T
