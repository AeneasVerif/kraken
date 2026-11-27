module

public import LeanQbe.T.Arm64.IselCore

/-!
# AArch64 Wave 6.2-A Scratch-Constant, Zext & `mulHi` Lowering (`Arm64.IselScr`)

Implements the opt-in `GprIsa` hooks for:
* `OPT-7b` intra-block scratch-constant reuse (`armStoreScr`, `armStoreZextIdxScr`,
  `armLoadScr`, `armLoadZextIdxScr`, `armBinOpScr`, `armCmpOpScr`, `armSelectOpScr`);
* `OPT-7c` immediate-to-GPR / loop-constant preference (`armPreferRegImm`,
  `armPreferStoreRegImm`);
* `OPT-10a` canonical 64-bit zero-extension oracle (`armZeroExtOp`);
* `OPT-10c` dead-low `umulw`/`smulw` high-product lowering (`armMulHi`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Scratch-Constant Cache Helpers (`OPT-7b`) -/

/-- Drop scratch-constant cache entries whose register appears in `gClob`. -/
def armKillScr (gClob : List Reg) (scr : List (Reg × BitVec 64)) : List (Reg × BitVec 64) :=
  scr.filter fun (r, _) => !gClob.contains r

/-- `true` iff `scr` currently maps `.reg tmp` to exact 64-bit constant `c64`. -/
def armHasScr (scr : List (Reg × BitVec 64)) (tmp : XReg) (c64 : BitVec 64) : Bool :=
  scr.any fun (r, v) => r == .reg tmp && v == c64

/-- Record `.reg tmp ↦ c64` in `scr`, dropping any prior entry for `.reg tmp`. -/
def armSetScr (scr : List (Reg × BitVec 64)) (tmp : XReg) (c64 : BitVec 64) :
    List (Reg × BitVec 64) :=
  (.reg tmp, c64) :: armKillScr [.reg tmp] scr

/-- Materialize `c64` into `tmp`, emitting `[]` when `scr` already holds `.reg tmp ↦ c64`. -/
def armMovImmScr (scr : List (Reg × BitVec 64)) (tmp : XReg) (c64 : BitVec 64) :
    List Instr × List (Reg × BitVec 64) :=
  if armHasScr scr tmp c64 then ([], scr)
  else (armMovImmI tmp c64, armSetScr scr tmp c64)

/-- Scratch-aware `armArgInIns`, reusing `tmp` if already holding `c.setWidth 64`. -/
def armArgInScr (scr : List (Reg × BitVec 64)) (tmp : XReg) {n : Nat} :
    PArg Reg Empty ArmCond (.bits n) → Option (List Instr × XReg × List (Reg × BitVec 64))
  | .gpr (.reg r) => some ([], r, scr)
  | .gpr .SP => none
  | .imm c =>
    let (ins, scr') := armMovImmScr scr tmp (c.setWidth 64)
    some (ins, tmp, scr')

/-- Scratch-aware `armSetupAddrIns` (`setup.isEmpty` keeps `scr`; non-empty address setup via
`.imm` or non-scaled `.baseDisp (.reg _)` reuses `.X16`; `.SP` / idx-disp kills `.X16`). -/
def armSetupAddrScr (scr : List (Reg × BitVec 64)) (scale : Nat) :
    AddrArg Reg → List Instr × AddrExpr × List (Reg × BitVec 64)
  | .imm addr =>
    let (c, scr') := armMovImmScr scr .X16 addr
    (c, atReg .X16, scr')
  | .baseDisp (.reg rb) disp =>
    if disp == 0 then ([], atReg rb, scr)
    else if armFitsScaledOff scale disp then ([], armAtDisp rb disp, scr)
    else
      let (c, scr') := armMovImmScr scr .X16 disp.toBitVec
      (c, armAtIdx rb .X16, scr')
  | a =>
    let (setup, addr) := armSetupAddrIns scale a
    let scr' := if setup.isEmpty then scr else armKillScr [.reg .X16] scr
    (setup, addr, scr')

/-! ## 2. Scratch-Aware Store and Load Builders (`armStoreScr`, `armLoadScr`) -/

/-- Scratch-aware `armStoreValInIns`, reusing `.X17` across consecutive constant stores. -/
def armStoreValInScr (scr : List (Reg × BitVec 64)) :
    (t : Ty) → PArg Reg Empty ArmCond t → Option (List Instr × XRegOrXzr × List (Reg × BitVec 64))
  | .bool, .gpr (.reg r) => some ([], .reg r, scr)
  | .bool, .gpr .SP => some ([armIselMovToXI .X17 .SP], .reg .X17, armKillScr [.reg .X17] scr)
  | .bool, .imm false => some ([], .XZR, scr)
  | .bool, .imm true =>
    let (c, scr') := armMovImmScr scr .X17 1#64
    some (c, .reg .X17, scr')
  | .bool, .flag c => some ([armCset64I .X17 c], .reg .X17, armKillScr [.reg .X17] scr)
  | .bits _, .gpr (.reg r) => some ([], .reg r, scr)
  | .bits _, .gpr .SP => some ([armIselMovToXI .X17 .SP], .reg .X17, armKillScr [.reg .X17] scr)
  | .bits n, .imm c =>
    if c == 0#n then some ([], .XZR, scr)
    else
      let (ci, scr') := armMovImmScr scr .X17 (c.setWidth 64)
      some (ci, .reg .X17, scr')
  | _, _ => none

/-- Scratch-aware `armStore` (`Instr` builder). -/
def armStoreScrIns (scr : List (Reg × BitVec 64)) (t : Ty) (pa : PArg Reg Empty ArmCond t)
    (a : AddrArg Reg) : Option (List Instr × FlagMask × List (Reg × BitVec 64)) := do
  let scale ← armMemScale t
  if !armAddrValid scale a then none
  else
    let (valSetup, rx, scr1) ← armStoreValInScr scr t pa
    let (addrSetup, addr, scr2) := armSetupAddrScr scr1 scale a
    let dir ← armStoreDirI t rx addr
    some (valSetup ++ addrSetup ++ [dir], maskNone, scr2)

/-- Scratch-aware `armStore` returning clean directives, flags, and updated scratch cache. -/
def armStoreScr (scr : List (Reg × BitVec 64)) (t : Ty) (pa : PArg Reg Empty ArmCond t)
    (a : AddrArg Reg) : Option (List Directive × FlagMask × List (Reg × BitVec 64)) :=
  (armStoreScrIns scr t pa a).map fun (c, cl, scr') => (emitClean c, cl, scr')

/-- Scratch-aware `armStoreZextIdx` (`Instr` builder). -/
def armStoreZextIdxScrIns (scr : List (Reg × BitVec 64)) (t : Ty) (pa : PArg Reg Empty ArmCond t)
    (base idx : Reg) (sc : AddrScale) (disp : Int64) :
    Option (List Instr × FlagMask × List (Reg × BitVec 64)) := do
  let scale ← armMemScale t
  let (addrSetup, addr) ← armSetupAddrZextIns scale base idx sc disp
  let scr1 := if addrSetup.isEmpty then scr else armKillScr [.reg .X16] scr
  let (valSetup, rx, scr2) ← armStoreValInScr scr1 t pa
  let dir ← armStoreDirI t rx addr
  some (valSetup ++ addrSetup ++ [dir], maskNone, scr2)

/-- Scratch-aware `armStoreZextIdx`. -/
def armStoreZextIdxScr (scr : List (Reg × BitVec 64)) (t : Ty) (pa : PArg Reg Empty ArmCond t)
    (base idx : Reg) (sc : AddrScale) (disp : Int64) :
    Option (List Directive × FlagMask × List (Reg × BitVec 64)) :=
  (armStoreZextIdxScrIns scr t pa base idx sc disp).map fun (c, cl, scr') => (emitClean c, cl, scr')

/-- Scratch-aware `armLoad` (`Instr` builder). -/
def armLoadScrIns (scr : List (Reg × BitVec 64)) (t : Ty) (rd : Reg) (a : AddrArg Reg) :
    Option (List Instr × FlagMask × List (Reg × BitVec 64)) := do
  let scale ← armMemScale t
  if !armAddrValid scale a then none
  else
    let (setup, addr, scr1) := armSetupAddrScr scr scale a
    let (ci, cl) ← armLoadTailIns t rd setup addr
    let scrOut := match rd with | .reg _ => scr1 | .SP => armKillScr [.reg .X16] scr1
    some (ci, cl, scrOut)

/-- Scratch-aware `armLoad`. -/
def armLoadScr (scr : List (Reg × BitVec 64)) (t : Ty) (rd : Reg) (a : AddrArg Reg) :
    Option (List Directive × FlagMask × List (Reg × BitVec 64)) :=
  (armLoadScrIns scr t rd a).map fun (c, cl, scr') => (emitClean c, cl, scr')

/-- Scratch-aware `armLoadZextIdx` (`Instr` builder). -/
def armLoadZextIdxScrIns (scr : List (Reg × BitVec 64)) (t : Ty) (rd base idx : Reg)
    (sc : AddrScale) (disp : Int64) : Option (List Instr × FlagMask × List (Reg × BitVec 64)) := do
  let scale ← armMemScale t
  let (setup, addr) ← armSetupAddrZextIns scale base idx sc disp
  let scr1 := if setup.isEmpty then scr else armKillScr [.reg .X16] scr
  let (ci, cl) ← armLoadTailIns t rd setup addr
  let scrOut := match rd with | .reg _ => scr1 | .SP => armKillScr [.reg .X16] scr1
  some (ci, cl, scrOut)

/-- Scratch-aware `armLoadZextIdx`. -/
def armLoadZextIdxScr (scr : List (Reg × BitVec 64)) (t : Ty) (rd base idx : Reg)
    (sc : AddrScale) (disp : Int64) :
    Option (List Directive × FlagMask × List (Reg × BitVec 64)) :=
  (armLoadZextIdxScrIns scr t rd base idx sc disp).map fun (c, cl, scr') => (emitClean c, cl, scr')

/-! ## 3. Scratch-Aware Binary ALU, Compare, and Select Builders (`armOpScr`) -/

/-- Scratch-aware `armMulRegImmIns`. -/
def armMulRegImmScrIns (scr : List (Reg × BitVec 64)) {n : Nat} (w : RegWidth) (d r : XReg)
    (imm : BitVec n) : List Instr × List (Reg × BitVec 64) :=
  if imm == 0#n then (armMovImmI d 0#64, scr)
  else if imm == ~~~0#n then ([armIselInsI (.SUB_s (zr d w) (xzr w) (sh r))], scr)
  else match armPow2Shift? imm with
    | some k =>
      let ins := if k == 0 then armIselInsI (.ORR_s (zr d w) (xzr w) (sh r))
        else armIselInsI (.UBFM (zr d w) (zr r w) ((w.bits - k) % w.bits) (w.bits - 1 - k))
      ([ins], scr)
    | none => match armPow2Plus1Shift? imm with
      | some k =>
        ([armIselInsI (.ADD_s (zr d w) (zr r w)
            { reg := zr r w, amount := Int64.ofNat k, shift := .LSL })], scr)
      | none =>
        let (ci, scr') := armMovImmScr scr .X17 (imm.setWidth 64)
        (ci ++ [armBinDirI .mul w d r .X17], scr')

/-- Scratch-aware `armBinOpIns`. -/
def armBinOpScrIns (scr : List (Reg × BitVec 64)) (k : ArmBinK) (n : Nat)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Instr × FlagMask × List (Reg × BitVec 64)) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let w := armWidthOf n
    match k, pa, pb with
    | .add, .gpr (.reg ra), .imm cb =>
      match armAddSubImmI? false w d ra cb with
      | some dir => some ([dir], maskNone, scr)
      | none =>
        let (cb', rb, scr') ← armArgInScr scr .X17 pb
        some (cb' ++ [armBinDirI k w d ra rb], maskNone, scr')
    | .add, .imm ca, .gpr (.reg rb) =>
      match armAddSubImmI? false w d rb ca with
      | some dir => some ([dir], maskNone, scr)
      | none =>
        let (ca', ra, scr') ← armArgInScr scr .X16 pa
        some (ca' ++ [armBinDirI k w d ra rb], maskNone, scr')
    | .sub, .gpr (.reg ra), .imm cb =>
      match armAddSubImmI? true w d ra cb with
      | some dir => some ([dir], maskNone, scr)
      | none =>
        let (cb', rb, scr') ← armArgInScr scr .X17 pb
        some (cb' ++ [armBinDirI k w d ra rb], maskNone, scr')
    | .sub, .imm ca, .gpr (.reg rb) =>
      if ca == 0#n then
        some ([armIselInsI (.SUB_s (zr d w) (xzr w) (sh rb))], maskNone, scr)
      else if ca == ~~~0#n then
        some ([armIselInsI (.ORN_s (zr d w) (xzr w) (sh rb))], maskNone, scr)
      else
        let (ca', ra, scr') ← armArgInScr scr .X16 pa
        some (ca' ++ [armBinDirI k w d ra rb], maskNone, scr')
    | .mul, .gpr (.reg ra), .imm cb =>
      let (ci, scr') := armMulRegImmScrIns scr w d ra cb
      some (ci, maskNone, scr')
    | .mul, .imm ca, .gpr (.reg rb) =>
      let (ci, scr') := armMulRegImmScrIns scr w d rb ca
      some (ci, maskNone, scr')
    | .and, .gpr (.reg ra), .imm cb
    | .or, .gpr (.reg ra), .imm cb
    | .xor, .gpr (.reg ra), .imm cb =>
      let c64 := cb.setWidth 64
      if armIsValidLogicalImm w c64 then
        let dir ← armLogicImmDirI k w d ra (Int64.ofBitVec c64)
        some ([dir], maskNone, scr)
      else if (n == 8 || n == 16) && armIsValidLogicalImm .W32 (cb.signExtend 64) then
        let dir ← armLogicImmDirI k .W32 d ra (Int64.ofBitVec (cb.signExtend 64))
        some ([dir], maskNone, scr)
      else
        let (cb', rb, scr') ← armArgInScr scr .X17 pb
        some (cb' ++ [armBinDirI k w d ra rb], maskNone, scr')
    | .and, .imm ca, .gpr (.reg rb)
    | .or, .imm ca, .gpr (.reg rb)
    | .xor, .imm ca, .gpr (.reg rb) =>
      let c64 := ca.setWidth 64
      if armIsValidLogicalImm w c64 then
        let dir ← armLogicImmDirI k w d rb (Int64.ofBitVec c64)
        some ([dir], maskNone, scr)
      else if (n == 8 || n == 16) && armIsValidLogicalImm .W32 (ca.signExtend 64) then
        let dir ← armLogicImmDirI k .W32 d rb (Int64.ofBitVec (ca.signExtend 64))
        some ([dir], maskNone, scr)
      else
        let (ca', ra, scr') ← armArgInScr scr .X16 pa
        some (ca' ++ [armBinDirI k w d ra rb], maskNone, scr')
    | _, _, _ =>
      let (ca, ra, scr1) ← armArgInScr scr .X16 pa
      let (cb, rb, scr2) ← armArgInScr scr1 .X17 pb
      some (ca ++ cb ++ [armBinDirI k w d ra rb], maskNone, scr2)

/-- Scratch-aware `armSelectCondIns`. -/
def armSelectCondScrIns (scr : List (Reg × BitVec 64)) (n : Nat) (cond : ArmCond)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (d : XReg) :
    Option (List Instr × List (Reg × BitVec 64)) :=
  let w := armWidthOf n
  let mkSel (ra rb : XRegOrXzr) (op : Nat) (cnd : ArmCond) : Instr :=
    match op with
    | 0 => armIselInsI (.CSEL (zr d w) (.low ra w) (.low rb w) cnd.toKraken)
    | 1 => armIselInsI (.CSINC (zr d w) (.low ra w) (.low rb w) cnd.toKraken)
    | _ => armIselInsI (.CSINV (zr d w) (.low ra w) (.low rb w) cnd.toKraken)
  match pa, pb with
  | .imm ca, .imm cb =>
    if ca == cb then some (armMovImmI d (ca.setWidth 64), scr)
    else if ca == 1#n && cb == 0#n then some ([mkSel .XZR .XZR 1 (armNegCond cond)], scr)
    else if ca == 0#n && cb == 1#n then some ([mkSel .XZR .XZR 1 cond], scr)
    else if ca == ~~~0#n && cb == 0#n then some ([mkSel .XZR .XZR 2 (armNegCond cond)], scr)
    else if ca == 0#n && cb == ~~~0#n then some ([mkSel .XZR .XZR 2 cond], scr)
    else if cb == 0#n then do
      let (ca', ra, scr') ← armArgInScr scr .X16 pa
      some (ca' ++ [mkSel (.reg ra) .XZR 0 cond], scr')
    else if cb == 1#n then do
      let (ca', ra, scr') ← armArgInScr scr .X16 pa
      some (ca' ++ [mkSel (.reg ra) .XZR 1 cond], scr')
    else if cb == ~~~0#n then do
      let (ca', ra, scr') ← armArgInScr scr .X16 pa
      some (ca' ++ [mkSel (.reg ra) .XZR 2 cond], scr')
    else if ca == 0#n then do
      let (cb', rb, scr') ← armArgInScr scr .X17 pb
      some (cb' ++ [mkSel (.reg rb) .XZR 0 (armNegCond cond)], scr')
    else if ca == 1#n then do
      let (cb', rb, scr') ← armArgInScr scr .X17 pb
      some (cb' ++ [mkSel (.reg rb) .XZR 1 (armNegCond cond)], scr')
    else if ca == ~~~0#n then do
      let (cb', rb, scr') ← armArgInScr scr .X17 pb
      some (cb' ++ [mkSel (.reg rb) .XZR 2 (armNegCond cond)], scr')
    else do
      let (ca', ra, scr1) ← armArgInScr scr .X16 pa
      let (cb', rb, scr2) ← armArgInScr scr1 .X17 pb
      some (ca' ++ cb' ++ [mkSel (.reg ra) (.reg rb) 0 cond], scr2)
  | .gpr (.reg ra), .imm cb =>
    if cb == 0#n then some ([mkSel (.reg ra) .XZR 0 cond], scr)
    else if cb == 1#n then some ([mkSel (.reg ra) .XZR 1 cond], scr)
    else if cb == ~~~0#n then some ([mkSel (.reg ra) .XZR 2 cond], scr)
    else do
      let (cb', rb, scr') ← armArgInScr scr .X17 pb
      some (cb' ++ [mkSel (.reg ra) (.reg rb) 0 cond], scr')
  | .imm ca, .gpr (.reg rb) =>
    if ca == 0#n then some ([mkSel (.reg rb) .XZR 0 (armNegCond cond)], scr)
    else if ca == 1#n then some ([mkSel (.reg rb) .XZR 1 (armNegCond cond)], scr)
    else if ca == ~~~0#n then some ([mkSel (.reg rb) .XZR 2 (armNegCond cond)], scr)
    else do
      let (ca', ra, scr') ← armArgInScr scr .X16 pa
      some (ca' ++ [mkSel (.reg ra) (.reg rb) 0 cond], scr')
  | _, _ => do
    let (ca, ra, scr1) ← armArgInScr scr .X16 pa
    let (cb, rb, scr2) ← armArgInScr scr1 .X17 pb
    some (ca ++ cb ++ [mkSel (.reg ra) (.reg rb) 0 cond], scr2)

/-- Scratch-aware `armSelectOpIns`. -/
def armSelectOpScrIns (scr : List (Reg × BitVec 64)) (n : Nat)
    (pc : PArg Reg Empty ArmCond .bool) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (d : XReg) : Option (List Instr × FlagMask × List (Reg × BitVec 64)) := do
  if ![8, 16, 32, 64].contains n then none
  else match pc with
    | .imm true => (armCopyBitsIns n pa d).map fun (c, cl) => (c, cl, scr)
    | .imm false => (armCopyBitsIns n pb d).map fun (c, cl) => (c, cl, scr)
    | .flag cond =>
      let (sel, scr') ← armSelectCondScrIns scr n cond pa pb d
      some (sel, maskNone, scr')
    | .gpr (.reg rc) =>
      let (sel, scr') ← armSelectCondScrIns scr n .ne pa pb d
      some (armIselInsI (.ANDS_i (xzr .W32) (zr rc .W32) (.int64 1)) :: sel, maskNZCV, scr')
    | .gpr .SP => none

/-- Scratch-aware `armCmpOpIns`. -/
def armCmpOpScrIns (scr : List (Reg × BitVec 64)) (o : CmpOp) (n : Nat)
    (pa pb : PArg Reg Empty ArmCond (.bits n)) (dst : PDst Reg Empty ArmCond .bool) :
    Option (List Instr × FlagMask × List (Reg × BitVec 64)) := do
  if ![8, 16, 32, 64].contains n then none
  else
    let finish (cmpCode : List Instr) (cond : ArmCond) (scrOut : List (Reg × BitVec 64)) :
        Option (List Instr × FlagMask × List (Reg × BitVec 64)) :=
      match dst with
      | .flag c => if c == cond then some (cmpCode, maskNZCV, scrOut) else none
      | .gpr (.reg d) => some (cmpCode ++ [armCset64I d cond], maskNZCV, scrOut)
      | .gpr .SP | .vec _ => none
    match pa, pb with
    | .gpr (.reg ra), .imm cb =>
      if cb == 0#n then
        match armZeroCmpIns? o n ra dst with
        | some (ci, cl) => some (ci, cl, scr)
        | none =>
          if n == 32 || n == 64 then
            match armCmpImmIns? (armWidthOf n) ra cb with
            | some cmp => finish cmp (armCmpCond o) scr
            | none => none
          else
            let ext := armExt32I (armIsSignedCmp o) n .X16 ra
            match armCmpImmIns? .W32 .X16 0#32 with
            | some cmp => finish (ext :: cmp) (armCmpCond o) (armKillScr [.reg .X16] scr)
            | none => none
      else if n == 32 || n == 64 then
        let w := armWidthOf n
        match armCmpImmIns? w ra cb with
        | some cmp => finish cmp (armCmpCond o) scr
        | none =>
          let (cb', rb, scr') ← armArgInScr scr .X17 pb
          finish (cb' ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o) scr'
      else
        let sgn := armIsSignedCmp o
        let c32 := if sgn then cb.signExtend 32 else cb.setWidth 32
        let ext := armExt32I sgn n .X16 ra
        let scr1 := armKillScr [.reg .X16] scr
        match armCmpImmIns? .W32 .X16 c32 with
        | some cmp => finish (ext :: cmp) (armCmpCond o) scr1
        | none =>
          let (ci17, scr2) := armMovImmScr scr1 .X17 (c32.setWidth 64)
          finish (ext :: ci17 ++ [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
            (armCmpCond o) scr2
    | .imm ca, .gpr (.reg rb) =>
      if ca == 0#n then
        match armZeroCmpIns? o.swap n rb dst with
        | some (ci, cl) => some (ci, cl, scr)
        | none =>
          if n == 32 || n == 64 then
            match armCmpImmIns? (armWidthOf n) rb ca with
            | some cmp => finish cmp (armCmpCond o.swap) scr
            | none => none
          else
            let ext := armExt32I (armIsSignedCmp o) n .X16 rb
            match armCmpImmIns? .W32 .X16 0#32 with
            | some cmp => finish (ext :: cmp) (armCmpCond o.swap) (armKillScr [.reg .X16] scr)
            | none => none
      else if n == 32 || n == 64 then
        let w := armWidthOf n
        match armCmpImmIns? w rb ca with
        | some cmp => finish cmp (armCmpCond o.swap) scr
        | none =>
          let (ca', ra, scr') ← armArgInScr scr .X16 pa
          finish (ca' ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o) scr'
      else
        let sgn := armIsSignedCmp o
        let c32 := if sgn then ca.signExtend 32 else ca.setWidth 32
        let ext := armExt32I sgn n .X16 rb
        let scr1 := armKillScr [.reg .X16] scr
        match armCmpImmIns? .W32 .X16 c32 with
        | some cmp => finish (ext :: cmp) (armCmpCond o.swap) scr1
        | none =>
          let (ci17, scr2) := armMovImmScr scr1 .X17 (c32.setWidth 64)
          finish (ext :: ci17 ++ [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
            (armCmpCond o.swap) scr2
    | _, _ =>
      let (ca, ra, scr1) ← armArgInScr scr .X16 pa
      let (cb, rb, scr2) ← armArgInScr scr1 .X17 pb
      if n == 32 || n == 64 then
        let w := armWidthOf n
        finish (ca ++ cb ++ [armIselInsI (.SUBS_s (xzr w) (zr ra w) (sh rb))]) (armCmpCond o) scr2
      else
        let sgn := armIsSignedCmp o
        finish (ca ++ cb ++ [armExt32I sgn n .X16 ra, armExt32I sgn n .X17 rb,
          armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))])
          (armCmpCond o) (armKillScr [.reg .X16, .reg .X17] scr2)

/-! ## 4. Dead-Low Multiply-High (`armMulHi`, `OPT-10c`) -/

/-- Emit only the high product of `umulw`/`smulw` when `lo` is dead (`Instr` builder). -/
def armMulHiIns (isSigned : Bool) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (rd : Reg) : Option (List Instr × FlagMask) := do
  if !(n == 32 || n == 64) then none
  else
    let dhi ← match rd with | .reg d => some d | .SP => none
    let (ca, ra) ← armArgInIns .X16 pa
    let (cb, rb) ← armArgInIns .X17 pb
    if n == 32 then
      let mul64 :=
        if isSigned then armIselInsI (.SMADDL (zr .X16 .W64) (zr ra .W32) (zr rb .W32) (xzr .W64))
        else armIselInsI (.UMADDL (zr .X16 .W64) (zr ra .W32) (zr rb .W32) (xzr .W64))
      some (ca ++ cb ++ [mul64, armIselInsI (.UBFM (zr dhi .W64) (zr .X16 .W64) 32 63)], maskNone)
    else
      let mulH :=
        if isSigned then armIselInsI (.SMULH (zr dhi .W64) (zr ra .W64) (zr rb .W64))
        else armIselInsI (.UMULH (zr dhi .W64) (zr ra .W64) (zr rb .W64))
      some (ca ++ cb ++ [mulH], maskNone)

/-- High-half multiply (`umulh`/`smulh`, or `umaddl`/`smaddl .X16` + `lsr #32`). -/
def armMulHi (isSigned : Bool) (n : Nat) (pa pb : PArg Reg Empty ArmCond (.bits n))
    (rd : Reg) : Option (List Directive × FlagMask) :=
  emitCleanPair (armMulHiIns isSigned n pa pb rd)

/-! ## 5. Zero-Extension Oracle (`OPT-10a`) & Immediate-Preference (`OPT-7c`) -/

/-- `true` when `pas` contains no `.gpr _` argument. -/
def armHasNoGprArg : {sig : List Ty} → Tup (PArg Reg Empty ArmCond) sig → Bool
  | [], () => true
  | _ :: _, (.gpr _, _) => false
  | _ :: _, (_, pas) => armHasNoGprArg pas

/-- Canonical 64-bit `AbiGprHolds` guarantee on `armGpr.op` outputs (`OPT-10a`). -/
def armZeroExtOp {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg Empty ArmCond) sig) (dsts : Tup (PDst Reg Empty ArmCond) rs) : Bool :=
  let dstOk : Bool := match rs, dsts with
    | [_], (.gpr (.reg _), ()) => true
    | _, _ => false
  if !dstOk then false
  else match code with
    | .zext _ n => [8, 16, 32, 64].contains n
    | .ofBool n => [8, 16, 32, 64].contains n
    | .cmp _ (.bits _) .bool _ => true
    | .copy .bool | .not .bool | .and .bool | .or .bool | .xor .bool => armHasNoGprArg pas
    | _ => match rs with
      | [.bits n] => n == 32
      | _ => false

/-- `true` when immediate `c64` at width `n` forces scratch literal load in `code` (`OPT-7c`). -/
def armPreferRegImm : {sig rs : List Ty} → OpCode sig rs → Nat → BitVec 64 → Bool
  | _, _, .add (.bits _), n, c64 =>
    if ![8, 16, 32, 64].contains n then false
    else (armAddSubImmI? false (armWidthOf n) .X16 .X16 (c64.setWidth n)).isNone
  | _, _, .sub (.bits _), n, c64 =>
    if ![8, 16, 32, 64].contains n then false
    else
      let cw : BitVec n := c64.setWidth n
      cw != 0#n && cw != ~~~0#n && (armAddSubImmI? true (armWidthOf n) .X16 .X16 cw).isNone
  | _, _, .cmp o (.bits _), n, c64 =>
    if n == 8 || n == 16 then
      let sgn := armIsSignedCmp o
      let cb : BitVec n := c64.setWidth n
      let c32 := if sgn then cb.signExtend 32 else cb.setWidth 32
      c32 != 0#32 && (armCmpImmIns? .W32 .X16 c32).isNone
    else if n == 32 || n == 64 then
      let cw : BitVec n := c64.setWidth n
      cw != 0#n && (armCmpImmIns? (armWidthOf n) .X16 cw).isNone
    else false
  | _, _, .and (.bits _), n, c64
  | _, _, .or (.bits _), n, c64
  | _, _, .xor (.bits _), n, c64 =>
    let w := armWidthOf n
    let cw : BitVec n := c64.setWidth n
    let c64' := cw.setWidth 64
    !armIsValidLogicalImm w c64' &&
      !((n == 8 || n == 16) && armIsValidLogicalImm .W32 (cw.signExtend 64))
  | _, _, .select (.bits _), n, c64 =>
    let cw : BitVec n := c64.setWidth n
    cw != 0#n && cw != 1#n && cw != ~~~0#n
  | _, _, .mul (.bits _), n, c64 =>
    let cw : BitVec n := c64.setWidth n
    cw != 0#n && cw != ~~~0#n && (armPow2Shift? cw).isNone && (armPow2Plus1Shift? cw).isNone
  | _, _, _, _, _ => false

/-- Prefer live GPR over materializing non-zero immediate in `.X17` for stores (`OPT-7c`). -/
def armPreferStoreRegImm (n : Nat) (c64 : BitVec 64) : Bool :=
  c64.setWidth n != 0#n

end LeanQbe.T.Arm64
