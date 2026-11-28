module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reorder

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X27)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X25)),
  (XRegOrSp.reg (XReg.X26)), (XRegOrSp.reg (XReg.X29)), (XRegOrSp.reg (XReg.X4)),
  (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X1)),
  (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X28))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.gpr (XRegOrSp.reg (XReg.X14))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X29))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.flag LeanQbe.T.Arm64.ArmCond.gt), (.slot 8 .w64), (.slot 7 .w64), (.slot 10 .w64),
  (.slot 9 .w64), (.slot 6 .w64), (.gpr (XRegOrSp.reg (XReg.X27))), (.slot 5 .w64),
  (.slot 2 .w64), (.slot 1 .w64), (.slot 3 .w64), (.slot 4 .w64), (.slot 0 .w64)]

@[expose] def _d64 (c : Char) : Nat :=
  let n := c.toNat
  if n >= 97 then n - 61
  else if n >= 65 then n - 55
  else if n >= 48 then n - 48
  else if n == 43 then 62 else 63

@[expose] def _rNatAux (acc : Nat) : List Char → Nat × List Char
  | [] => (acc, [])
  | c :: cs =>
    let v := _d64 c; let acc' := acc * 32 + v % 32
    if v >= 32 then _rNatAux acc' cs else (acc', cs)

@[expose] def _rNat (cs : List Char) : Nat × List Char := _rNatAux 0 cs

@[expose] def _rList {α : Type} (f : List Char → α × List Char) :
    Nat → List Char → List α × List Char
  | 0, cs => ([], cs)
  | n + 1, cs =>
    let (x, cs1) := f cs; let (xs, cs2) := _rList f n cs1; (x :: xs, cs2)

@[expose] def _rDeltas {α : Type} (f : List Char → α × List Char) :
    Nat → Bool → Nat → List Char → List (Nat × α) × List Char
  | 0, _, _, cs => ([], cs)
  | n + 1, isF, prev, cs =>
    let (d, cs1) := _rNat cs
    let k := if isF then d else prev + 1 + d
    let (v, cs2) := f cs1
    let (rest, cs3) := _rDeltas f n false k cs2
    ((k, v) :: rest, cs3)

@[expose] def _rTrie {α : Type} (f : List Char → α × List Char)
    (cs : List Char) : Trie α × List Char :=
  let (n, cs1) := _rNat cs
  let (ps, cs2) := _rDeltas f n true 0 cs1
  (ps.foldl (fun t (k, v) => t.insert k v) .empty, cs2)

@[expose] def _rTrieOpt {α : Type} (f : List Char → Option α × List Char)
    (cs : List Char) : Trie α × List Char :=
  let (n, cs1) := _rNat cs
  let (ps, cs2) := _rDeltas f n true 0 cs1
  (ps.foldl (fun t (k, vo) => match vo with | some v => t.insert k v | none => t) .empty,
    cs2)

@[expose] def _mkBTGo (i t f : Nat) (acc : Trie Bool) : Trie Bool :=
  if h : t = 0 ∧ f = 0 then acc
  else
    let acc' := if t % 2 == 1 then acc.insert i true
      else if f % 2 == 1 then acc.insert i false else acc
    _mkBTGo (i + 1) (t / 2) (f / 2) acc'
termination_by t + f

@[expose] def _rBTrie (cs : List Char) : Trie Bool × List Char :=
  let (tm, cs1) := _rNat cs; let (fm, cs2) := _rNat cs1
  (_mkBTGo 0 tm fm .empty, cs2)

@[expose] def _rBoolsAux : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, m => (m % 2 == 1) :: _rBoolsAux n (m / 2)

@[expose] def _rBools (cs : List Char) : List Bool × List Char :=
  let (n, cs1) := _rNat cs; let (m, cs2) := _rNat cs1
  (_rBoolsAux n m, cs2)

@[expose] def _sw : Nat → SlotWidth
  | 0 => .w64 | 1 => .w128 | 2 => .w256 | _ => .w512

@[expose] def _rSymArg (cs : List Char) : SymArg × List Char :=
  let (t, cs1) := _rNat cs
  match t with
  | 0 => (.immBool false, cs1)
  | 1 => (.immBool true, cs1)
  | 2 => let (w, c2) := _rNat cs1; let (c, c3) := _rNat c2
    (.immBits w (BitVec.ofNat 64 c), c3)
  | 3 => let (w, c2) := _rNat cs1; let (c, c3) := _rNat c2
    (.immVec (_sw w) (BitVec.ofNat 512 c), c3)
  | k + 4 => (.var k, cs1)

@[expose] def _rLoc (cs : List Char) : Option (Loc armIsa.Reg armIsa.VReg
    armIsa.Cond) × List Char :=
  let (i, cs1) := _rNat cs; (_locs[i]?, cs1)

@[expose] def _rMove (cs : List Char) : Option (Move armIsa.Reg armIsa.VReg
    armIsa.Cond) × List Char :=
  let (t, cs1) := _rNat cs
  match t with
  | 0 => let (d, c2) := _rNat cs1; let (s, c3) := _rNat c2
    ((_regs[d]?.bind fun dr => _regs[s]?.map (.mov dr ·)), c3)
  | 1 => let (d, c2) := _rNat cs1; let (c, c3) := _rNat c2
    (_regs[d]?.map (.movi · (BitVec.ofNat 64 c)), c3)
  | 2 => let (d, c2) := _rNat cs1; let (i, c3) := _rNat c2
    (_regs[d]?.map (.ld · i), c3)
  | 3 => let (i, c2) := _rNat cs1; let (s, c3) := _rNat c2
    (_regs[s]?.map (.st i ·), c3)
  | 4 => let (d, c2) := _rNat cs1; let (c, c3) := _rNat c2
    ((_regs[d]?.bind fun dr => _conds[c]?.map (.setcc dr ·)), c3)
  | 5 => let (w, c2) := _rNat cs1; let (d, c3) := _rNat c2; let (s, c4) := _rNat c3
    ((_vregs[d]?.bind fun dv => _vregs[s]?.map (.vmov (_sw w) dv ·)), c4)
  | 6 => let (w, c2) := _rNat cs1; let (d, c3) := _rNat c2; let (c, c4) := _rNat c3
    (_vregs[d]?.map (.vmovi (_sw w) · (BitVec.ofNat 512 c)), c4)
  | 7 => let (w, c2) := _rNat cs1; let (d, c3) := _rNat c2; let (i, c4) := _rNat c3
    (_vregs[d]?.map (.vld (_sw w) · i), c4)
  | _ => let (w, c2) := _rNat cs1; let (i, c3) := _rNat c2; let (s, c4) := _rNat c3
    (_vregs[s]?.map (.vst (_sw w) i ·), c4)

@[expose] def _rEntry (cs : List Char) : Entry armIsa.Reg armIsa.VReg
    armIsa.Cond × List Char :=
  let (nl, c1) := _rNat cs
  let (lv, c2) := _rList (fun s => let (sa, s1) := _rSymArg s
    let (lo, s2) := _rLoc s1; (lo.map (sa, ·), s2)) nl c1
  let (np, c3) := _rNat c2
  let (pl, c4) := _rList _rLoc np c3
  let (lz, c5) := _rBools c4; let (pz, c6) := _rBools c5
  ({ live := lv.filterMap id, ploc := pl.filterMap id, liveZ := lz, plocZ := pz }, c6)

@[expose] def _rPre (cs : List Char) : PreStep armIsa.Reg armIsa.VReg
    armIsa.Cond × List Char :=
  let (pk, c1) := _rNat cs
  let (ms, c2) := _rList _rMove (pk / 2) c1
  ({ clearFlags := pk % 2 == 1, moves := ms.filterMap id }, c2)

@[expose] def _rVar (cs : List Char) : VariantHint × List Char :=
  let (t, c1) := _rNat cs
  match t with
  | 0 => (.default, c1) | 1 => (.adcx, c1) | 2 => (.adox, c1)
  | 3 => (.mulxFast, c1) | 4 => (.decInc, c1)
  | _ => let (o, c2) := _rNat c1; (.disp (Int64.ofBitVec (BitVec.ofNat 64 o)), c2)

@[expose] def _decH (chunks : Array String) : armIsa.Hints :=
  let cs := (chunks.foldl (· ++ ·) "").toList
  let (dt, c1) := _rTrieOpt _rLoc cs
  let (et, c2) := _rTrie _rEntry c1
  let (pt, c3) := _rTrie _rPre c2
  let (vt, c4) := _rTrie _rVar c3
  let (el, c5) := _rBTrie c4; let (ij, c6) := _rBTrie c5
  let (dj, c7) := _rBTrie c6; let (dl, c8) := _rBTrie c7
  let (df, c9) := _rBTrie c8; let (mh, c10) := _rBTrie c9
  let (ns, c11) := _rNat c10; let (sn, c12) := _rNat c11
  let (sv, _) := _rList (fun s => let (i, s1) := _rNat s; (_regs[i]?, s1)) sn c12
  { dest := dt, entry := et, pre := pt, variant := vt, elide := el, invertJnz := ij
    deferJnz := dj, deferLea := dl, deadFlags := df, mulHiIps := mh
    nslots := ns, saved := sv.filterMap id }

@[expose] def hint_full_reorder_sift_fid : armIsa.Hints := _decH #[
  "XH300112031415160708095A322B2C3D2E0F0G0H0I0J000G0K0I0B0F0G0C0D0E0203283B270F0E07000E0C",
  "0F020C2027080940000000300000004H6F5D46L378M403016H6F5D46LQANM22C6G2200iWWczmWWWjxjxWbe",
  "G0aWWWWWWWWWW00aWmWWWYWWWWWWWYWY50aWWYemWWWananWWW00Z/p+ua//xWXX////v/uHiXdxWWa/++WWWW",
  "cWdE000201"]
@[expose] def ext_full_reorder_sift_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_reorder_queue_m7 : armIsa.Hints := _decH #[
  "kD2N0O1A1M1P1L1Q121C1K1R1S1T1I1U0V010F0A0M090A090A010A011L0M3L320L0113130A0F0D0D0M3S0S",
  "100A090C0V2A0A031A0X0000L11420203120X0000A0L1M0311010L0A0A0D0V3L0L030R103A4A1Q030A0L0M",
  "0A020F2C3A0A0A0F1V0M13220V0A030M0M0M0M0M1M010V1L2A1V1A000A0A0A0Q0Q3T0T0V030A090T0A333R",
  "100A0A0F030M321V1A00000A1A202A3A1Q030A030Q030S030V3O1A015Q031A0V0V4L1V2L0A1M03110Q0V1Q",
  "090M030405060708095L322B2C3D2E0F0G0H0I0J000G0U0I0B0F0G0C0D0E0203283B270F0E07000E0C0F02",
  "0C202708090V1H0L22000M030405060F5L322B2C3D2E0F0G0I0U0J000Q0I0U0B0F080C0D0E02032G3B270F",
  "0E07000E0C0F020C20270809010V010F0M0L0902090M090C010C0M010M0M010M011L0M3M3L320L0113000V",
  "5L0L2V322203222M02020202000C0D032M0M4M0M290C0CD21U0V4L1V2L0M1A03110G0V1G070B095M3D1822",
  "3C140F00030A0E0506000A0E0D060F0B020D044E032C38170F00030A0D000A0D0F020C20270B090V150M2L",
  "0F5M3D18223C140F00030A0E060G000A0E0D0G0F0B020D044E032C38170F00030A0D000A0D0F020C20270B",
  "09013V1O2Q0Q2A1M1L010A0D042M0M0201032L0V180V12023L0L0C012C095V4V32XV001N00100KX1UVI6N7",
  "ODPHQHX19X2BX3JX4FX54X6LX7NKRSRX8PRPX9TTTXA12K0100KX1UVI6N7ODPHQHX19X2BX3JX4FX54X6LX7N",
  "KRSRX8PRPX9TTTXA12K0109EBX3JX4DPFX56N7OVIX1ULX74X6NKRX8PX9TXA0E0000HBX3JX4DPFX56N7OVIX",
  "1ULX74X6NKRX8PX9TXAHQHX19X21TH0102IBX3JX4DPFX56N7OVIX1ULX74X6NKRX8PX9TXAHQHX19X2XTT0I0",
  "002LVIX1U7O4X6XTTY8SDPHQHX19X2BX3JX4FX56NLX7NKRX8PX9TXAY7SY2D1LLmWW0100MBX3JX4DPFX56N7",
  "OVIX1ULX74X6NKRX8PX9TXAHQHX19X2XTTYDCY7SY2DY8S2LMMmWW0201MBX3JX4DPFX56N7OVIX1ULX74X6NK",
  "RX8PX9TXAHQHX19X2XTTYDCY7SY2DY8S1LMYmWW0103NBX3JX4DPFX56N7OVIX1ULX74X6NKRX8PX9TXAHQHX1",
  "9X2XTTYDCY7SY2DY8SYSM1LNmWW0104LVIZGXBX1U7OZHDZHXC4X6XTTY8SDPHX19X2BX3JX4FX56NLX7NKRX8",
  "PX9TXA1QL0101MVIZGXBX1U7OZHDZHXC4X6XTTY8SDPHX19X2BX3JX4FX56NLX7NKRX8PX9TXAZJQ0M0003IBX",
  "3JX4DPFX56N7OVIX1ULX74X6NKRX8PX9TXAHQHX19X2XTT1MI0113Ka9LaAM7ODPHQHX19X2XTTBX3JX4FX56N",
  "4X6VIX1ULX7NKRX8PX9TXA1AK0100KBX3JX4DPFX56N7OVIX1ULX74X6NKRX8PX9TXAHQHX19X2XTTaRAaAM0K",
  "0003DX1UVI6N4X6NKFX5RSRX8PRPX9TTTXADP0D0000EBX3JX4DPFX56N7OVIX1ULX74X6NKRX8PX9TXA1SE01",
  "01FBX3JX4DPFX56N7OVIX1ULX74X6NKRX8PX9TXAbCS0F0005JBX3JX4DPFX56N7ObCSc4TVIbDLbDXBX1Uc5X",
  "2LX74X6NKRX8PX9TXA1QJ0102KBX3JX4DPFX56N7ObCSc4TVIbDLbDXBX1Uc5X2LX74X6NKRX8PX9TXAcAQ0K0",
  "004NBX3JX4DPFX56N7ObCSc4TVIbDLbDXBX1Uc5X2LX74X6NKRX8PX9TXAcAQcKMcKXCcDR0NaWWW0006CNKFX",
  "56NVI4X6RSRX8PRPX9TTTXADP0C0000DX1UVI6N4X6NKFX5RSRX8PRPX9TTTXADP1QD0101EX1UVI6N4X6NKFX",
  "5RSRX8PRPX9TTTXADPdMQ1AE0103A4X6NK6NRSRX8PRPX9TTTXADP1AA0100CNKF2FX56N4X6RSRX8PRPX9TTT",
  "XADP2AMC0201DNKF2FX56N4X6RSRX8PRPX9TTTXADPe9M1AD0102BTTTXARSRX8PRPX94X6eMA6NNKDP0B0001",
  "BeMA4X6NK6NRSRX8PRPX9TTTXADP0B0000BeMA4X6NK6NRSRX8PRPX9TTTXADP1QB0101CeRQeMA4X6NK6NRSR",
  "X8PRPX9TTTXADP0C0002FeRQeMA4X6NK6NRSRX8PRPX9TTTXADPf16f05eV4378MF0301HeRQeMA4X6NK6NRSR",
  "X8PRPX9TTTXADPf16f05eV4fALf7M22CHXWW0224B4X6NK6NRSRX8PRPX9TTTXAeMADP1MB0100ChAH4X6NK6N",
  "RSRX8PRPX9TTTXAeMADP0C0002FhAH4X6NK6NRSRX8PRPX9TTTXAeMADPhK6hJ5hI4378MF0301HhAH4X6NK6N",
  "RSRX8PRPX9TTTXAeMADPhK6hJ5hI4hRLhOM22CHXWW0224BTTTXARSRX8PRPX94X6eMA6NNKDP12B0100BTTTX",
  "ARSRX8PRPX94X6eMA6NNKDP12B010D4eMANK6N4X62CD40200BNKeMA6N4X6DPTTTXARSRX8PRPX93CDMB0301",
  "FNKeMA6N4X6l4Dl9Ll3CDPTTTXAl5MRSRX8PRPX912FX0101FNKeMAPRPX96N4X6l4Dl9Ll3CDPTTTXAl5MRSR",
  "X812Fa01022eMA4X62CD202014n1UVINK4X61N401007NKF2FX56Nn1UVI4X62MA702018NKF2FX56Nn1UVI4X",
  "6n4A1M801025nHN4X6n1UVINK0500015nHNNKn1UVI4X60500005nHNn1UVINK4X61G501016nMGnHNn1UVINK",
  "4X60600006nMGnHNn1UVINK4X637BL603019nMGnHNn1UVINK4X6nVMnSLnQ74B2D49Y04228nMGnHNn1UVINK",
  "4X6nVMnSL22C8Y02265NKnHNn1UVI4X61A501006q45NKnHNn1UVI4X60600006q45NKnHNn1UVI4X637BL603",
  "019q45NKnHNn1UVI4X6qFMqCLqA74B2D49Y04228q45NKnHNn1UVI4X6qFMqCL22C8Y022654X6n1UVINKnHN1",
  "A501016sOO4X6n1UVINKnHN060004AsOO4X6n1UVINKnHNt6DsSQsRQt5A1MAe0110CsOO4X6n1UVINKnHNt6D",
  "sSQsRQt5AtK8t741MCe011X402023C23847231512326123374A35839936A3AB373XJ2237322B7D22B7XN23",
  "0C0234302248I22C0622C032248XL62622512732234A12236B22B9A223AC237342235C230B222969223732",
  "2A4022B0222A4022B0722B0022A4422B0022A4H6262251273C2303020B30hWWkWjuudWaiWuWhcXuWXmWWWh",
  "sWWWWWhstiWuWWcWWWXkuWWWWXkwzmWWWWusXXhbgomYpqWWYcYdZcWWXgberWWWWWWWWWWWZWWXtiWWWZkxku",
  "WWcWWWiWWczmWWWjxjxWWWWWWcbmYWWXiWWWWWuimWWnkWWsZmWWyWahWWWWWiWediWWXukeZWWWWWmiWXWuWY",
  "kWWWYqgmWWWWWbgrgr90aWWYWWWWWWWWWWWWWXWWWWWeWWmWWWeWWWWWWaWWWWXWWYWWWXWWWWWWXYWYWWWWWW",
  "WWmWWaWWWmWeWWmWWWWWWWWWYaefaeWWWWWWXWWWWWWWWWWWXWWWWWWWaWWWWWWWWWWWemWmWWeWWWXXYYWWWW",
  "WaaWfWWWXYeWXXWWWWWYXWWWWWaWWWXWWWnWWaWmWeYaeWWfWWWWWXXYYfWWWWW00YWWXWYYWWnXeWeWWYWmmY",
  "WWbWWeWWWbWWWWeWYYWeWWqWXWWWWqWWWXWenWXWaWWWWWWeWWYWWWeWaWbemWWWWWfXXXYaaoaXWaWWWWmWWW",
  "WWWWmoWWmaWmWWWYWWWWWWWYWoYaeWeXeaWaWemnXWWXWWoYWanWaWnaWWmmXXWWXWmoWXWYWWWmmYWemYYWea",
  "aXYaWYanWWWWamnXamWWWW00cWaueZeWaWeWWYWWWWmWWWWoWWWWWWoXaWeWWYWWWWYeWWWWWYeamWWWWeYWWW",
  "WWWWWXmWXWYWZWYWWeWWWWWWWWWWWWWWWXWWWoaWWWXafaeWWYWWWaWWYemWWWananWWWWWWYWmWWWWWWWWmWe",
  "aWWWWbWWYWWeWieWXWWWYWaWWpaWWWucWfWeWWmWaWWWeXWceWWmWWWWWWWWWWWWW00d/x//z/xx/+zyl/l//x",
  "++lxmfn//lWXXn////l/xv/kXcd/zyWacd///y/ky/z/t//////l//wl//d/t/rkl/////k++avpohty/sXd/+",
  "uWel///++Z/+/p+ua//xWXX////v+Zxtd/lzlp/t/kkay//z/+xx/oz/t+jt/++/zz/vz++udi/v//++/xvkkZ",
  "x/kdtzvt/usy////tYiyo/////VaWWYWaaWXYZmWmWWaXXmalskWWm/++kWWWWmWacWn+vuWYZ/xvuWWWZWnZW",
  "YWeWWWWWWmWWbmWWuWeWgnmWWWWWnXXxcijqeZWf+uWXd/tmWWWXXyWXWiXdxWWa/++WWWWcXyaeuWmYmiWeWn",
  "nxZWWYWXaaWjYWeXoeWXXWYYWcYXXdupWcWWXXWacnnyaWnueYceWdfZWWWWezpZjWWWWW000BB01DE4F562G7"]
@[expose] def ext_full_reorder_queue_m7 : List (SigEntry × Nat) :=
  [(("f64u_add", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("full_rescale_m6", [i64], []), 64)]

@[expose] def hint_full_reorder_m6 : armIsa.Hints := _decH #["23M0V1001A00100010004000dN80000"]
@[expose] def ext_full_reorder_m6 : List (SigEntry × Nat) :=
  [(("full_reorder_queue_m7", [i64], [i64]), 256)]

@[expose] def hints : List armIsa.Hints := [hint_full_reorder_sift_fid,
    hint_full_reorder_queue_m7, hint_full_reorder_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_add", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("full_rescale_m6", [i64], []), 64)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reorder
