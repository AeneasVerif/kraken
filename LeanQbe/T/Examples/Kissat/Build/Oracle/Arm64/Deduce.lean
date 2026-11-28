module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Deduce

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X8)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X2)),
  (XRegOrSp.reg (XReg.X11)), (XRegOrSp.reg (XReg.X14)), (XRegOrSp.reg (XReg.X7)),
  (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X1)),
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X20)),
  (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X6)),
  (XRegOrSp.reg (XReg.X4)), (XRegOrSp.reg (XReg.X12)), (XRegOrSp.reg (XReg.X13)),
  (XRegOrSp.reg (XReg.X28)), (XRegOrSp.reg (XReg.X29))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X27))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.gpr (XRegOrSp.reg (XReg.X22))), (.slot 4 .w64),
  (.slot 3 .w64), (.gpr (XRegOrSp.reg (XReg.X29))), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.slot 7 .w64), (.slot 2 .w64), (.slot 1 .w64), (.slot 0 .w64), (.slot 6 .w64),
  (.slot 5 .w64)]

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

@[expose] def hint_full_analyze_lit : armIsa.Hints := _decH #[
  "X040111213240505160726080911010A1B081B00092B0B1B0B081B05072C0C1C0C3001D00103000000254D",
  "5CC2H4P605Q0000mcYXWuaYWmiewL0YWmmWWWW00mmWXWeebXWW00YWWWeWWWWaWW00l//++//z/llnz//VXXW",
  "WYWmmkYWW00000"]
@[expose] def ext_full_analyze_lit : List (SigEntry × Nat) := []

@[expose] def hint_full_analyze_rsn_m6_hdr : armIsa.Hints := _decH #[
  "b7381A150C06140E0F0F0G33090C060E1A0H0H071I1C16120J6505050E2505000K201800210K140E1A0734",
  "30003430003430003430000504071E343000050E0A0E0G0C0G3C080C0C0A1C0A0C07010805012509053509",
  "050C090G0G0FF402000I0J110C0C060726080900000A050E1008050E0002092C0C0C0C080C06072C0C050E",
  "0C0C050E050E0C14101312210505160726080910000A1B081B04092B0B1B0B081B05072C0C1C0CH001D001",
  "054N34D6BIF0450014IF4DN36B2G14C21184DIFJGVHX4CX66N36B118c4100B4DIFJGVHX4CX66N36BX2IX82",
  "X9J214Bc4200C4DIFJGVHX4CX66N36BX2IX82X9JXC411Cc41057Y71IF4DN36BJGVH07XO0009Y714DIFJGVH",
  "X4CX66N36B159i81009Y714DIFJGVHX4CX66N36B159i81009Y714DIFJGVHX4CX66N36B159i81075N34D6BI",
  "Fa3G05L0016N34D6BIFa3Ga4106L0016N34D6BIFa3GaEC06L0034N34D6Bb3F15451079N34D6Bb3FbF5bJ4b",
  "MIbP1c0609j500601D0010554Dd6CdC3dH1dP605Q002bGC3103013223333443550C2012102222332442550",
  "XWiaYXmeaXWunrgWWWWWZWWXmWWmWWiXWz//WWWkWiWeWYWWWZsWWdkdkdkdiWWWiYuZWkorWYWkWn40eaWeWW",
  "WWaXWYWWWWWWWWWeYWYWWWmmWoaWWemWWWWWWWWYaWWeYWeWWWeeWWWW00XXWWYWmmgYWWWWaYWaWemWYWoXab",
  "XWWWWWWaXWXWWWeeWfYWWaeWWWWWWWWfYYWaXWaWWWaanWYW90aWWWmWWWWeWWWWWWWWXWWWmWWWWWaWWiWWWY",
  "WcWcWWWWWWWXoWaZcZcZcZaWWWaWeXXcWWWWiceW00X///zz//x++/Zx////pv/p/k//x+hytnz//////tz/z+",
  "r/ll/bv//td////////bvv/tz/t///tsj/u/DYYWWaXXWyaWWWWicWiWnWWaXqZekYWWWWWWeYWYXgWmmWwcWW",
  "euWWWWWWWWwccWeYWeWWWefoWdWI0060"]
@[expose] def ext_full_analyze_rsn_m6_hdr : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_full_clear_ana : armIsa.Hints := _decH #[
  "G2415161C0A0C0C0E1C073B0B0E1C0B09400000001464A6854D040001464A6854D1C40101564A6854DKC05",
  "00000ecWaWYL0mYWWXWm00eXWYWme00YWWWW00lZz/x+/lVyYWaXWm00000"]
@[expose] def ext_full_clear_ana : List (SigEntry × Nat) := []

@[expose] def hint_full_otfs_large : armIsa.Hints := _decH #[
  "bL4L1M0N3O3D080A4P0D0D0D073C0C3C0A04075000300A0407160E190Q0Q0R076C003009040B060E2D1C0D",
  "091D0A0D0C0D09150D1C0C071C100A1906040916060409121114020206063303060A00075B0C0207220832",
  "08031D070D0800075306277106360A39020003340E2C4A160S3B0B0A074000310100300031010030003101",
  "00300031010400071E40003101040E0B0K0C030C280C0P0P3A0C3B051B1D180O0C0C0C0C0C3B0B07060C0K",
  "4408060404060K351D0DQ001D0010066S4TAM8LBN5N1O6XH11286S4TQPAM5NMO8LBN148XL11096S4TQPAM5",
  "NMO8LBNTD2469XL212A6S4TQPAM5NMO8LBNTDXC614AXL114A4TY0RAMXVQ6S8LBNQP5NMO1BAyG110A4TQPAM",
  "Y0R5NMO6S8LBNXVQ364BAZI342B4TY0RAMXVQ6S8LBNQP5NMOYJB0BXyG001B4TY0RAMXVQ6S8LBNQP5NMOYJB",
  "0BXyG002AY0RAMXVQ6S4T8LBNQP5NMO0Ay800014T010001CY0RAMXVQ6S4T8LBNQP5NMOYJBZ250CZy8002FY",
  "0RAMXVQ6S4T8LBNQP5NMOZ3DZ25YJBZB0Z9C0Fdy8000FY0RAMXVQ6S4T8LBNQP5NMOZ3DZ25YJBZB0Z9C0Fdy",
  "8006JY0RAMXVQ6S4T8LBNQP5NMOa66ZQ1Z3Da43ZS4Z25YJBZB0Z9C0JZiy80079MO5N4T8LBNY0RQPXVQ6S23",
  "29g3200AY0RAMXVQ6S4T8LBNQPMO5N44320Ay8401BY0RAMXVQ6S4T8LBNQPMO5NbE43320By83029MO5N4T8L",
  "BNY0Rc92QPXVQ1C9a3111CcAC8LBNQPXVQc83cH6Y0Rc92MO5N4T14CXm9100CcAC8LBNQPXVQc83cH6Y0Rc92",
  "MO5N4T14CXm9100CcAC8LBNQPXVQc83cH6Y0Rc92MO5N4T14CXm91067MO5N4T8LBNY0Rc920730015MO5N4T8",
  "LBN05300114T01000254TfGDfC5g0C5N165K10306062078091Z92302022200YYdWWkWWyWbedWkWeWWXvuWW",
  "yyddXvukkWXvbuWWyddWXWWzmWWmXuiWXxWXubWWeWWYmmmWYXeWkkWWWWddWddWdWZt50aWWWeWWmWWaWXWYY",
  "WWXYWWWWWWWWWWXWWWWeWXWWWWWWWWWWWWWWWWWWWWWWWWWWWeWaWmmXWWWWWmXWWWWWeWWWW00YXWaaWWeWWY",
  "WWmXXWWWnWWWWWWWWWWamWeWaWWmWYWWWWYaYWaXWmWWamWWWaWmmeaWYWeeWmWWaaeemWYWWaWXeW00ZWucWW",
  "igWWZWdmWmWWyuWmkkZpmyydcWWyWuWWiZpWWWWinWWWWuaeWvYaumWWWWWWYWXWWaWWdcWmWWZpWZpXpWXo00",
  "X///vz/tt//l//x/+/yy//+y//////////o//l/pm+//x////vtx/tz+l//ol///t++/lt/v/ld+f//ttdc//w",
  "//t/yl/VcYWeeWWmWWaWXWZZWWXZWWWWWWWWWWjWWmWilXWWaWWWWceaWeYXmWWjmWWWeXXWmeWcWmuXsWWeeu",
  "vWWbWWeWZmW00019ABC97D6EF"]
@[expose] def ext_full_otfs_large : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 48),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_unwatch_large", [i64, i32, i32], []), 0)]

@[expose] def hint_full_otfs_bin : armIsa.Hints := _decH #[
  "bI4M110P340000000A5C0A06360A08150E28081D140T0B3B0N05350K0B010B05050505053606060E3D1A05",
  "0D08051E2D1B0D091D0A0D0B0D0915050B0B1D0D071D140A190601091606010911030J0J06061202060A04",
  "0A250D0J072J08021D0A0D08040A22063D0D071D160A19050409150504091400030305051101050A060A2C",
  "0D1D0D03072308011D0A0D08060A21051D0D3D0D5C3C041D0C2C150505091A0D1E260A050E0D0D0D0D0D1D",
  "0D2C0C1C0D5D0DP001D001004BP4R5P8M20C4420084RA16BI0F4BP5P8M2D58YK20194RA16BI0F4BP5P8ML5",
  "1D9YK106A4RXJNXDT8MBP5PX6CXKUX50XEV1DAX0100D4RXJNXDT8MBP5PX6CXKUX50XEVXR1XC4Y7615DXX01",
  "01D4RXJNXDT8MBP5PX6CXKUX50XEVXR1XC4Y7615DXX010364RXJNXDT8MBP5P06X0001A4RBP5P8MXJNX6CXK",
  "UXDTX50XEV0A4001A4RBP5P8MXJNX6CXKUXDTX50XEV0A400294RXJNXDT8MBP5PZ7BX6CXKU09Z000014R010",
  "001B4RXJNXDT8MBP5PZ7BX6CXKUX50Z550BXZ0002E4RBP5P8MXJNZ7BX6CXKUXDTZ55X50ZF4ZDDXEV0En400",
  "0E4RBP5P8MXJNZ7BX6CXKUXDTZ55X50ZF4ZDDXEV0En4006H4RBP5P8MXJNZ7BX6CXKUa56ZS1XDTa32Z55ZT3",
  "X50ZF4ZDD0HcX400664RXJNXDT8MBP5P06X000014R01000184RXJNXDT8MBP5PX6CZ7B08b0002B4RXJNXDT8",
  "MBP5PZ7BX6Cb86b6DXKU0BZ0000B4RXJNXDT8MBP5PZ7BX6Cb86b6DXKU0BZ0006E4RXJNXDT8MBP5PbU5bL4b",
  "S1Z7BbM0X6Cb86b6D0Ev000654RXJNXDT8MBP1D501137dD4dFD4RXJNXDT8MBP157010074RXJNXDT8MBPdS5",
  "dFD07000D040B80A1XK23325234GXJ431830H042812H0O432231824222281F432231824222281322I3XQ43",
  "2231824222281X822G40YrenmWWZWYXieyyfXaWecWWYWiWeZWXWWWeWWYmoWXmWWmZWWiWaWWXWWWgYWmWYXe",
  "WWbmZmWkdYmWWZmkWd50meeWWWWWWWWWWWWWWWWWWWWWWWWWWWWeWWWWWWWWWWWWWWWWWWWXWWaWmmWmWWWWWW",
  "WWWWaamYWWW00eaamXWWWWWWWWWemeXWmWWamWWaWmmeaWWWYaYWeaWWoWWWmYYXWmWYWeeWeeeXWWWWWWbYYe",
  "XWaW00qWmXWWaaWieWWWWWYaWWWaeWXYaYWWWWWWYWWWnWWWXYWaemeWWWWWWeWXWWaWWWWmfneYXWWWWXucXn",
  "00l/////+lltsXj/////////c/lz+l//ol//t++/lt///vtx/lp/+f//+/xxz+//v/ld/ldlz//v///rvxlz/t",
  "/VXmmef+oWWWWWWWWWvWmYXmWWjmWWeXXWmeWWWceaWmiWXsWWXWaaYXWWcWmuWmumYWWcWWWgcamYWeW00055",
  "ABC97"]
@[expose] def ext_full_otfs_bin : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 48),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_unwatch_large", [i64, i32, i32], []), 0)]

@[expose] def hint_full_otfs_subsume : armIsa.Hints := _decH #[
  "X15A081B241A0010003505001A150A05351A051C0A0C1C0C150A053D1A05040E0D04500000003000000144",
  "DCB5C8604400314D0100014CB5CF4860460000hmXWmYXkWamymsG0XXWWeWWmaWXWWWWW00mmWaWWeYWWnWWX",
  "W50XmWWWWWcWWYiWY00Z/+c//t//lx/+z//z/LXvWWeWWmaWXYWWYWA0000"]
@[expose] def ext_full_otfs_subsume : List (SigEntry × Nat) := []

@[expose] def hint_full_deduce_1uip_m6_hdr : armIsa.Hints := _decH #[
  "pV7D081D0B1C0K0D081A1B0D050E0M0M023P090P050E1A0J0J07131C1D10016B0B0B0E2B0B060K26180624",
  "0K150E1A073536063536063536063536060B05071E3536060B0E0A0E020T0T3D080D0D0A1D0A0D070N080C",
  "0N2C090C3C090C0D090T0T02A500060301140D0D0B072B080906060A0C0E16080C0E0600092D0D0D0D080D",
  "0B072D0D0C0E0D0D0C0E0C0E0D1B141011250C0C16072608090A14080B04092C0C0C0C080C0B072D0D0D0D",
  "2C14151011260D0D1B072B08090A15080504092D0D0D0D080D0B072D0D0D0D2C14151011260D0D1B072B08",
  "0905050A15080504092D0D0D0D080D0B072D0D0D0D1D0C081X01I1G1Q1B1X12H1D65680L2N0T0D0K150A25",
  "080C081M0S081A050M0D0C0E0O0O0B3P090P0D0E1A0F0F070J050403025606060E26060C0K201800210K1D",
  "0E1A073D30003D30003D30003D3000060D071E3D3C0C060E0A0E0B0D0B2D080D0A0D0A0D0701080C012C09",
  "0C3C090C0D090B0B0B44010002031C0D0D060726080900000A050E1008050E0001092D0D0D0D080D0C072D",
  "0D050E0D0D050E050E05060401001B0D0D0C072C08090A14080604092D0D0D0D080D0C072D0D0D0D0P050A",
  "051B0709180O0T081M080D0E0A080D2C1A0B1B0B35050B1A1C0A0C2C1A0C1D0A0D1D0D1B0A0B2B1A050C0E",
  "0B0C0D060B050A0D0D0E1D073C0C0E1D0C091D3C1A1C0A0C1C0A0C080C0E0A082C1A0B1B0B3D0D0B1A1D0A",
  "0D1D0A0D0D060B050A0D0D0E1D073C0C0E1D0C09060B050D0A0D0D0E1D073C0C0E1D0C090N2A060B050D0A",
  "0D0D0E1D073C0C0E1D0C09060B050D0A0D0D0E1D073C0C0E1D0C09180D061B050A0D0D0E1D073C0C0E1D0C",
  "09061B050D0A0D0D0E1D073C0C0E1D0C09161B150D0A0D080D0D0D0E1D073C0C0E1D0C090D080DY9001D00",
  "10014R141010734RX2PTM0320013TM4RX2P2TN3421174RTMU2XAJXFCXHDX2P147Y4100A4RTMU2XAJXFCXHD",
  "XD3XJ0XK1X2P245Am4200B4RTMU2XAJXFCXHDXD3XJ0XK1X2PXN514Bm41056YI4TM4RX2PU2XAJ06O0008YI4",
  "4RTMU2XAJXFCXHDX2P1B8a81008YI44RTMU2XAJXFCXHDX2P1B8a81008YI44RTMU2XAJXFCXHDX2P1B8a8107",
  "44RX2PTMaET04A00154RX2PTMaETaFN05A00154RX2PTMaETaPD05A00334RX2PbE21C3210784RX2PbE2bLCb",
  "P5bS3bV4c6B08cI00B54RdCDdI0dN5dV605Q00314R01000554ReRCf10f66fEB05Q00854RgACgG0gL6gTB05",
  "Q00324RhP402000224Ri6X21N20100D4Ri6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QhQX6iKX73CDBDXG30",
  "2EiSL4Ri6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QhQX6iKX72CBEZ0203H4RhQX6jESjDMiSLi6X2iKX7i2",
  "Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVN0HYXm800014R010005K4RjTPj0TjDMjESiSLi6X2i2Gi2X3iBHiBX",
  "4i0Ii0X5hUX0i8X1i4QiVNhQX6iKX7jOO0KYXmE001K4RjTPj0TjOOiKX7jDMjESiSLi6X2i2Gi2X3iBHiBX4i",
  "0Ii0X5hUX0i8X1i4QiVNhQX62B1KecX6211O4RiKX7jOOjPBk5Fk85k94jTPj0TjDMjESiSLi6X2i2Gi2X3iBH",
  "iBX4i0Ii0X5hUX0i8X1i4QiVNhQX611OaZWy8100R4RiKX7jOOjPBk5Fk85k94jTPj0TjDMjESiSLi6X2i2Gi2",
  "X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6k7JkA3kB221DRaZWy8200S4RiKX7jOOjPBk5Fk85k94jTPj0TjDM",
  "jESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6k7JkA3kB2kDD11SaZWy8105Nl814RjTPj0TjO",
  "OiKX7jDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6jPBk5F0NYmiYC000Pl814RiKX7jOO",
  "jPBk5Fk85k94jTPj0TjDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX616PecXuG100Pl814",
  "RiKX7jOOjPBk5Fk85k94jTPj0TjDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX616PecXuG",
  "100Pl814RiKX7jOOjPBk5Fk85k94jTPj0TjDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6",
  "16PecXuG107L4RjTPj0TjDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6iKX7jOOn4B0LXY",
  "XmE001M4RjTPj0TjDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6iKX7jOOn4Bn510MXYXm",
  "E001M4RjTPj0TjDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6iKX7jOOn4BnCD0MXYXmE0",
  "03K4RjTPj0To1BjDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6iKX715KaZWM107P4RjTP",
  "j0To1BjDMjESiSLi6X2i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNhQX6iKX7o25o64o92oCCoJ60PwaZWM00",
  "BL4RhQX6jESjDMiSLi6X2iKX7i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVNpP5pS1pVBq6C0LXsXm8003I4Rh",
  "QX6jESjDMr0PiSLi6X2iKX7i2Gi2X3iBHiBX4i0Ii0X5hUX0i8X1i4QiVN15IaZW810614R01000634RrKDrEM",
  "03400214R01000144RrKDrEMrNC04C0034t66t85t7B4R1D401014t66t85t7B4R0400025t66t85t7B4RtGD0",
  "5000364RtRDrBTrAOhQX6jES06000314R0100084v96vB5vAB4R1D401014v96vB5vAB4R0400025v96vB5vAB",
  "4RvJD0500024vT6vV5vUB4R1D401014vT6vV5vUB4R0400025vT6vV5vUB4Rw8D0500034wM6wO5wNB4R1D401",
  "014wM6wO5wNB4R0400025wM6wO5wNB4Rx1D0500024xB6xD5xCB4R1D401014xB6xD5xCB4R0400025xB6xD5x",
  "CB4RxMD0500034y36y65y5B4R1D401014y36y65y5B4R0400025y36y65y5B4RyED0500024yO6yR5yQB4R1D4",
  "01014yO6yR5yQB4R0400025yO6yR5yQB4Rz4D05000224RhP40200005zF6zJ5zHB4RhP41D501025zF6zJ5zH",
  "B4RhP40500026zF6zJ5zHB4RhP4zVD06000E020A1nD23617230J123248231KB435G372c02215343323450A",
  "2422K12J0223254cT62422K12J072286ZV62422K12J0S2226cJ22170XWuXWWWgmWecWaWWmWecWaWXWWWmiW",
  "eWWWXWuWmWWWWXWuWmWWWYXmXWWWWXWamymsWWWaWoyWWecWaWWWWWbmYYWebmYekehWWWWWmWWWWWuWWiWYWZ",
  "WeWWWWWWuWWiWWaWWZWedWWWdWcWWWWWWWkuWWzuzuzuzmWWXmhWiXuWWeXuWYXWZXWuk/rrgqWWWcWWZWWmWc",
  "ajgsWWcWWZWWmWunrguWWiWWcWXWXnZgqWWWWWcWWZWWXWWWuYXx+WWWyWuWmWaWWWdiWWkykykykuWWWubmcW",
  "zbgWaWyWfWangL0XYWeXWeWmWWmYWaXWWWmYWaXWWWXWaWeYWWYWeWmaWWeYWeWmaWWaWmXWWWWWWWWWWWWWYW",
  "WWWWWmYWaWWWWWWWWWWWWWWWWWWWWWmWYamaWWWWWWXWmmWWWWYXWYWWWWXWeWmWWWWWWaXWXWWWnWYemWXYWW",
  "WWWWWWWemWXWeXWWXXWWWWWWWmeWWWWWWWWeWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWmeWmW",
  "WWWeYWaWWWWWWWWmaWaWWXXWWaeWWnWWWWWWWWWaeWWmaWmWWWmmWWWWXWWW00XWaWmaWYWWeXWYWmeWeXWYWm",
  "eWmmYWaXWmXWaWeYXWaXWaWeYXWYWeWmaYWWaWnWWXWqnWmYWWWeXWYWmeWWeeWeWXWeWemWWmbaeXXYeYWWWY",
  "aWWmefeeWWXWmXWYaWWmamfXeeWWWYWmWmWWemXaeWWnWWWWWWWWXaeeWmaWmWWmoaWeameeaeXWWWWWXWWWWn",
  "WWaYYYmmWWWWWWnWWaYYgYWWWWWWXYWWeaaqaWWWWeaWeWnWWaXaYegYWWWWWeYWYWWWmmWoaWWemWWWWWWWWo",
  "aaWeYWeWWWefYWaYemaW00eWWWWWWWWYWWWWWWWYWWWWWWWWaWWWWWWWeWWWWWWWWeWWWWWWWmWWWWWWWWYiWY",
  "WWWWWWiWWWYWWWWWWWWmWWWWWmWXcWXWWWWWWWWWWWeWWaWWWXWWWWWWWWeWWaWWWWWXWWZWXWZWZWWWWWWWce",
  "WmiuiuiuimWWWmXWaauWWXmvWWWWWWWeWWWWWWWWWYWWXWWWWYWWWWWWYWWXWWWWeWWWWWWaWWYWWWWmWWWWWW",
  "WWYWWXWWWWWWeWWuWWaWiWiWWWWWWWZaWeciciciceWWWeWmYYiWWWWuimWWWWW00Zlylt+/ttx//Zz/x+/l/Z",
  "z/x+/l++dx/tz+/ylt/lxz/tylt/lxz/u/l+/tx//t+z//z+sz+/xt//Zz/x+/l//Zl/l/z/l/k//+/rtlzzvl",
  "x///xt/+/lill//y+ly/xt/+/o/byll///x+/+/g/k/ytd/+y////////ytdd+/t+//++vt/Zs/Zltlz/////z",
  "///+z//txxu+//////+z//txxZx//////zx//ltsdt////dp/d+z//tytvlZx/////lx/xzh++/+hp//kl////",
  "///+hpp/lx/l///lix/pxkdt/VmZmeXWeeaWWyYWaXWmWyYWaXWmXXuaWeYXWZmeWmaYWeZmeWmaYWdWmXWeaW",
  "WeXYWWYXfYXWaeWWyYWaXWmWWymWmWYWmWnWWXWgemYYcmaWWWaeWXWmpmmWWZXmZWaeWXWjWwZmmWWWaXWXWr",
  "WnWZeuWXZWWWWWWWWZeuuXWeXWWXXceWyfWymemYWWWWWYWWWXYWWeaadXWWWWWWXYWWeaayaWWWWWWYaWWmef",
  "ueWWWWuiWuXYWWeZecmyaWWWWWmaWaYqXXWXqiWWnmWWWWWWWXqiiWmaWmWWWmpaWianueW0008BABC97D6EFL", "M"]
@[expose] def ext_full_deduce_1uip_m6_hdr : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("full_otfs_large", [i64, i32, i32], [.bool]), 240),
   (("full_otfs_bin", [i64, i32, i32], [.bool]), 240)]

@[expose] def hints : List armIsa.Hints := [hint_full_analyze_lit, hint_full_analyze_rsn_m6_hdr,
    hint_full_clear_ana, hint_full_otfs_large, hint_full_otfs_bin, hint_full_otfs_subsume,
    hint_full_deduce_1uip_m6_hdr]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_unwatch_large", [i64, i32, i32], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Deduce
