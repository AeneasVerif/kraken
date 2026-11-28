module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Eliminate

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X14)), (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X23)),
  (XRegOrSp.reg (XReg.X26)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X25)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X0)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28)),
  (XRegOrSp.reg (XReg.X29)), (XRegOrSp.reg (XReg.X7)), (XRegOrSp.reg (XReg.X8)),
  (XRegOrSp.reg (XReg.X6)), (XRegOrSp.reg (XReg.X10)), (XRegOrSp.reg (XReg.X9)),
  (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X4))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.flag LeanQbe.T.Arm64.ArmCond.gt), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.flag LeanQbe.T.Arm64.ArmCond.lt),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.gpr (XRegOrSp.reg (XReg.X26))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.gpr (XRegOrSp.reg (XReg.X29))), (.flag LeanQbe.T.Arm64.ArmCond.cc), (.slot 0 .w64),
  (.slot 13 .w64), (.slot 15 .w64), (.slot 14 .w64), (.slot 3 .w64), (.slot 17 .w64),
  (.slot 18 .w64), (.slot 11 .w64), (.slot 1 .w64), (.slot 8 .w64), (.slot 7 .w64),
  (.slot 10 .w64), (.slot 12 .w64), (.slot 5 .w64), (.slot 16 .w64), (.slot 9 .w64),
  (.slot 6 .w64), (.slot 2 .w64), (.slot 4 .w64), (.gpr (XRegOrSp.reg (XReg.X15)))]

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

@[expose] def hint_full_bve_collect_m7 : armIsa.Hints := _decH #[
  "X250111213040505050505360606074008190A20053819380B0A340705250C0A3407274001400100014001",
  "006R66D7EF3D2B1254642006R66D7EF3D2B1254642000XucWWyZoyufmZmYL0XWmWWWeWWWWWWWWWW00meYmW",
  "aXeaWYmXWWW00uYWWiXmeeWmfne00+/lw//tzlt/w/z///VXWmbWWeYmeWbWYWWW00000"]
@[expose] def ext_full_bve_collect_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_resolve_pair : armIsa.Hints := _decH #[
  "YE5F101812040G190D3H0D0I0I095D09210C0323090J110J3E16070D240C0J490K330K0F0F095409260C01",
  "21090J160J3E1D070K240C0D2D090J140J3E290B4D2D3D2D3D2D3D240D0B174D24070E16A0745B0D8F27KH",
  "G9F2E47XG201A45B0D8F27KHG9FG4RIOH2E6ArG201B45B0D8F27KHG9FG4RIOHU61EBrG108345B0D82E6302",
  "02745B0D8F2HGYAFY732ED7YG201845B0D8F2HGYAFY73YDD1E8YG10A3ZQ645ZPE0300005ZQ645ZPEB0D814",
  "501005ZQ645ZPEB0D814501005ZQ645ZPEB0D81450101020010YWjuWZkjvtcyWWkXWicWWyYWuidWZnWmcWW",
  "yYWuidWZnYL0aWXYWWWWWWWYWWWWWWaWWmmWXWWWWWaWaWWmmWXWWWWW00YWWnWWWWWWWfWWabWmYWWegXWmYW",
  "YWYmYWWegXWmYWYW00auWndaypoiWWcWWaWWWiWWeWZWvmWWWWWiWWeWZWvmW00/v/+y///////b//tr+/v//l",
  "hz+/x/x/u/v//lhz+/x/x/VcWXZWWWWWWWwWWegXWcWWmqYXWaWaWdWcWWmqYXWaWaW00000"]
@[expose] def ext_full_bve_resolve_pair : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_weaken : armIsa.Hints := _decH #[
  "X65L1M6N0N19153O19450505053404050O05050D040O0705350J150P1605080708070E56060Q0740015001",
  "0074RBM5S9L6T7UJN1Q7ZK10184RBM5S9L6T7UJNMQ08ZK00294RBM5S9L6T7UMQXCOJN109jK101080210340",
  "560780dcWWYZmWWkXubua/L0YWWWWWWWmYWWWWYWWWW00XWWWWfWeeXWWWWWeWeW00ZYaWWXuWXcWmWyWW00y/",
  "///b/llz/////l/l/VZWWWWwWmmYWWWWWmWmW0000979AB2C53D"]
@[expose] def ext_full_bve_weaken : List (SigEntry × Nat) :=
  [(("full_extend_push_cl", [i64, i32, i32], [.bool]), 0),
   (("full_delete_binary", [i64, i32, i32], []), 0)]

@[expose] def hint_full_bve_commit_res : armIsa.Hints := _decH #[
  "b94V1R1Q9710000M0X00J0J0J0M05040T04070505AJ0N050N0505000O0B481606072101190801063816060",
  "72101190801063816060721011908010638160607210119080104080B17451808072E0E19050E04070S0T0",
  "9440405050B050E091X100080X10000080X112060802020000310100090E0B5E050L07020B220J320J0105",
  "0B050J0E0B51000L071L07050515050M0515053O3L1J0J050405072E0E19000E05072404190E04241M0407",
  "M00150010054U8VARCQ6X2145010274U8VARCQ6X2RX0QM07Y000284UARCQQM8V6X2RX0P01T88102A4UQMXK",
  "NXOO8VARCQ6X2RX0XGT0A2000DARCQXOOXN0QMXGT4U8V6X2RX0XKN2Y0X0D2Y0Y0214DG100DARCQXOOXN0QM",
  "XGT4U8V6X2RX0XKN2Y0X0D2Y0Y0214DG100FARCQXOOXN0QMXGT4U8V6X2RX0XKN2Y0X0D2Y0Y022Y0X052Y0Y",
  "0E14FG101GARCQXOOXN0QMXGT4U8V6X2RX0XKNXQ42Y0X0D2Y0Y022Y0X052Y0Y0E0GG001GARCQXOOXN0QMXG",
  "T4U8V6X2RX0XKNXQ42Y0X0D2Y0Y022Y0X052Y0Y0E0GG001GARCQXOOXN0QMXGT4U8V6X2RX0XKNXQ42Y0X0D2",
  "Y0Y022Y0X052Y0Y0E0GG001GARCQXOOXN0QMXGT4U8V6X2RX0XKNXQ42Y0X0D2Y0Y022Y0X052Y0Y0E0GG003E",
  "ARCQXOOXN0QMXGT4U8V6X2RX0XKNa342Y0X0D2Y0Y020EG00274U8VARCQ6X2RX0QM07Y0000B4UQMXKNaMSaN",
  "TXOO8VARCQ6X2RX01LBQ101C4UQMXKNaMSaNTXOO8VARCQ6X2RX0aPL0CQ00034UQMXKN032001D4UaMSaNTXO",
  "O8VARCQ6X2RX0QMaPLXKNaT40Dam6002G4UaMSaNTXOO8VARCQ6X2RX0QMaPLaU4b25XKNaT4b3E0Gom6000G4",
  "UaMSaNTXOO8VARCQ6X2RX0QMaPLaU4b25XKNaT4b3E0Gom6007K4UaMSaNTXOO8VARCQ6X2RX0QMaPLbR0bG6a",
  "U4bP1bH8XKNaT4b3Eb250Kaum600B94U8VARCQ6X2RX0QMdNLdS409k000302028F2304i122400YWWuXcWYiW",
  "WzoWmeWWWWzmWWWZmuWWdiWdWWWWWWWWyWWXcWtWWWpWhmauYyXcWtWfmbuWWYkzmWWWW/+L0eaWWWmWXWWWWW",
  "WWaYaWWaeaWmaYYWWXWWWWmWXYmWWWeWWmWaeWWeWWWYWWWWmWWWaWWWWWWWWWWWWWW00aWWWWeWWmqWWWWWYW",
  "YWWYaYWeYXXWWWoWWWYWmmemWeaWWeWYaWWaWWWXWWWWeWWWYWWmWmWWWmbeXWW00XWeWYWWaWWimWYWWWWWin",
  "WWWXmemWZaepYWWWWWWeiWWWYWXWYWXWWuWeWcWYWXmWmWeWaWcimemWmWW00/p//x/lt++d/////v/v//vtx/",
  "lxyy//+f///x++/k//lpx/l/xpz/t//lz//x/l/+/x/+/+///+Xnlz//ViWWaWmeXXuWWWWWcWcWWceaWmaZZW",
  "WXsWWWaXXWnWWmiaWmWaiYWeWWmYWWaWmWXWaWXWXWWWX+kmYWW0001B79AB2C53DEF"]
@[expose] def ext_full_bve_commit_res : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 192),
   (("full_add_unit", [i64, i32], [.bool]), 128)]

@[expose] def hint_full_bve_ext_need : armIsa.Hints := _decH #[
  "D48160925351945050000001E0730010001004A688546D20E4C2015A688546DDE105C1000+hm50mWWWW00e",
  "WWmWG0ckXu00dd/+/+VuWXWX00000"]
@[expose] def ext_full_bve_ext_need : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_weaken_unit_fid : armIsa.Hints := _decH #[
  "P4J15140B1U1Q19153D19350505053D0D050D0R0714052S0S05400150010224O5S02200064O5SHQFU6L7M1",
  "R6XI10174O5SHQFU6L7MKR07XI001080B10C40560980imWXudbubeK0YWWWWWWWW00XWWWWeWeY10aWWauYWy",
  "WW00d//y////l/lxTZWWWWmWma2000779AB2C5"]
@[expose] def ext_full_bve_weaken_unit_fid : List (SigEntry × Nat) :=
  [(("full_delete_binary", [i64, i32, i32], []), 0)]

@[expose] def hint_full_bve_var_m7 : armIsa.Hints := _decH #[
  "fE350X10G0T0D0E0O0U0M1Q10181615051112030F1112050505050505360606074008190A20053819380B0",
  "A3E0705250C0A3E07271T03030D11120F050505050505360606074008190A20053819380B0A3E0705250C0",
  "A3E07271J0J0909050D050B09061105194505001B581948080000001507190112092633194606080808150",
  "7150J0J0505090509052D100A000A1J0J092935050D000D100D15092509350535051VI705053500051X035",
  "09500030080019000008090800090V0D053E100J0J0U0B0X101010X10M02050203095616074505050L0L18",
  "05070N0N0N000007150P0J0505080B08060B0816090I0102030F060G4819080908080J2908084808080828",
  "0525050O075O075O075N450D05050U0L0L1D0D0715050715090505070595051J0J1M1D340X1040J240O140",
  "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",
  "OV4ReTXIg0XKfSX0eOXJHQCXAb1SBX9UX7SX8FX4YUXFfHNJX6QXBLXCX0X5ATVX3dAXGNXE7XDeCXH5X2g6O0",
  "UekWbY0006X6g2Mg3Ug4LgOV4ReTXIg0XKfSX0eOXJHQCXAb1SBX9UX7SX8FX4YUXFfHNJX6QXBLXCX0X5ATVX",
  "3dAXGNXE7XDeCXH5X2g6Oi80iT3iUFiG5iV6iS2iR1iQI0X6fekWbY0002X5g2Mg3Ug4LgOV4ReTXIg0XKfSX0",
  "eOXJHQCXAb1SBX9UX7SX8FX4YUXFfHNJX6QXBLXCX0X5ATVX3dAXGNXE7XDeCXH5X2g6Oi80iT3iUFiG5iV6iS",
  "2iR10X5fekWbY0003P4ReTXIg0XKfSX0eOXJHQCXAb1SBX9UX7SX8FX4YUXFfHNJX6QXBLXCX0X5ATVX3dAXGN",
  "XE7XDeCXH5X25MUL5OPmyWg4501A4RFX4kOM5X2X0X5ATb1SVX3YUXFdAXG0AbO003D4RFX4kOM5X2X0X5ATb1",
  "SVX3YUXFdAXGl2LU4UX70DbO00244RFX4kOM5X204800734Rm1MlTQ1D301003lTQ4Rm6D03000XD02078243A",
  "8306P23IG123HH02388823CI3E3EJ3DK37L33M3FB3113B404180358X423511418Z/////V3580418Z/////V",
  "35812351F23511418Z/////V35832351A226EYF2215XQ2215X62215023G8Q2215X62394A428326DA2328F2",
  "368022157226BD2348322618224242214122I6M22893226AD2267522886224CH22871226832243ZE228F82",
  "26I4226HI228GS20A80uWjeWeeeaaWWWmeeWWWWWWWWuuYsXmWWsuWYWWWmWWWXyWsWWWWWdWWWeyWzZmWl/zd",
  "dZYWYWeeWmWWWXeWWWWXytWeWWZvkWZvaWWWWWWkXmWdWytcYiWyWgWWWyZWWkXvkiauXuXeqrgW10eYaWYWWW",
  "WWWWWaaWWWmaYWeWWWWWWWaXYWWWWWWmaWXWWXYWWXWWXWWWXWWWWWWoWWWWWWWWmWWWmXWXWeWWWXWWWWWXYW",
  "WWWeWWWmWoWeaWWWYWWWWWWWWWWWWmeWWWaWWWWWWWWWWWWWWW00XYWXeWWWWWWmYYYWWWYXWaWWWWWWWYWnWW",
  "WeemgYWWmWWmWaWnfeWWeWWWYWWWXWWWWWeeWWWWWeWmqYaWWYmmWXWXWnWWYWaWYWemfgaYWqWXWgXWWqWeWW",
  "WWeaXeWYWqYWXeWmWWWWWWW40eWWWWWWWWWWaWXXZiWWWWWWWeWWWWWWWYeWWWYWWWWWyyWWWYaWWZmWWalWin",
  "yWWWWZZXWWWmWWWWWWXWWWWWWiyZmWWWvucWfuWWiWWWWcWmWZWiYYWaYigWiWWiXWWcWuaaWeauqWWWWW00lx",
  "t/zx/yl//////dxuf///vy/p//////xx+z///lk/Zx/+d/+//t+iWl//jY//x///z/////ll/////l++tvtzlw",
  "+l/z/z+y//x/t/x/kljhtx+t/z/hz/+t/l////ltzl/x+tx/zl+////////7aeWYaWZmWWWWWWuadsWWWcZWiW",
  "WWWWWaaXYWWWmnWyaWXuWXWWeXp/mWWozWWaWWWYWWWWWmmWWWWWmXXeceYmbXmWYWYXZWWaWeWaWnmoqeaXeW",
  "YWqYWXeWmWWWWmeYmWaXeaWYmXWWWWWWWWO00JB79AB2C53DEF"]
@[expose] def ext_full_bve_var_m7 : List (SigEntry × Nat) :=
  [(("full_bve_weaken_unit_fid", [i64, i32, i32, i32], [.bool]), 64),
   (("full_set_inactive", [i64, i32, i32], []), 0),
   (("full_bve_gates_m7", [i64, i32, i32, i32], []), 320),
   (("full_bve_gates_fid", [i64, i32, i32, i32], []), 784),
   (("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]), 0),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_bve_weaken", [i64, i32, i32, i32], [.bool]), 80),
   (("full_bve_commit_res", [i64, i64, i64], [i64]), 304),
   (("full_dense_prop_unit_m7", [i64, i32], [.bool]), 208)]

@[expose] def hint_full_bve_var_key_m7 : armIsa.Hints := _decH #[
  "YP221D0B1104040D0D0D0D0D38080X116080X12E190E0D0D272019000D0D0E0B14040D0D0D0D0D36060X11",
  "1060X12419040D0D272819080D0D000B1B0E0B0004040E041D09152505152D050X10E0B0D0D0B0E0E050D0",
  "50B051B050405600150010146245B1C41E4810166245B1C4Q6R82DE6820336245XIE103010156245XIEY11",
  "Y262D0502031Z141510101020H60ZewaWWWhWYuadWWWbmXiYZmX20eWYWWWWWWaWXWWWW00amWWmWWmWaWXXW",
  "WWeWYWWmmWW80mXqWXWeWeWYXWmeWZYmXWmeaWXne00ltqZY//+/w+e/sdzz///alxZ++///FehyzWWXWbXtWf",
  "uYYWWWxmayXXWWWG0000"]
@[expose] def ext_full_bve_var_key_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_heap_up_m7 : armIsa.Hints := _decH #[
  "P46130D0A0710110F25050A220303091E0E24040A280A4509353000000033F0IF6D15341007F0IF6DS3Q2H",
  "18615741000ZWZiicWZXom50XWWWWWWWWW00mXXWXWeWb00XWXaaYmfWuW00//+/zz/z/XonVXWYYWYW+jk000",
  "00"]
@[expose] def ext_full_bve_heap_up_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_heap_down_m7 : armIsa.Hints := _decH #[
  "X54F1H0D0A071E1G0K28080A2I0H0H01050A50000A220607210107230X10002063B5801050A38400000003",
  "3FEIK6D18341008FEIK6DHG8F54SHQI3158843029X28FEIK6DHG8F54SHQI3026983100iWZsWcXmicWZXom5",
  "0maWWWWWWW00YWWmWeYXWaWeWb00aWXoWYWmaYWfWuW00Z//v/+u/lxz/p/XonVcWXdWmaYWiW+jk00000"]
@[expose] def ext_full_bve_heap_down_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_heap_push_m7 : armIsa.Hints := _decH #[
  "Z540180D0A07161233082202070B2005020G0B0706030I2E0E0A1F0G0G09180820000A210A4E093E070X10",
  "G0K0B07020I0XL28080A1H0K0K01000A5E0E0A2306072101072F0X10E03063B5801000A38020G0B0706030",
  "I2E0E0A1F0G0G09180820000A210A4E093EA0015001041X050100034X05X56X7I641E481008X05X56X7I64",
  "XGGXEFX63X121E88104155010005455YE2YGXL641848100855YE2YGXL64YFIYAGYPKYNH3108883029YV855",
  "YE2YGXL64YFIYAGYPKYNH3E369G317455aB6aDI641E48100855aB6aDI64aMGaKFaC3a721E8810G06018086",
  "064CG30834632431136I33M37L35H020G8142H5242122L7222I612280122M33226432211Y02211M2264022",
  "64XN2211K2264022640iWjnmuWeiWWXmWkuWucXmuWeiWWWWiWjnmuWeiWWiXnom50aWWWWWWWWWWWWWWWYWmW",
  "WWWWWYWWWaWWWWWWWWWWWWWW00YWaaWaYWbWWWeWYWXWeaWmYWbXeWWYWaaWaYWbWXeWWb00aWammgXWcWWWmW",
  "ceWeYWmeXWcWWWWaWammgXWcWWaauWW00///x/tt/tuiX///d/xZz/lt+luiXyl//x/tt/tuiX/yl//nVaWeeW",
  "edp+WWWuWayYWmeXmdp+ZmWWaWeeWedp+WZmWWk00080"]
@[expose] def ext_full_bve_heap_push_m7 : List (SigEntry × Nat) :=
  [(("full_bve_var_key_m7", [i64, i32], [i64]), 0)]

@[expose] def hint_full_bve_heap_pop_m7 : armIsa.Hints := _decH #[
  "XM3H1E0J071D0K0K070022092XL0XL070E230I0B070D1F052E0E0A2G0I0I08050A54040A26000728080721",
  "0X10406003B5E08050A3E0K070560015001026EK7H45DD9E540610012EK7H0210055EK7HX2DX5X2OXL1E5H",
  "100AEK7HX2DX5X2OXLX4FU3K2XFIXDG385EAH302BXLEEK7HX2DX5X2OXLX4FU3K2XFIXDG3460BX2312XJ230",
  "8XT22800XmWkuWucXmuWiceWuXmcWe50YWmWWWWWWWXWaWeW00eWYWXWeaWmXWXeWmYWaYG0eWmWceWeYWmeXa",
  "ZWWiWmZWW00+///d/xZz/lt+lyceWw/x/tuVXWWWuWayYWmeXmZvt/bWaWed00010"]
@[expose] def ext_full_bve_heap_pop_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_collect_nbrs_m7 : armIsa.Hints := _decH #[
  "YM30131F1O1H1XL161G0Q0M2D0D0X105050505053I0I0I074D08190A2D0K0D020205193102095505090507",
  "28190808080J180J072E1D071705050905072D190D0D0D0J1D0J072E17271R0X1190B3D6D6D6D340D0B173",
  "53407D001E001002J6LG1E20100BLGJ670BF9354DONMMQHXLFH2ERBf0200CLGJ670BF9354DONMMQHXLFHPR",
  "1ECf0101DLGJ670BF9354DONMMQPRHXLFHX7I2E5Df0200DLGJ670BF9354DONMMQPRHXLFHX7I2E5Df0204EX",
  "LKLGJ670BF9354DONMMQPRHXLFHX7I1EEo0100GLGJ670BF9354Y02XLKDONMMQPRHXLFHX7IXV12EDGXXX020",
  "1HLGJ670BF9354Y02XLKDONMMQPRHXLFHX7IXV1Y3D1EHXXX0108EXE8LGJ670BF9354DONMMQPRHXLFHX7I1E",
  "Eo01093ZUEJ6LG14301003ZUEJ6LG14301003ZUEJ6LG14301000XxWWkzxtkzmWWWXmXWXiWWWWiWeWhWXuZo",
  "WufmZmWWrgL0mWaeWWWWWWWemnWYeeaXYWemWoYXWemWWWWWWWWWaWWW00eWYaWWWWWWXaeemXaaYWnWaeWfXW",
  "maeWmaWYmXWWYWWW00vWYcivpcimWWWWmWWmWWWWWaWWaWWWuXmeeWmfnWWWW00dd/xp//////ytdk/zttx+b/",
  "td/jz+/nl+/t/w/z//x///VuWaiWWWWWWZeunWYeeaXwWeuWoYXWkmXWeWbWYWWaWWW0000479AB"]
@[expose] def ext_full_bve_collect_nbrs_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_elim_bve_m7 : armIsa.Hints := _decH #[
  "dA3Q1S1V1L101E1D090B150574050B173407400V850B0509050J050J0M05140X1040J240O140A05050J0O0",
  "90B15057D050B173D070945050J0505050J0D2M071J2509050J050J050X10I0E0J07050O0O070D22092XL0",
  "XL070E230K0B07050G0M20000A2H0K0K060D0A5E0E0A2108072606072F0X10E01083B50060D0A300O070O1",
  "N0D0J050A2D0E090E0E0E090D0505151J04090J0U0D1E0X10E0J240O1E0A0D0D0J050X10U094D0D072E190",
  "000000J0E2O0729293D0X14D0J0D050B0J150J1509150X10J05050B05090B340434043404340405040B173",
  "4040507090B340434043404340405040B1734040507150905X900150010074R5X09S7QDLBVF00700009BVF",
  "04RJDHE5X09S7QDL14901009BVF04RJDHE5X09S7QDL14901009BVF04RJDHE5X09S7QDL149010534R7Q5X03",
  "54E3030064R5X0XFV9S7QDL34EXA6030474R5X0XFV9S7QXNXADL07000084RY0M5X0XFV9S7QXNXADL158010",
  "084R5X0XFV9S7QXNXADLY2508000484R9S7Q5X0YHOXNXAXFVDL08000084R5X0YHOXFV9S7QXNXADL1D80100",
  "84R5X0YHOXFV9S7QXNXADL1D8010084R5X0YHOXFV9S7QXNXADL1D8010574R7Q5X0XFV9SXNXADL147010084",
  "R9S7Q5X0YHOXNXAXFVDL24M8020194R9S7Q5X0YHOXNXAXFVDLZAM149010474R7Q5X0XFV9SDLXNXA354T703",
  "0074R7Q5X0XFV9SXNXADL24T7020074R7Q5X0XFV9SXNXADL24T702049ZST4R5X0XNXA7Q9SXFVDLZR41O901",
  "02DZST4R5X0XNXA7Q9SXFVDLZR4aAOa5Ia95a6E0Dm0001BZST4R5X0XNXA7Q9SXFVDLZR4aAOa5I0Bm0005EZ",
  "ST4R5X0XNXA7Q9SXFVDLZR4aAOa5IaU5b0MaKXL10Eem0100JZST4R5X0XNXA7Q9SXFVDLZR4aAOa5IaU5b0Ma",
  "KXLaVGaQ3aG2bAKb8H36D0Jem0302KbG0ZST4R5X0XNXA7Q9SXFVDLZR4aAOa5IaU5b0MaKXLaVGaQ3aG2bAKb",
  "8H3E18KnW031BBcSN4R7Q9SDL5X0XNXAdDMXFVZSTdEX20B0000C4RdKUcSNdDMZSTdEX27Q9SDL5X0XNXAXFV",
  "1DC0100CcSN4R7Q9SDL5X0XNXAdDMXFVZSTdEX2dMD0C000474R7Q5X0XFV9SXNXADL24T7020194R7Q9Se7UD",
  "L5X0XNXAdDMXFV24O90201A4R7Q9Se7UDL5X0XNXAdDMXFVeAO14A010914R01000134RfFD7Q03000034RfFD",
  "7Q03000734RfFD7Q153010034RfFD7Q153010034RfFD7Q153010534RfFD7Q153010034RfFD7Q153010034R",
  "fFD7Q1530109040F6078Y34180318ZA2068b720B802308X42260U2068N2241423140eWuWWykdZWWWuWWykd",
  "ZWWWaWmmWWmWWWWWWWWsXmWWWWuWWWWWWcWWWXmWkuWucXmuWicWXmZWiWWWWWWWWWZWWuWYrgmWWWWcWWWWWd",
  "vwWuWYrgmWbgL0XWXYWWWWWWnWXYWWWWWWmXWWaYeaWeoWWnWaYWmWaaWeYaWWWWWWWWWWWWWWWYWmWWWWWWWY",
  "WeWmWWnYWeYXWaeXYWWWWXXWYWnWenYWWWeXYWWWWXWW00mWnWWWWWYemWnWWWWWYeWmYYXaYWaXWWemYXWeXY",
  "YWWXYXfWXXWoWWWWeWYWXWeaWmXWYmXWaWegaenYaXWmYaWnWWWWammWWemaenWWWaWnWWWWamW00eWmicZXWW",
  "WeWmicZXWWeWWWWWWWWWWWWWWeYWmWWWWeWWWWWaYWWeWmWceWeYWmeXaZWWuXWcWWWWWWWWaXWWeWmWWYWWWW",
  "YWWWWWWYWWeWmWWYWWW00j+l+y/////vkl+y/////vjY/xxztx/pz//klxz/lzxxt/zxzj/zy+Z+///d/xZz/l",
  "t+lycWXr/t/lZtkzxpz+lxp+y////o+z//k/tkz///p+y////o//VYXmXZWWWWWcnmXZWWWWWcozWaaYeaWiYW",
  "WnmaYWmYaaeWYaYoWYZXyXWWWuWayYWmeXmZv/+gWeWmyenYaiYXmaiXZWWWWjXYWWnWenYWWWiXZWWWWjWW00",
  "02B79AB2C53DEF"]
@[expose] def ext_full_elim_bve_m7 : List (SigEntry × Nat) :=
  [(("full_dense_prop_unit_m7", [i64, i32], [.bool]), 208),
   (("full_bve_heap_push_m7", [i64, i64, i32], [i64]), 80),
   (("full_bve_collect_nbrs_m7", [i64, i32], [i64]), 48),
   (("full_bve_var_m7", [i64, i32], [i64]), 1040)]

@[expose] def hint_full_has_elim_cands_fid : armIsa.Hints := _decH #[
  "D2E10180934190D0D0D0J19050730015001003A8806E15301014A8806EC50400000eWhWL0XWYXWW00mnWmY",
  "00aXW00kkz+/xVXnYXWa00000"]
@[expose] def ext_full_has_elim_cands_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_eliminate_m6 : armIsa.Hints := _decH #[
  "YR3O150705051514051405051B0515052D0X1040B05050B04040D050434052E101809053D190505050J190",
  "4070515150905150B05050Q0Q1J1810090B1D0D7E0D0B173E07341D0D0B040D0B14040904041E04040D0D0",
  "90D0J0J150905E00150010034R7O5Q153010144R7OOX25Q04000144R7OOX25Q144010234R7OOX203000164",
  "R7OOX2XL8XJ0XHE146010174R7OOX2XL8XJ0XHEXO407000634R7OYJQ03000054R7OYJQYP0YN81E5010054R",
  "7OYJQYP0YN81E5010054R7OYJQYP0YN81E5010544RZH5ZGQ7O1D4010254RZH5ZGQ7OZRD145010144RZH5ZG",
  "Q7O040007040A6078K230852068YB22600231832261XH20A80eWWWWWWbWXmWbgrWWgWYYWWWmWsWgmoWWWWa",
  "Wom50YWWmYaWWWWYWWWWeYWaYWWWWWWWWWWWWa00YmaWYXXWWeXYWWWWfWmWWWXXYXWXWWWWWamWWWW00mXWWW",
  "aWWWWWWWWWeYWWWWXqWWWYWX00dzw/t/xzz//dzv////b+/ll/yzxz/z///yZY/+//yVYbWeWaYYWWuYcWWWWw",
  "XWmmWZYaYWYWWWZyzWXWWZ0XWWWWWWWWWWWWWWWWWWWW002379A"]
@[expose] def ext_full_eliminate_m6 : List (SigEntry × Nat) :=
  [(("f64u_nlogpown", [i64, i64], [i64]), 48),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("full_scale_delta", [i64, i64], [i64]), 16),
   (("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 656),
   (("full_forward_sub_m7", [i64, i64], [i64]), 384),
   (("full_elim_bve_m7", [i64, i64], [i64]), 1152),
   (("full_rebuild_watches_nosort_fid", [i64], [i64]), 592)]

@[expose] def hints : List armIsa.Hints := [hint_full_bve_collect_m7,
    hint_full_bve_resolve_pair, hint_full_bve_weaken, hint_full_bve_commit_res,
    hint_full_bve_ext_need, hint_full_bve_weaken_unit_fid, hint_full_bve_var_m7,
    hint_full_bve_var_key_m7, hint_full_bve_heap_up_m7, hint_full_bve_heap_down_m7,
    hint_full_bve_heap_push_m7, hint_full_bve_heap_pop_m7, hint_full_bve_collect_nbrs_m7,
    hint_full_elim_bve_m7, hint_full_has_elim_cands_fid, hint_full_eliminate_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_extend_push_cl", [i64, i32, i32], [.bool]), 0),
   (("full_delete_binary", [i64, i32, i32], []), 0),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 192),
   (("full_add_unit", [i64, i32], [.bool]), 128),
   (("full_set_inactive", [i64, i32, i32], []), 0),
   (("full_bve_gates_m7", [i64, i32, i32, i32], []), 320),
   (("full_bve_gates_fid", [i64, i32, i32, i32], []), 784),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_dense_prop_unit_m7", [i64, i32], [.bool]), 208),
   (("f64u_nlogpown", [i64, i64], [i64]), 48),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("full_scale_delta", [i64, i64], [i64]), 16),
   (("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 656),
   (("full_forward_sub_m7", [i64, i64], [i64]), 384),
   (("full_rebuild_watches_nosort_fid", [i64], [i64]), 592)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Eliminate
