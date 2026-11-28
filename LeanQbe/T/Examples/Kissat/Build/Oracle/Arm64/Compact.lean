module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Compact

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X2)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X25)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X3)),
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28)), (XRegOrSp.reg (XReg.X29)),
  (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X7))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X1))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.flag LeanQbe.T.Arm64.ArmCond.gt),
  (.flag LeanQbe.T.Arm64.ArmCond.lt), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.slot 0 .w64), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.gpr (XRegOrSp.reg (XReg.X29))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.slot 1 .w64)]

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

@[expose] def hint_full_compact_needed : armIsa.Hints := _decH #[
  "B200110011002130403030210013001000aeH000nY40YWW00/kbxNnwa80000"]
@[expose] def ext_full_compact_needed : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_flush : armIsa.Hints := _decH #[
  "D230113011301131002150103013001300101146010002146010001020010rWWWbYWH0XWWa00femeY4000/",
  "//ik/lxNpnWma800010"]
@[expose] def ext_full_compact_flush : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560)]

@[expose] def hint_full_compact_mark_live : armIsa.Hints := _decH #[
  "bU2708191A1B1C1D16010E4F110F0F0F050F5F112F050F5F112F050F5F112F050F100F0E1G4F110F0F0F05",
  "0F100G0110000000003707070H0H1I3G3F11000F0F0G0001000J05001J05000J11000F3J1100101G0K0G1I",
  "011H020F0F0L3K000D07000J022C3000000211001G2J01000G07000000001M150E0K0H0E0C67070G1H0N05",
  "073715070J0D200G31010F0E47070G1D05073D111737070G1D05073D111737070G1D05073D111737070G1D",
  "05073D1110070E1G47070G1D05073D11100G0GX008DBBA9978HDFC43J6080000999BA7867DBFC43HDJ6109",
  "0100999BA7867DBFC43HDJ61090100999BADB7867FC43HDJ61090102A99BADB7867FC43HDJ6M01FA0101A9",
  "9BADB7867FC43HDJ6M01FA0101A99BADB7867FC43HDJ6M01FA0101A99BADB7867FC43HDJ6M01FA0103A99B",
  "A7867DBFC43HDJ6YF01FA0102643J6BA9978DB0600008DBBA9978HDFC43J61K801019DBBA9978HDFC43J6Y",
  "VK090000CDBZEIBA99YVKZCH78HDFC43ZA7J610CX0101CDBZEIBA99YVKZCH78HDFC43ZA7J610CX01090000",
  "000743J6aQIBA9978DB1M70102B43J6aQIBA9978b1Lb5Kb0FDBaTH10Bc0113Db7Db87b0FaQIaTHb5Kb1L43",
  "J6BA9978DB10DZ0100D43J6aQIBA9978b1Lb5Kb0FDBaTHbP0b870Dc00028c7M43J6aQIBA9978DB080003Bc",
  "7M43J6aQIDBBA9978b5Kb0Fb1L2JDBXe0200Cc7M43J6aQIBA9978cECb1Lb5Kb0FDB3JD0Cu0300Dc7M43J6a",
  "QIBA9978cECb1Lb5Kb0FDBcH02JDDu0204BDBBA9978c7M43J6aQIb5Kb0FdBD0Be0003ADBBA9978dFFc7M43",
  "J6aQIb5K10Am0100ADBBA9978dFFc7M43J6aQIb5K10Am0100ADBBA9978dFFc7M43J6aQIb5K10Am0101BDBB",
  "A9978dFFc7M43J6aQIb5KdH00Bm0003BDBBA9978dFFc7M43J6aQIb5KdH00Bm0003BDBBA9978dFFc7M43J6a",
  "QIb5KdH00Bm0003BDBBA9978dFFc7M43J6aQIb5KdH00Bm0005BDBBA9978dFFc7M43J6aQIb5KfU00Bm00000",
  "ahmedWWahmedYbuaZnYyYXunkXWyWWaWXkWedWWYWWWuWmkuWyWXWWaYyYWmWWWsZqZmWWWWtWWWutmihucbyW",
  "YyWgr90YaXWYYWaeXWYYWWmXXWWeWmmWaWeeWXWmmWWeYWYYeWWaYWWWWWWWWaaWWWWWWWWWWWWWWWaWYWaeWY",
  "WWXWWWmWWeWYWW00XYWmXXWYaWmXXWWeWmmWaWeeWYWaaWemeeWWbXWXXaWWYXXaWYWWaaYYWaWaYXXYXWaWWW",
  "XYWXWYaWXWWWmWWeWWaWfWW00uWZWYWWuWZmWiWXuWcWWyWZWWiWWWWWdWWZWuWWaWeWXceWimWWWWWcWWWWWW",
  "YWefnWWWeWWYWeWWaWWYWWXWWWWW00Xzv+/zz/xp+/zz//l++//t/ll/x/tt/k/ldZ/nz/yzt/pxzzmkv//ptv",
  "x/t/txzyuz/t///zvxz/xpxz/z+/+/l/lt/b//VYcXWYYWaiXWYYWWmXXWWeWmmWaWeeWnWmuyWkYWZYeWiaYY",
  "lncWWiecaWeWeaYZdYWeWWWYcaYWaiaYWYXWXWmWmeWwWW000010"]
@[expose] def ext_full_compact_mark_live : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_assign_map : armIsa.Hints := _decH #[
  "G2F1A191B01480108080805082803300G40013001004CBA98A6F230402015CBA98A6FF013501006E3CBA98",
  "A6FF00600000icWWiYL0eWWaYWW00aWWYXWe00aYWeaW00Zp//xz/lViWWaYWm00000"]
@[expose] def ext_full_compact_assign_map : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_record_ext : armIsa.Hints := _decH #[
  "XD34181F0G171K1D2A0A0A010A080F0G18080A0F0A0G2A0B0B010A0O0B0A2A0F180G3000000001200F0E6F",
  "00080G70013001026IDE74369GK5018601006436950E7IDGK28F6020244369IDGK1F401006IDE74369GK50",
  "28F602007IDE74369GK50X481F7010244369IDGK208402000+WcWZWXmWWWWWbeK0XWWWWWWaWWeWWeWWW00m",
  "WYWaWYWWaYWaWWY10gWYWXWWmWXYWnWW00d+l/udt/v/utudol/xTXmWdueWcWdedujmWa20000"]
@[expose] def ext_full_compact_record_ext : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_bins : armIsa.Hints := _decH #[
  "c8331P1D1F17112L0L0L0I0I3B0B0508280118051B0G5A11080C080C0G080Q3Q01081C05080Q0A0Q2Q0Q0K",
  "0H083G2G080E18087A080E1G3A0G050808080B080J0G0J0G1H110E181A010A010A0B17170B0B1707170B0B",
  "1707170A0A1808180B081A010A010A0B17170B0B1707170B0B1707170A0A18081803080E1G181A010A010A",
  "0B17170B0B1707170B0B1707170A0A180818030G0G030E1308180818081303130308180818081303130308",
  "18081808130313030818081808130319030E1G1308180818081303190GM000000005DFBD6R50461H501008",
  "5046739PBDDF6RF72HJ80202DIHOIF79PBD73DFJJML50466RTB1MDaW2102CDFJJMLOIX8BF75046739PBD6R",
  "2HKC0200DF79PBD73X7MX8BDFJJMLOI50466R3H8KD0301DF79PBD73X7MX8BDFJJMLOI50466R3H8KD0306EY",
  "HH5046739PBDDF6RF7JJX8BYIKMLOI0E0000EDFJJMLYIKOIX8BF7YHH5046739PBD6R1AE0100EDFJJMLYIKO",
  "IX8BF7YHH5046739PBD6R1AE0100EDFJJMLYIKOIX8BF7YHH5046739PBD6R1AE0105CYHH5046739PBDDF6RF",
  "7JJX8BYIK0C000336R50DF0300004DFBD6R5013401004DFBD6R5013401004DFBD6R5013401025DFBD6R50Z",
  "P30500025DFBD6R50ZP30500045DFBD6R50c23050003250DF1920100250DF1920100250DF192010302001A",
  "2302fB22200XYaeWWnYaaenXYaeenYWWWamoYegWXWWXaamoYmWeamoYegWXWXWWWWWWiWXgreWWWXmXWyWWbm",
  "WeiZmWrA0mWWWemWWWWWWWWWWWWWWaeWWWWWWaeYaWWWWWWXYWWWWWWWaeWeYXWWWaWnWWWWWemWWWWWWWWWWY",
  "WWWWW00eWWWaeWWWWWWWWWWWWWXYaWWWWWWYaXYWWWWWWWnWWWWWWWYaXaXWmWXYWemWWWYaeWWaYWaWeXXXWm",
  "WXW00vpaWaivopciqvpbcivWmWZijnsbWWWXWxZijneWWZijnsbWWWWWWXWaWaWeWWXXWWWmWWkWWWmWWcXnWW",
  "00dd///td/////////////yxp//////utzv//////+b///////utyty+l/zv/kl///vtl//tx/ntlzzz+//z/V",
  "uWWWeuWWWWWWWWWWWWWZaiWWWWWWdeYcWWWWWWXwWWWWWWWdeZeZXmWYcWnmWWWcemWWeaWkemYYYXWWYW0001",
  "3034"]
@[expose] def ext_full_compact_bins : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_arena : armIsa.Hints := _decH #[
  "bR3S1T1U0V1X0715F020303073B090800090A022D39090902110X11G2A01090G00000X10X10X11X111020B",
  "0F020300000058080G1F0N050F3F053F080F0A190G1505052375030009010Q0P0X2060A060G30380F0F090",
  "90003030E030701120A0B020A0A0B021H0B0K0H0H0A0A3D0D0A0107012F030H0E2H050D0301030507012D0",
  "A2003030E030B01120F0A020F0F0A021K0A0D0K0K0F0F37070F010B01290303030G0K0E2K0507030103050",
  "B01270F03030G23030G7GA8100079000E123902P00130010014X356QPX231050064X37SEX0BU9TCV596QPX",
  "26050064X37SEX0BU9TCV596QPX260502EO6PQQPRX24X37SEX0BU9TCVV3SFX4BX071X1EiW0113GX68X70O6",
  "PQQPRX27SV3EX0SFX4BX074X3BU9TCV19GZW0100GO6PQQPRX24X37SEX0BU9TCVV3SFX4BX07XO9X700GiW00",
  "05CO6PQQPRX24X3Y6X17SEX0BU9TCVX071ACYW0100FY6X1O6PQQPRX24X37SEX0YG0BU9TCVYD3X07X4B2A9F",
  "uW0200GY6X1O6PQQPRX2YG0BU9TCVYD34X37SEX0X07X4BYI91AGuW0109FO6PQQPRX24X3Y6X17SEX0BU9TCV",
  "aI9aIX4aE8aER0F+W00005O6PQQPRX24X3050001HO6PQQPRX24X3Y6X17SEX0BU9TCVaI9aIX4aE8aERaA0aG",
  "F0HZ+W0002KO6PQQPRX24X3Y6X17SEX0BU9TCVaI9aIX4aE8aERaJ0aGFaA0aO7aN30Kd+W0000KO6PQQPRX24",
  "X3Y6X17SEX0BU9TCVaI9aIX4aE8aERaJ0aGFaA0aO7aN30Kd+W0006OO6PQQPRX24X3Y6X17SEX0BU9TCVaI9a",
  "IX4aE8aERbGAb5BaJ0bEDaGFb6KaA0aO7aN30OYy+W0006BY6X1O6PQQPRX24X37SEX0BU9TCV0B00005O6PQQ",
  "PRX24X3050001FY6X1O6PQQPRX24X37SEX0BU9TCVaE8aERaI9aIX40F+W0002IY6X1O6PQQPRX24X37SEX0BU",
  "9TCVcB0aI9aIX4aE8aERcGBcF30IX+W0000IY6X1O6PQQPRX24X37SEX0BU9TCVcB0aI9aIX4aE8aERcGBcF30",
  "IX+W0007MY6X1O6PQQPRX24X37SEX0BU9TCVd8FcTAcB0d67aI9aIX4cUDaE8aERcGBcF30MxuW00092eO3eU8",
  "19201002eO3eU819201002eO3eU8192010604056071b8230832312B4221280H4221280Y342212800cWWrgq",
  "YreWWoWYWWWuWWWZWWWcWZmWWWWWWWaWZWWWWiWXmWyWWWWWWWWdkWWXkyuWWWkdWaZmWXWWWiWediWkWX/qL0",
  "YWemWWWWWWmWWeWemWYaYWmeeWWmWWWeWWneWWmWemeYXWWaWWWYWWaeWWWWeWWWWWWmWXWaXWWWWWWYXWWWWW",
  "WWWWW00XWaeWWWWWWeWWaWWeWXYXWeaaWWfWWWXWeeaeWWWaeaXWmWYeWWWeYYXYWWWaWWWWYqeWWmYmmWagWW",
  "XWmoWXWWYYWW00YWaWWWmWWWWWWWWWWemWWXYWWYafnWWWWWWaWWXYWWWaeWnYieWWWWWXWZcXWWcieWWWcZmW",
  "XpZWWYWaWWpaWceWWW00y/td//////l//t//l/yxz/lpt//a///z/lltl///pltz+l/vd///lxxzx///tnx//u",
  "dd/+/u+//ph/vz++udi//vx//VZWeuWWWWWWmWWeWWmWZaYWmieWWxWWWYWmmemWWWimeYXmWcuWWWmaaYaWWW",
  "ekaWWduuWXWdXWWiqWcYXXdupWWcaWW0002B0349A75BCDE"]
@[expose] def ext_full_compact_arena : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_compact_vars : armIsa.Hints := _decH #[
  "XO461F1J1C13191A1B171D1K1H1I1M1L1V09010E1873080E1G230G01564P2P1P1X2210P03010P0Q2P4P262",
  "80G2G090EXS9080E1GF90GA3021303B00000000I6X350ECCJUHSKQDO7MBKAAFX6V4X1IX4GRX4LX2MX0I0I0",
  "000K6X3X798650ECCJUHSKQDO7MBKAAFX6V4X1IX4GRX4LX2MX0I13K0100K6X3X798650ECCJUHSKQDO7MBKA",
  "AFX6V4X1IX4GRX4LX2MX0I13K0100K6X3X798650ECCJUHSKQDO7MBKAAFX6V4X1IX4GRX4LX2MX0I13K0105H",
  "6X34X1IX4GR50X4LX2MX0IUHQDO7MBKASKECCJAF23QH0200I6X350ECCJUHSKQDO7MBKAAFX6V4X1IX4GRX4L",
  "X2MX0I33Q8I030264X16X3Z7QZ63IX4GR060000J4X16X3Z7QZ63IX4GR50X4LX2MX0IUHQDO7MBKASKECCJAF",
  "19J0100J4X16X3Z7QZ63IX4GR50X4LX2MX0IUHQDO7MBKASKECCJAF19J0100J4X16X3Z7QZ63IX4GR50X4LX2",
  "MX0IUHQDO7MBKASKECCJAF19J0105040720A1V231212301dO2260022610fWgrgrWYrgrriWXgrgwtgrgsrwr",
  "grrkrgrjhWWXfpvmYrcliWYWWrgqWXgrgrgL0aWWWWXWWWWWWnWWWWWWWWWWWWWWWWWWWWWWWemWWWWWWWWWXW",
  "emWWWWmWWWWW00YWWWWWmWWWWWemWWWWWWWWWWWWWWWWWWWWWYaeWWWWWWWWWemaeWWWYeWWWWW00mWWeWWWeW",
  "WWWYWWWWWmWWWWaWXWWWXeamWWWWWWWaWWWWWWWWWW00Z/x////+l/////kl/////////////////////vtd//",
  "/ol////kltd///vl/////VaWWWWXmWWWWWnmWWWWWWWWWWWWWWWWWWWWWceuWWWjmWWWWnmeuWWWcmWWWWW000",
  "270349A75"]
@[expose] def ext_full_compact_vars : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_sift_q : armIsa.Hints := _decH #[
  "J470F045B3D090G273K02090B0D5F3704270F04300000000343507837FA303014435078DA39BD40361020F",
  "20XmzmdiZs00XWW00mYWWWWmW40mimZaXo00+lx/u/+l/JXmaWdWXmWC0000"]
@[expose] def ext_full_compact_sift_q : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_vmtf : armIsa.Hints := _decH #[
  "ZK251F1A1B190E3707270727072708070E1G37080G0E0I011I0H07045K3J080G2H3C02080K0J573H042H07",
  "04010I011827025K3J080G2H3C02080K0J573H042H07040I010E37353D2D042D2D0K27350D2D042D2D0K27",
  "350D2D042D2D0K27350D2D042D280D070E1G37353D2D042D280D0G08084909T000000016508FE943AACB06",
  "0000650E98F43AACB1860100650E98F43AACB1860100650E98F43AACB18601046E98FCB50AA430600016E9",
  "508F43CBAA0600006508FE943AACB1I601017XFI508FE943AACB0700007XFI508FE943AACB3H7D703018XF",
  "I508FE943AACBXLD38KJ803646E9508F43AACB1I601017E9508F43AACBYTI0700007E9508F43AACBYTI3H7",
  "D703018E9508F43AACBYTIZ5D38KJ8036435043E90300006E950438FCBAA18601006E950438FCBAA186010",
  "06E950438FCBAA18601018E950438FaD8CBAAaG71D8a01018E950438FaD8CBAAaG71D8a01018E950438FaD",
  "8CBAAb671D8a01018E950438FaD8CBAAb671D8a01018E950438FaD8CBAAbP71D8a01018E950438FaD8CBAA",
  "bP71D8a01018E950438FcC7aD8CBAA1D8G1018E950AA438FcC7aD8CB1D8X01038E950438Fd47d18CBAA1D8",
  "G1018E950AA438Fd47d18CB1D8X01000YrfgpqWacaddiWWmumdieieZsacaXxYZYZpsWWWidiXxWzmZWWWZXx",
  "WkudiWWWWuWXnnnmgK0aWWWWWWnWWWWWWWWWWWWWWWWWWWWWWWmWWWWWWeWWWWYWWWWWWYWWWWemXYWWWWWW00",
  "YWWmWeWemWYWeWWXWaWWWmYWWWeWaWaeaWmWWWaWXWXXXWaWWWXWWeYaeWnWWWWXW10XmWWYWZXaWeWeWXaWaW",
  "WoWYWWfWXWXmoWWWaZaWvWimXWWWXWvWceZaWWWWeWmmmmmW00//////ul+l/l/kl/v/l//y/t//+lx///d/t/",
  "tdp+/+d/p/z/zzy/t/n/y//dxtd+y////z/TdmXmWmWnmWcWmWWZWeWWXmaWWWuWeWeuiXWXuWiWYWYYZWeWkW",
  "ZWWuaeuXZWWWWYW20000"]
@[expose] def ext_full_compact_vmtf : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_sift_h : armIsa.Hints := _decH #[
  "L7C3J0D0A045B3K080G2D3H02080B0K3E570D0A045730369BC501732100669BC50438FFJ3DA7623017L769",
  "BC50438FFJ38BK74321020G80cuWkuWzmkuXR0aWWW00eWYWWYWWm00YeWceWimceWH0X//d/xZ/v/+lVuWayW",
  "cWXm00000"]
@[expose] def ext_full_compact_sift_h : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_heap : armIsa.Hints := _decH #[
  "XD3H181F010E3A1A2A1A2A1A2A190A0E1G3A190G1E03011C2I3J0703045A3D090G273K02090A0D3E5B0703",
  "045B01905507H98BF4305000055043BF987H195010055043BF987H195010055043BF987H19501050000001",
  "4507H98BF13401016XJC507H98BFXMI1B6X01007XJC507H98BFXMIXQJ373B7X03018Y0BXJC507H98BFXMIX",
  "QJ39AD8Y03200xWXxWZsXxWdiWYWpWWfoipauWL0eWWWWWWWmWWWWWmeWaeWWWWWWa00aWXWWeWWeWYWWaeaWY",
  "aWWWWWWo00fWWvWXoWvWYaWWWWWYWWWWWWW00Zt/y//il/d/v//tlp/xp/////+hVeWZWWpmWuWcWWemiWaiWW",
  "WWWXq00000"]
@[expose] def ext_full_compact_heap : List (SigEntry × Nat) := []

@[expose] def hint_full_compact : armIsa.Hints := _decH #[
  "P2301111P05031B1F17014A010A0A0A050A2A09380G152505195001300103246BP1Q201006J7HFFB46BPD3",
  "298602017J7HFFB46BPD3M819701008L9J7HFFB46BPD3M808000302001XR2301222100fYaWWWWuiWWubea1",
  "0mXWmWWeaWWWW00XeWaeWWaYWmWn40eaWmeWWW00X///yl/td//tx+/+zNZmWeuWWeaXWXY80013034"]
@[expose] def ext_full_compact : List (SigEntry × Nat) :=
  [(("full_compact_flush", [i64], [i64]), 576),
   (("full_compact_mark_live", [i64], []), 16),
   (("full_compact_record_ext", [i64, i64, i64], [.bool]), 0),
   (("full_compact_bins", [i64, i64, i64], []), 48),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_compact_arena", [i64, i64], [i64]), 256),
   (("full_compact_vars", [i64, i64, i64], []), 80),
   (("full_compact_vmtf", [i64, i64], []), 0),
   (("full_compact_heap", [i64, i64], []), 0),
   (("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 240)]

@[expose] def hints : List armIsa.Hints := [hint_full_compact_needed, hint_full_compact_flush,
    hint_full_compact_mark_live, hint_full_compact_assign_map, hint_full_compact_record_ext,
    hint_full_compact_bins, hint_full_compact_arena, hint_full_compact_vars,
    hint_full_compact_sift_q, hint_full_compact_vmtf, hint_full_compact_sift_h,
    hint_full_compact_heap, hint_full_compact]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 240)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Compact
