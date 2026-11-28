module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Forward

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X28)),
  (XRegOrSp.reg (XReg.X29)), (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X11))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.flag LeanQbe.T.Arm64.ArmCond.le),
  (.gpr (XRegOrSp.reg (XReg.X27))), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.flag LeanQbe.T.Arm64.ArmCond.gt),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.flag LeanQbe.T.Arm64.ArmCond.ge),
  (.gpr (XRegOrSp.reg (XReg.X28))), (.gpr (XRegOrSp.reg (XReg.X29))),
  (.flag LeanQbe.T.Arm64.ArmCond.lt), (.slot 0 .w64)]

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

@[expose] def hint_full_fwd_dedup_bins : armIsa.Hints := _decH #[
  "YN200011121324150505060637070807095A0B180C0C0915040D0504050C090525041C093E2909750E0F29",
  "2D050G3B140B5B140B5B140B5B140B2E0B0G193A140A2E0909050G1E0E7A0B0G193A090505050705061H09",
  "0H09N00150010057091B24ID31H501028M6D3B2T74IHH91702FJ802008B2T74IHHD370M6913FEJ803029X5",
  "BB2T74IHHD370M6912EJ90200DX5BB2T74IHHD370M691X0EX4AX8CX1J0DZW0004CX5BB2T74IHHD370M691X",
  "0EX4AX8C1JCZW0102CXPJX5BB2T74IHHD370M691X0EX4A0CYW00029X1JB2T74IHHD370M6912FE90202AYHF",
  "4IHHYIJT791M6B270D30A0000AD3B2YHFT74IHHYIJ91M6701EA0100AD3B2YHFT74IHHYIJ91M6701EA0100A",
  "D3B2YHFT74IHHYIJ91M6701EA0102BD3B2YHFT74IHHYIJ91M670YME0B0001BD3B2YHFT74IHHYIJ91M670YM",
  "E0B0001BD3B2YHFT74IHHYIJ91M670YME0B0001BD3B2YHFT74IHHYIJ91M670YME0B0003BD3B2YHFT74IHHY",
  "IJ91M670ZVE0B0002A7091B24ID3HHYIJT7YHFM60A0000A4IHHYIJT7YHF91M6B270D31AA0100A4IHHYIJT7",
  "YHF91M6B270D31AA0100A4IHHYIJT7YHF91M6B270D31AA010567091B24ID3HH060001020010uWYrgmWWXms",
  "WWibvmtcYyuhWWWdxWWvWXmWWWmYiWdWXr90aaaeWeXYWWWWWnWYWemWmWYWWeWXWWemWWemWeWYWnaaWWWWWW",
  "W00YYWWWaWnWWWWaemXWaeWeWXWWaWWmYaeWWaeWaaXWeoYaWfWWYW00XYWeWmWWYYWWmYWaaWmmYYWeeXXWWY",
  "vWWeWWmmWWWWaWZYWW00Xvv///p+y////pklz/td/l/z//t/+/vtl//tl/ttz/kxxt/j//x/VccWWWiXZWWWWi",
  "nmYWeuWmWYWWeWXWcemWWemWeeYWnaaeWoWWaW00006234506"]
@[expose] def ext_full_fwd_dedup_bins : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 128)]

@[expose] def hint_full_fwd_flush_large_m7 : armIsa.Hints := _decH #[
  "XD2K0K1L1B141606060J0J3A0A040A09470F140906062E2919060G16067E060G193E090606060A060C0906",
  "061E09B000000001450100004BB9L457K1C401015BB9L457KEC05000179L457KECQAJJBB17701007BBQA9L",
  "457KECJJ26E702017BBQA9L457KECJJ26E702028BB9L457KECQAXD7JJ08000089L457KECQAXD7JJBB1E801",
  "0089L457KECQAXD7JJBB1E8010089L457KECQAXD7JJBB1E801000eWWWZWWgrgWWWcWpWWyWb90YWeWXWaeWW",
  "WWYaWWWWeWWW00XWaWWmYaWWWWnYWXWYaWWe00aeXWYWWWeeWYeXWWieW00Xz/p/+lxp///+jx/b/xt//lVYWi",
  "WXmaiWWWXoaWwWaeWWm00000"]
@[expose] def ext_full_fwd_flush_large_m7 : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 48)]

@[expose] def hint_full_dense_bin_roundtrip_fid : armIsa.Hints := _decH #[
  "bD250508160816081E1J1M1L1I1N0N390606060O0O3B0B040A1P0B0Q094F0C140906060F0F091K080R1K0R",
  "0D090606063729290A3F0C140906060F0F09290A0G1A0A0AO60A0G191A0A0A36092415050503300E0E0305",
  "050G050B041D060A0D06060A0D1C0A0F0C0C0606370706040B0426050C0G2C0807050405080B0427061E0E",
  "0005050G050B041D060A0D06060A0D1C0A0F0C0C0606370706040B0426050C0G2C0807050405080B042706",
  "1H09N0000000384275OIKMGERNMLIJ31KA80300742S1IJ75GEOITK070003BX4OML75XEBIJ42OIKMGERNUA2",
  "1KB0200DOIXFQX4OKMGE75UAXEBRNXDPMLIJ42276Dm2201DOIXFQX4OKMGE75UAXEBRNXDPMLIJ42276Dm220",
  "8CML75XEBIJYI1YJKKMGEUA42OIRN16C0101CML75XEBIJYI1YJKKMGEUA42OIRN16C0104442OIS1IJ040000",
  "6S142IJ75GEOI16601006S142IJ75GEOI16601006S142IJ75GEOI1660104342OIS11H30101642OIS1aLHaT",
  "0aP306XG001742OIS1aLHaT0aP3aVE07ZG001A42OIS1aLHaT0aP3b03aVEb5Bb450AdG000A42OIS1aLHaT0a",
  "P3b03aVEb5Bb450AdG005E42OIS1aLHaT0aP3bT6bIAb03bR7aVEbJFb5Bb450EXvG005442OIS1aLH0400016",
  "42OIS1aLHaT0cOE06XG001942OIS1aLHcP0cOEcT5aT0cUB09bG000942OIS1aLHcP0cOEcT5aT0cUB09bG005",
  "D42OIS1aLHdM6dBAcP0dK7cOEdCFaT0cUBcT50DXk00030202142301L22100cWWWWuWZWXuWWWWWWWWZWWWWi",
  "WXmWyWWWWWWWkWXeXuWWdlk+zzuWWXWWfmWZmWWmXWWfmYWyWWrgnY10mWWnWmaYWWeWWWWWXWWWWWemeYXWWa",
  "WWWWWWmWWWWWWmWYaWWWWWWWWWWeWWWYWWfaaeeWWWWWWWmWWWW00eWWemeYXWWamWWYWmnYWWWaeaXWmWYeWW",
  "XWeenWWWeWeWXYWWWWWWWXWeaWmWnWWaoYaaWmXWaWWeWWae80YaWWWemXYaumWWWWXWWXYWWWaeWnYieWWWWW",
  "mceWWWvWXZbcgiqvWWWWaWmWXoWWWWWaWmWWieWWWWW00d/d//c/lxy//ol//x++zx///pltz+l/vd//z/lkz/",
  "//l/d/zv///////z/lno/+z//sxxtno/z/t//l//tlFuWWvWmaZWWjmWWaXXYaWWWimeYXmWcuWWYWmnYWWWmW",
  "uWYcWWWWWWWYWmkjWXYWWfaaekjWYWeWWmWWemG0016234506"]
@[expose] def ext_full_dense_bin_roundtrip_fid : List (SigEntry × Nat) :=
  [(("full_fwd_flush_large_m7", [i64], []), 64),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_sweep_bins_m6cf", [i64], []), 96)]

@[expose] def hint_full_fwd_reconnect_irred_m7 : armIsa.Hints := _decH #[
  "Z92S11960425080T0T0B3H000E00050D2F3707050D1406192704050906060606061U180G1E25250V46260V",
  "05090B05050H050T0I460605050G050E041D0A0B0D0A0A0B0D1C0F070C0C0B0B3A0A0B040E0G5E0503090C",
  "0G2C083C080A050G05080E0G5A0B03091309060DG000000003816S4226A302028816S42UHPTQBV0LA168Z8",
  "113AX0EK6816SLAPTUHQB42V015As0100A816S42UHPTQBV0LAXH5K60AZ80024XVU816S420400027XVU816S",
  "42UHPTQB07YG0007XVU816S42V0UHPT07XG0009XVU816S42UHPTQBY4EV0159gG1038XVU816S42YTIV0YSTU",
  "H138bG1009XVU816S42YTIV0YSTUHYU309bG0004XVU816S42040001AXVU816S42YTIV0YSTUHYU3Z260ArG0",
  "02DXVU816S42YTIV0YSTUHYU3Z36Z26Z8EZ750DXrG000DXVU816S42YTIV0YSTUHYU3Z36Z26Z8EZ750DXrG0",
  "07HXVU816S42YTIV0YSTUHYU3a0BZLFZ36ZUAZM7Z26Z8EZ750HsbG001020210ZsWWWWkZWWWzmWyWWWWWWWZ",
  "mWWWjucwWmWWcWaZsWkWWl/A0aXWWmWWnWmYWmeeWWaWWWWWWaYWWWWWmWWWWoWWXWmWWWWWYWWW00YWmWeWWe",
  "meXWeaaWWYeWWWeYYXYWWWWfWWmWfWWWmefWWmWXXWW00XoaWWWcXYWWinYieWWWWWXXmaWWauYeWWXWYWWfoW",
  "ceWWW00Xx+l/d//c/lz/lpp//vd///lxxzx////b/+//j/y+/liZsl/zz//VaXmWuWWvWmYWmiiWWcuWWWmaaY",
  "aWWWWwWXWWoWZXWmpyfmWYYWW00009234506789"]
@[expose] def ext_full_fwd_reconnect_irred_m7 : List (SigEntry × Nat) :=
  [(("full_fwd_flush_large_m7", [i64], []), 64),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_fwd_scan_lit_m7 : armIsa.Hints := _decH #[
  "YB6N1F1M171Q0A05050505053K0K080D0L0D2714070C07292J140J07070C0G1G0K093C07140X0270J08070",
  "P0P05143O0D0P04552C081C0X1052C0409080917092809080C0C25040C0425040919A001C00101AO5CF7A8",
  "B6EAN56IQEMTK1CAYK101BO5CF7A8B6EAN56IQEMTKX0L27CBYK20400000009CF7A8B6EAN56IQXPKEM1J9XA",
  "1009CF7A8B6EAN56IQXPKEM1J9XA106AY6JCF7A8B6EAN56IQXPKEM25LAYK200CY6JCF7A8B6EAN56IQXPKEM",
  "YJPYHO2L7CYYK201DY6JCF7A8B6EAN56IQXPKEMYJPYHOYM71LDYYK109AXV7CF7A8B6EAN56IQXPKEM0AYK00",
  "00iWuWWWWWWcXXtWZoWcYiWWWsWbmWkWgL0XYWXWXWXWmeaWeeWWWWWWWWWWWWmWaWWWW00nXWoWWWqebYmaaW",
  "YeaXWqWfXWWeWYgWWW00aWeWWWWWWYWWZWXmeYWaWWaYXWmWcbW00Z+zz+h//ktdrw/tt/xltz+t/jyn/ilxh/",
  "//VXYYXqWWneugbWeeWameYXeWoZkWpmaqWWW00000"]
@[expose] def ext_full_fwd_scan_lit_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_fwd_check_cl_m7 : armIsa.Hints := _decH #[
  "f83S101U1X21I0H02020X333140DA406250V0X4060G6E2A0V080E0X40605090X31505030518075A04756B0",
  "9070A0E0914184E14080E1Q0F0M050P0E0A0A0A0A0A3C0C080D050D2B140B0J0B292J140J0B0B070G1G0C0",
  "93B07140X02B0A080B0O0O07143K0D0O045B2J081J0X10B2J0409080917092809080B0B2A040B042A04091",
  "918040E0M0C0K050O0E0A0A0A0A0A3P0P080D050D2E140E0B0E292714070E0E0B0G1G0P192E0B140X02E0L",
  "080E0J0J05143E0D0J045A2F081F0X10A2F04081B0928080B18040N09240G5E2E4E2E4E2E4E2A0E0G195B2",
  "A090X3150503051505180505046A04351E091X00808080G66065E065E065E0A060G19660A09180X34X30X3",
  "001I18080X3450503051315360D06082602160X00505080X315050305062315360D06082602160X0050508",
  "0X315050305XB001500102841I2DX27S5HBU90FI2X338G210441X43I2X3X3048000AX43DX290I241X3X35H",
  "7SFIBU16AZ0100A41X43I2X3X3DX27S5HBU90FI265AY8215441X43I2X3X3048000AFII241X43X3X37S5HBU",
  "DX2901TAYG101BY56X4341I2X3X35H7S90FIBUDX21TBXG110BY56X43DX290I241X3X35H7SFIBU3E7ABc036",
  "2A41X43I2X3X35H90FI7SBUDX2265AO200CZ3TY5641X43I2X3X35H90FI7SBUDX21NCZ1101DY5641X43I2X3",
  "X35H90FI7SBUDX2Z3TZ5N1EDYXG111DY5641X43I2X3X35H90FI7SBUDX2Z3TZ5N1EDYXG112EY5641X43I2X3",
  "X35H90FI7SBUDX2Z3TZ5NZGE1BEgXG101KY5641X43I2X3X35H90FI7SBUDX2Z3TZ5NZGEZRAZIFZHQZLPZJMa",
  "0C17KgXG101LY5641X43I2X3X35H90FI7SBUDX2Z3TZ5NZGEZRAZIFZHQZLPZJMa0Ca352B7LgXG204JY5641X",
  "43I2X3X35H90FI7SBUDX2Z3TZ5NZGEZIFZHQZLPaSCZJM1AJgXG100JY5641X43I2X3X35H90FI7SBUDX2Z3TZ",
  "5NZGEZIFZHQZLPaSCZJM1AJgXG106KY5641X43I2X3X35H90FI7SBUDX2Z3TZ5NZGEb9AZIFZHQZLPaSCZJM2B",
  "LKgXG200Mb9AY56X4341I2X3X35HZGEZIFZHQZLPaSCZJMbMObKK90FI7SZ3TZ5NBUDX22L7Memd0201Nb9AY5",
  "6X4341I2X3X35HZGEZIFZHQZLPaSCZJMbMObKK90FI7SZ3TZ5NBUDX2bP71LNemd0109Kb27Y5641X43I2X3X3",
  "5H90FI7SBUDX2Z3TZ5NZGEZIFZHQZLPaSCZJM0KqZ0007DY5641X43I2X3X35H90FI7SBUDX2Z3TZ5N1BDYXG1",
  "01JY5641X43I2X3X35H90FI7SBUDX2Z3TZ5NdIAd8MdCOd9CdAKdNP1BJYXG101KY5641X43I2X3X35H90FI7S",
  "BUDX2Z3TZ5NdIAd8MdCOd9CdAKdNPdQ52EBKYXG204IY56X4341I2X3X35HZ3TZ5Nd8MdCOeJP90FI7Sd9CdAK",
  "BUDX21LIZG106JY5641X43I2X3X35H90FI7SBUDX2Z3TZ5Nf0Ld8MdCOeJPd9CdAK257JYXG200Lf0LY56X434",
  "1I2X3X35HZ3TZ5Nd8MdCOeJPd9CdAKfDJfBE90FI7SBUDX227BLXWd0201Mf0LY56X4341I2X3X35HZ3TZ5Nd8",
  "MdCOeJPd9CdAKfDJfBE90FI7SBUDX2fGB17MXWd0109C41X43I2X3X3gF65HgG590FI7SBUDX21ACX8100C41X",
  "43I2X3X3gF65HgG590FI7SBUDX21ACX8100C41X43I2X3X3gF65HgG590FI7SBUDX21ACX8109A41X43I2X3X3",
  "FI7S5HBUDX29015AY8100BFIiBTI241X43X3X37S5HBUDX2902E5Bb0201CFIiBTI241X43X3X37S5HBUDX290",
  "iGE15Cb0106BiV541I2DX27S5HBU90FIX3X3X430Bn0000BiV5BU7S5HI2X3X3X43FI41DX2901ABX8100BiV5",
  "BU7S5HI2X3X3X43FI41DX2901ABX8100BiV5BU7S5HI2X3X3X43FI41DX2901ABX8107241l831520100241lD",
  "5020004241m531520100241mA50200010405A0610aYWWXmWwmWmWWZWXrWtWXWdmeWlmWZyln+duWWWdXyWWa",
  "YWXtmWXtplc+jyWWWWWWWWWiYZkWdaWiauWWXiWhWWyWWWWWWuXmWWWWWXmejuWymXmpWWWbmXiWZmWWWZuWWd",
  "s+X+WXWWWxuWcX/uhmgL0maeWaWWWXWemWWWWWWWWWeWYaWWWWWWWWWeWeWWWWWWmWWnWWWWWWWWWWYWWWWmYW",
  "mmWWWWWWWYWWWXWWeWWWWWYaWYWWWeaYXWYYWWWWWWWWWWWWaWXWWWWWoWWWmWWWWWeWWmWWWWWeWWWWW00YaW",
  "WWWWWWaeWWWXeWWWmaWXYWWWWWWWrgaWaWeaWWWeWWemWWWWWWWeeXbWWaefWeeWameYXeXYYWWmWaqWWWgXYY",
  "XaWWbYXeqXXWWoXWebWYeeWYWWomWWWfWYaeWWWaWaWWeYWWemaWYmWW00mWWWmWWWaWWWXWWWaZWWWZmWWYmX",
  "WsYuhXeWWWZWyWWWmWWpmWepvdolayWWWWWWWWWaWWcWZWmaWeWWeaYXWWigWWWWWeWmWWWWWWmWWuWiYWmXWW",
  "XWmeaWXneWWXuWWZmkW+WeWWWfuWYWhWXoW00///tl/xt////k//tl///yl//+/p/zv//////+mZp/t/lt///d",
  "//kl///////dlyn/ztdj/ll/s/lxzlzxvZ+u/st///Zzxxyt/xrvzktzz/+xz/lr/xlalxZ+w////j/xta///t",
  "/t//bh//e/t/w///VemWaeWWWWnWWemWWWZmWWXWiWYcWWWWWWXlyiWeWmeWWWuWWnmWWWWWWWumZkWYeuoWmm",
  "WfWmaYmYacyXdWfeWWWyYaaZeWagcYneYYWXaYWmgWamxmayXbWWWWoWaexWWWeWeWWwqWWtWeWbWWW0000B23",
  "4506789BC"]
@[expose] def ext_full_fwd_check_cl_m7 : List (SigEntry × Nat) :=
  [(("full_unwatch_large", [i64, i32, i32], []), 0),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 192),
   (("full_dense_prop_unit_m7", [i64, i32], [.bool]), 208),
   (("full_add_unit", [i64, i32], [.bool]), 128)]

@[expose] def hint_full_fwd_connect_subsumer_m7 : armIsa.Hints := _decH #[
  "aR3B2Q0A0M0M063E140D3P0M7L0B3B14070L0B0B0B0B0B3C0C0D0J0C0D2714070B0B292F140F0B0B070G17",
  "090P0O2K0928060P0B0B0B0B0B3C0C0D0J0C0D2614060B0B292F140F0B0B070G1L6607060B0B0B0B0B3C0C",
  "0D0J0C0D2714070B0B292F140F0B0B070G17090O0L0K092D0E0O16060G161F041D0B070D1B0B070D1L0C07",
  "0L0L0B0B3J0J0B040F0G5E060L0G2L083L080J160G06080F0G5J0BI00000002445QM5AIE2PO4C210545AQQ",
  "MIE5A3POK5O310645AQQMIE5AUK2PO6O211945AQQMIE5AUKTOX2LSP179iO101B45AQQMIE5AUKTOX2LSPXNJ",
  "XOC2B7BiO2043455AIE2OL362115YOP45QM5AIE175P1017YOP45QM5AIEZ8JZ9C2B77P203445QM5AIE3OLK4",
  "C330845QM5AIEa4Ka3La86a2O178dC101A45QM5AIEa4Ka3La86a2OaMJaNC2B7AdC204000000114X5010001",
  "445bLObOE5A04E002745bPO5AbOEbV6bLOc1F07XE000745bPO5AbOEbV6bLOc1F07XE006B45cQBcFCbPOcOJ",
  "5AcG7bOEbLOc1FbV60BjO008020DAcO2301020A1H2301020A1YJ2301020A1622100fWWzmWWmXuiWXxWXuWW",
  "XWWWgYWWWWYuWsWZmXuWXiWhWXuWWWWWbmXiWdWWtdfuhmD0XWaeWWWYWWmWWWWWWXWWeWWWnWWWWaWXWWWYWW",
  "WWWW00YaYWaXWmWWamWWWmYYXWmYaWaWXWWemWWWYWWmWaeWWemWeWYWWnWWXWWWYmW00inWWWWuaeWvYaumWW",
  "WWWWeWWWWmeaYWXneuWeaYXWWuqWWWXWmeaWZYmZpWuXo00/////vtx/tz+l//ol//+/xxz+/xolodzn/k////",
  "vZ+u/tl//ki/alxZ+z//z///w//VceaWeYXmWWjmWWXWaaYXWajmjuYkWnWWWWcyXdWemWWnpWxmayXYWWYWWW",
  "bWW00010"]
@[expose] def ext_full_fwd_connect_subsumer_m7 : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_fwd_collect_sort_m7 : armIsa.Hints := _decH #[
  "aA271L1K1A12022E0435050N3C0M0F0M060D2Q3J0J060D1406192J0406090E060606061Q180G140N1J5F2E",
  "0V080F3E140E0B16090N05050C051D0G092P1E0D1G160G1E16067B060G1D3B0D020C0G1B1F0B4F0D3J0J3F",
  "5F0D3J0J3F5F0D3J0J3F5B0D3F0F060B0G193B5B0D3F0F06094F0B060D3J460D3B0B092B0B0F090G1E1E0B",
  "4B4B4E060E0G194E0609X104CAF2674O1P4010064O67AK8LCAF23EPQ60301BLP4O67CAF2TCO5AK8LUMPN16",
  "BXn0113DVFKEO5PNLPTC4O67AK8LCAF2UM16DaX8100DLP4O67CAF2TCO5AK8LUMPNXG6KE0DXn00027XUQ4O6",
  "7AK8LCAF21P70102BLPXUQ4O67CAF2TCO5AK8LUM1NBXY2111BLPXUQ4O67AK8LCAF2TCO5Y5N0BXe0000AXUQ",
  "4O67AK8LCAF2LPUMTC1BAu0100DLPXUQ4O67CAF2TCO5Y5NAK8LY6JUM2B6Dag0201ELPXUQ4O67TCO5Y5NAK8",
  "LY6JUMCAF2Y861BEXYG1061ZDP0100025ZJE67CAZDPF20500005ZDPCAF2ZJE671B501005ZDPCAF2ZJE671B",
  "501005ZDPCAF2ZJE671B501035ZJEa9CZDP67CA0500005ZJE67a9CCAZDP16501005ZJE67a9CCAZDP165010",
  "05ZJE67a9CCAZDP16501017ZJE67a9CCAZDPaB6aFB0700017ZJE67a9CCAZDPaB6aFB0700017ZJE67a9CCAZ",
  "DPaB6aFB0700016ZJE67a9CCAZDPaB60600036ZJE67a9CCAZDPcG60600025ZJEa9CZDP67CA0500005ZJEa9",
  "CZDP67CA26B502013ZDPCAa9C0300005ZJEa9CZDP67CA1F501006ZJEa9CZDP67CAdAF0600033ZDPCAa9C16",
  "301003ZDPCAa9C16301003ZDPCAa9C1630101020E10dWWdpvyeWWcXuliWcWXulhWWXulhmydrukZwydXyeWW",
  "uWYrgmeeWZWWWWWbuXtWYWmWWcWaZsWkWcgL0aWaeWWWWWXWWmYWWeWaWYWWaeWYWWWXWWWWmWWWeWWWeXYWWW",
  "WYYaWfaWWmWXWWWeoWWXWmWWWWWWWW00YWYaWWWWWemWeXWWaWYWXWWYaWXWWWWmWWWeWWWaWWeaWnWWWWXXYW",
  "aoWWeWWqWWafWWWmefWWmWWmW00YXmuiWWWoWudaWYWWudWWYWudXmiZmucXuiZWyWYWeWmWWYWWWXWWaWWmyW",
  "pWWWWXWYWWfoWceWW00Xv/xp/////kl/lz//p/v/z//xp/z///+////l///t//lp+y////zzx/sx//cl+t//tj",
  "/y+/liZsl/+//VcWaiWWWWWnmWmYWWiWcWYWWaiWYWWWXWWWWmWWWeWWmiXZWWWWYYaWfaWWvmXeWWeoWZXWmp",
  "yfmWXWW000012"]
@[expose] def ext_full_fwd_collect_sort_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_forward_sub_m7 : armIsa.Hints := _decH #[
  "bF2820153E0D0E0826031E0X00505081H181U13490405080508210T1508000508003518000008050805081",
  "61A040G3B0B3B0B3B0B3B0B0E0B0G1935050E091E042B0B0F3C050J050L0D2K3505050D140E192L0405090",
  "E0E0E0E0E1J1405180G35053E0E05092B0B05092E0E0B040G470707092F0F07370707092F0F07370707092",
  "F0F07370707092F0F0E070G194707070925050E090E0D0504050D150X01005260D06082603160X00505080",
  "50405150405T001500102242510200003429051153010034251E5030005542X43X2UVIUH206502005UH42X",
  "43VIX700500082UH420200035Y86YAAX4342UH0500005UH42YAAY86X431E501005UH42YAAY86X431E50100",
  "5UH42YAAY86X431E501055Y86YAA42X43UH2E7502019Y86YAA42X43UHZOCZJBZH7ZKF1E9f0113BZQJZGEZO",
  "CZJBY86YAAX43ZH7ZKF42UH15Be4100BY86YAA42X43UHZOCZJBZH7ZKFaB5ZGE0Bf00026aPJY86YAAX4342U",
  "H0600037aPJ42X43UHY86YAAb9E07Y10028Y86YAAbMBaPJ42X43UHZOC1E8a01008Y86YAAbMBaPJ42X43UHZ",
  "OC1E8a01008Y86YAAbMBaPJ42X43UHZOC1E8a01029Y86YAAbMBaPJ42X43UHZOCbPE09a00019Y86YAAbMBaP",
  "J42X43UHZOCbPE09a00019Y86YAAbMBaPJ42X43UHZOCbPE09a00019Y86YAAbMBaPJ42X43UHZOCbPE09a000",
  "39Y86YAAbMBaPJ42X43UHZOCdEE09a0004142010002142010000242e601520100242e950200020406A021X",
  "720010mWWWcWYeYWWWWiXuWWiXucWyZWkXmdWWcWcWyyYXWWWiWediWyWeWuWWykdZWYmWWXkWWXmWWjeaWWZW",
  "Xr00YWnWWmmXXWXWXYWXWWWmWWeWWaWWmWmWmWXWaWWYXWWWWWWWXWXYWWWWWWmaemWWWWmaeoWWWWXWemW80m",
  "WWemWeemmmWmWnWWmWWeWWaWWYWYeWeWeWWqYWWXWmoWXWWXWmWnWWWWWYeYaeYWaaWYafWXWeWWaeW10YWWWW",
  "WWWWaWuWmaWyYWkXWdWmZWWYWYWiiWWWYWaWWpaWimWWeWmicZXWWWWWWcWWWmWWWWWWWXWWW00Zx++z//k//Z",
  "k++l+/+y/+///l//t//x/vl/l/l/+tx/vz++udi//z+l+y/////vlxtlx/tt/xtj/z/k//tl/TaXXYWWnWWynX",
  "XmXWXZWXWWWmWWeWWaWcmWmWmWXeaWcYXXdupWWYXmXZWWWWWcmaemaWeeWaeoWYWnWWemW2000823450678"]
@[expose] def ext_full_forward_sub_m7 : List (SigEntry × Nat) :=
  [(("full_fwd_dedup_bins", [i64], [.bool]), 192),
   (("full_dense_prop_unit_m7", [i64, i32], [.bool]), 208),
   (("full_fwd_collect_sort_m7", [i64], [i64]), 16),
   (("full_fwd_flush_large_m7", [i64], []), 64),
   (("full_fwd_check_cl_m7", [i64, i32], [.bool]), 304),
   (("full_fwd_connect_subsumer_m7", [i64, i32], []), 160),
   (("full_fwd_reconnect_irred_m7", [i64], []), 224)]

@[expose] def hints : List armIsa.Hints := [hint_full_fwd_dedup_bins,
    hint_full_fwd_flush_large_m7, hint_full_dense_bin_roundtrip_fid,
    hint_full_fwd_reconnect_irred_m7, hint_full_fwd_scan_lit_m7, hint_full_fwd_check_cl_m7,
    hint_full_fwd_connect_subsumer_m7, hint_full_fwd_collect_sort_m7, hint_full_forward_sub_m7]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 128),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_sweep_bins_m6cf", [i64], []), 96),
   (("full_unwatch_large", [i64, i32, i32], []), 0),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 192),
   (("full_dense_prop_unit_m7", [i64, i32], [.bool]), 208)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Forward
