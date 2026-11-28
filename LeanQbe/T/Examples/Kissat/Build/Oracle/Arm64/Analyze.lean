module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Analyze

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X20)),
  (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X23)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X27))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.flag LeanQbe.T.Arm64.ArmCond.le), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X14))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.flag LeanQbe.T.Arm64.ArmCond.lt),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X27))), (.slot 0 .w64)]

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

@[expose] def hint_full_ana_failed_lit_m6_hdr : armIsa.Hints := _decH #[
  "fC20110203111104050406171819210A210211021B1C1D1E1F21032101041G0H3I0I040H010J0J02510301",
  "01062G021G030G0H0K21010K140H000G0J010201010H110L34040H11040M212403030104010604062G021G",
  "030G2101310211030121010K31730J2G04040611022303010H2N3431031201040J0H3O0M0O040H010P0P51",
  "02030101062I021I030I0H0K21010K140H010301010624021403040H0K21010K530K200G0J010201010H11",
  "0L34040H11040M162Q100G0J010234040H11040M7231240R0304040J0L0J000L0J10020O0B0C0K0I00054J",
  "120J020J0J03220J0J4J0J0J0J2J0421010G0H010311031103140214020414021G1J03040J03040G0J0J03",
  "0J0G040G0L04000L0J04030J040G100H0B0C01020J040111011101100G0J010201010H110L34040H11040M",
  "X4001S00106B4SK7X9DG560XDFX5BM8XBEO9X7C2K4B8203D4SK7X9DG560XDFX5BM8XBEO9X7CY3JXTI2K4Da",
  "W8203E4SK7X9DG560XDFX5BM8XBEO9X7CY3JXTIY641KEaW81044Z10Z3JZ2G4S11401014Z10Z3JZ2G4S0400",
  "025Z10Z3JZ2G4SZC1050006D4SK7X9DG560XDFX5BM8XBEO9X7CZV4a241KDcW810454SK7X9DG5602NT58200",
  "14S01000054SK7X9DG5601N58100B4SK7X9DG560X5BX7CXDFM8XBEO95KNQ1UB8501F4SK7X9DG560b5QX5BX",
  "7Cb3KXDFM8XBEO9b4Nb7U2VGF8220F4SK7X9DG560b5QX5BX7Cb3KXDFM8XBEO9b4Nb7U11F8104F4SK7X9DG5",
  "60b5QbKVX5BX7Cb3KXDFM8bLGXBEO93NUTFaW8303EbTN4SK7X9DG560bKVbUUXDFX5BM8XBEO9X7C3K4TEG30",
  "0E4SbTNbKVbUUK7X9DG560X5BX7CXDFM8XBEO92KTEY0204JbTNbVT4SK7X9DG560b5QbKVbUUXDFX5BM8XBEO",
  "9X7CbLGcMPcFO2K4JgWX0200KbTNbVT4SK7X9DG560b5QbKVbUUXDFX5BM8XBEO9X7CbLGcMPcFOcO41KKgWX0",
  "10G4eH0eJJeIG4S11401014eH0eJJeIG4S0400025eH0eJJeIG4SeS105000344SK7X9DfAQ0400007fC0fEJf",
  "DGfAQ4SK7X9D11701018fC0fEJfDGfAQ4SK7X9DfH108000214S01000044SK7X9DfAQ1G4010254SK7X9DfAQ",
  "g3G050004D4SK7X9DfAQg3Gg61gQKgRIgD4gS0gPCgOBgNO0Df0002C4SK7X9DfAQg3Gg61gQKgRIgD4gS0gPC",
  "gOB0Cf000214S01000114S01000324Si710200024jV0k1Jk0G4S11401014jV0k1Jk0G4S0400025jV0k1Jk0",
  "G4SkA1050007jI230002200O23009220002200b82300122000aZWYWWXYYWWWYWWWWYnWaenWWWZZWgucWWYx",
  "WWeWWZid+WXWuWauWYXmXWWWWWWWiWYZWWWWZWWmuWdWWkWeycWWWmiWqWZWeiZWeiWWjmWYXmXWWWWXmWeiWy",
  "WWyeurgqeuwqXe50eXWYWmWWWWWWWWWWWWWWWWWWWaWWWWWWWmaeWWWWWYWWWWYWeWWWaaWmXWeWWWWWWWWmmW",
  "WaWWWaaWXWWWWWWWWnWWWWWWWWWWWWWWWWWWWaWmXWeWWmWWYYWWWWWWWWWWWWWWWWW00aWmXWeaWWWWWWWWWW",
  "WWaWnYaaYWWWWWWWeYaWWXXYXeWeWXWaWmWYYWeWmaYWWYWWWeeeemYWWYYYYamWnWmoWWeqYaWmWWWXXWWXXX",
  "abWWYWeWmaYWeWXXXXYWeeXWYWWXYYWXWYG0XWWWWWWWWWWWWWWmWWWWWWWWWXWWWWWWWWfWWWWeWaWWWWWeWW",
  "eWWWmWWWWWWWWaWWXWWWWXWWWeWZcicWWkYWWWXaWWWXWWaXWWaWWWWWWWmWWWWWWmWWaWiZciWWWWWWWeWWW0",
  "0l/n+/z/lt////+WlWoXolt+zxttv//////llxt//zzxzl/l/ylt+//xu/l+/tx//x///lllklv//xxxxo/+j+",
  "cx//ktxt+////zz//zzydn//u/l+/tx/d/zzzzx/lWylx//zxx/z/wVkXWYWmeWWWWX/m/j+jmeXYaeecWWWWW",
  "WmmaeWWYYaYmWmWZmeXWWadWmXWeaWWaWWWmmmnmcWWaaaajWXoXvaWWneaeXWWWWYYWWYYZukWWdWmXWeaWuW",
  "YYYYaWm/ZmaWWYaaWYWb0001812345678"]
@[expose] def ext_full_ana_failed_lit_m6_hdr : List (SigEntry × Nat) :=
  [(("full_bump_analyzed_mode_fid", [i64, .bool], []), 160),
   (("full_backtrack_ac_fid", [i64, i64], []), 96),
   (("full_ema_update", [i64, i64], []), 64)]

@[expose] def hint_full_restore_bump_ana_mode_fid : armIsa.Hints := _decH #[
  "XJ34021B1I0M0I101C151O0244040H1K032J1G0H2I0L024404040H2K021K030H2G1J0H22000G0J01020101",
  "0H110L34040H11040MB000000017ICG0ABMOK54S511J701008ICG0AB4SEIMOK5512JG802019ICG0AB4SEIM",
  "OK551PG1J9010324S511G201018ICG0ABMOK54S51XAI2GJ802019ICG0ABMOK54S51XAIXEJ1G90105000000",
  "14Y60Y8JY7G4S11401014Y60Y8JY7G4S0400025Y60Y8JY7G4SYH1050002YS2300022000aZWYWWWaWiWeiXm",
  "XWZWmiYrYH0eXWYWmWXWmWoYXWWeaWaaWWWW00aWmXWeaWmeWfXWmXaYWYYWeWW40XWWWWWWWaWWaWmWWXWWaW",
  "WW00/n+/z/lt+/d/jz+/ztv/xx/l/lNkXWYWmeXWuWoYXWYecWaaWmWm80010"]
@[expose] def ext_full_restore_bump_ana_mode_fid : List (SigEntry × Nat) :=
  [(("full_bump_analyzed_mode_fid", [i64, .bool], []), 160)]

@[expose] def hint_full_analyze_reasons_fid : armIsa.Hints := _decH #[
  "aT2S021D1J0M0J1V1U19171X01E024S0S0H1G0324110H2G0L024S0S0S0H240214030H2F110H230S0S020S0",
  "102010S0S020S0S0S031S02013S31020M131M0J0K0M0K3H010L2S0S0S0H2S12120S0S0S0H240214030H012",
  "S0S020S010406300L00010601010S0B0B140L3S0S0S0H2G021G030H042S0S010H0C0S0M0S0S020S01010S0",
  "S0M112S0S0H1S0M0S0S02010S0M040S010S020S0S0H1S0L31010H1S010MR000000018HUFV9DL7J94QNX0PE",
  "14801009HUFV9D4QDJL7J9NX0PE24190201AHUFV9D4QDJL7J9NX0PES114A01038FV9DHU4QNX0J9L7PE1F80",
  "1019HUFV9DL7J94QXDGNX0PE2F190201AHUFV9DL7J94QXDGNX0PEXH11FA01064FV9DHU4Q0400009NX09DJ9",
  "4QHUFVL7PEY6F0900009FV9DHU4QNX0J9L7PEY6F0900029NX09DJ94QHUFVL7PEY6F0900009NX09DJ94QHUF",
  "VL7PEY6F090006BNX09DJ9Z9J4QZCKHUFVL7PEY6F1CB01006FV9DHU4QY6FZ9J060002D4QHUFV9DL7NX0J9Y",
  "6FZ9JZCKZFCZH1PE1SD0101CNX09DJ9Z9J4QZCKHUFVL7PEY6FZFC0C0000D4QHUFV9DL7NX0J9Z9JZCKZFCPE",
  "Y6FZSS0D000AE4QHUFV9DL7b2BNX0J9Z9JZCKZFCaP0Y6FPE11EYW0101F4QHUFV9DL7b2BNX0J9Z9JZCKZFCa",
  "P0Y6FPEb310FYW00064FV9DHU4Q0400014FV9DHU4Q0400005FV9DHU4QY6F1S501015FV9DHU4QY6F0500024",
  "FV9DHU4Q0400014FV9DHU4Q1S401014FV9DHU4Q0400025FV9DHU4Qd3S05000302010aB2300020900aZWaWW",
  "WWWWmiWWWWWWXmWmuZmWWWkWWZWXXmWmiXmXmWWWdkaWWWWWYWcWacWuWmXmecXgrYH0eXWaXXWWXWmaWWWWmW",
  "eWXaaYWaWYYWmeWYeeaYaXWaeWWWWWWWWeXWeWeWfXWmWaYWYYWWWWW00aWmYWmmWWmeYWYWWemaWWoYXWYWXX",
  "WeaWXaaYXYWmYaWWoYmWXWaWmaeaWammeWoXWXXWaWWW40XWWWWaWWWWaWWWWWWWmWWeXmcWucWWXWWWmWWaWm",
  "WWWWWZcWmWWWWWWYWWYWeWWWmWYWWWW00ln+/x++/p+/lx/x//k/p/+xxz/x/yz/Zt/zttxzx+/xtt+xw/+z/t",
  "+/tlp/s+/l+xy/zz/t//lNkXWaXXWiXWmaWaWWnWiWXaaYWaWZYWyeWYeeaYaXWaeeXabWXYWeXWemiWfXWmXa",
  "ZWYYWeWWm8001912345678A"]
@[expose] def ext_full_analyze_reasons_fid : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_div", [i64, i64], [i64]), 0)]

@[expose] def hint_full_analyze_core_m6 : armIsa.Hints := _decH #[
  "a8291F1S17073E0V6U021D1303030S031303030S030S031S0311021102011102141G03010G0301040G0G03",
  "0G0401040L010J0L0G01030G01041J0H000B0S020G010S000L5G0G3G020J010S040M1S031S031S0203101G",
  "0J0S020S0S0H110L34040H11040M0S030S0S0S020S010M0S02010S0M010103010S010S020S03030S010M01",
  "0L3S1S0H1S030S0SG001S0010084Q8FAX1HED7IVPU691D8010834Q698F03000444Q698FXCS04000214Q1D1",
  "010044QYT0698F31S44030224QZGD0200011ZJD0100022ZJD4Q0200015ZR0ZUJZTGZJD4Q11501015ZR0ZUJ",
  "ZTGZJD4Q0500026ZR0ZUJZTGZJD4Qa710600029SD4Q8FAX1HED7IVPU690900019SD4QIVPUHED78FAX16909",
  "00019SD4QIVPUHED78FAX1690900019SD4Q8FAX1HED7IVPU6909000402010L2300ZS2020ZF22900ekWWWWW",
  "WWWWWWWaZWYWWgWYWWWWyuWWWWmWWWWqeXYaWWWWWW/poL0YWYWWWnXWWWWWmaXWeXWYWmWWammaaWWWWWWWWW",
  "WWWWWeWWYaWWWWWWW00XWXWWWemqaWWWeYWmaWmXWeaWYeeYYWWWmWWWWWWWWXWaenXYqoqYWWW00caWWWWaWW",
  "WWWWWXWWWWWWWWWWakeWWWWWWWaWWWWWWWWWWWWWWW00lz/z///c+dt+ptlx+/n+/z/lt/xllxvZ/+//mZuami",
  "pz/tkzzucudx///VYWYWWWvXueXiemaXWkXWYWmeWammacyWXWWlydxlpiYWenYYdvduaWWW0001812345678"]
@[expose] def ext_full_analyze_core_m6 : List (SigEntry × Nat) :=
  [(("full_one_lit_confl", [i64], [i64]), 272),
   (("full_deduce_1uip_m6_hdr", [i64], [i64]), 400),
   (("full_min_shrink_m6", [i64], []), 352),
   (("full_analyze_reasons_fid", [i64], []), 96),
   (("full_ema_update", [i64, i64], []), 64),
   (("full_learn_clause_m6", [i64, i64], [i64]), 768),
   (("full_bump_analyzed_mode_fid", [i64, .bool], []), 160),
   (("m6_hdr_init", [i64], []), 0),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 48),
   (("full_restore_bump_ana_mode_fid", [i64, .bool], []), 176),
   (("full_ana_failed_lit_m6_hdr", [i64], [i64]), 240)]

@[expose] def hint_full_analyze_m6_hdr : armIsa.Hints := _decH #[
  "4210311031001S00101A23000H000Y4000/xNa80010"]
@[expose] def ext_full_analyze_m6_hdr : List (SigEntry × Nat) :=
  [(("full_analyze_core_m6", [i64], [i64]), 848),
   (("m6_hdr_dr_update", [i64], []), 48)]

@[expose] def hints : List armIsa.Hints := [hint_full_ana_failed_lit_m6_hdr,
    hint_full_restore_bump_ana_mode_fid, hint_full_analyze_reasons_fid,
    hint_full_analyze_core_m6, hint_full_analyze_m6_hdr]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_bump_analyzed_mode_fid", [i64, .bool], []), 160),
   (("full_backtrack_ac_fid", [i64, i64], []), 96),
   (("full_ema_update", [i64, i64], []), 64),
   (("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_div", [i64, i64], [i64]), 0),
   (("full_one_lit_confl", [i64], [i64]), 272),
   (("full_deduce_1uip_m6_hdr", [i64], [i64]), 400),
   (("full_min_shrink_m6", [i64], []), 352),
   (("full_learn_clause_m6", [i64, i64], [i64]), 768),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 48),
   (("m6_hdr_dr_update", [i64], []), 48)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Analyze
