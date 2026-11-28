module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Minimize

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X3)),
  (XRegOrSp.reg (XReg.X4)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X20)),
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24)),
  (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X0)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X29)), (XRegOrSp.reg (XReg.X14)),
  (XRegOrSp.reg (XReg.X8)), (XRegOrSp.reg (XReg.X9)), (XRegOrSp.reg (XReg.X10)),
  (XRegOrSp.reg (XReg.X11)), (XRegOrSp.reg (XReg.X12)), (XRegOrSp.reg (XReg.X15)),
  (XRegOrSp.reg (XReg.X6)), (XRegOrSp.reg (XReg.X13)), (XRegOrSp.reg (XReg.X7)),
  (XRegOrSp.reg (XReg.X26)), (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X15))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X29))), (.slot 13 .w64), (.slot 3 .w64), (.slot 4 .w64),
  (.slot 5 .w64), (.slot 7 .w64), (.slot 6 .w64), (.slot 12 .w64), (.slot 0 .w64),
  (.slot 8 .w64), (.slot 11 .w64), (.slot 1 .w64), (.slot 2 .w64)]

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

@[expose] def hint_full_min_mark : armIsa.Hints := _decH #[
  "I400102131404051607140820200009090505200000002391C3G50350000coaYb10XWW00mqW80YWWWW00Z/",
  "//++t/FXXeWG0000"]
@[expose] def ext_full_min_mark : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_tmp : armIsa.Hints := _decH #[
  "cA2A1B0C08111D0C15191909205919092908000C0403082400040E0F070G09020H0H060G190973090G1833",
  "080B0B0B030G30000020340430000020340430000020340430000020340403000G18300000203404030806",
  "440904000308030G300004243E0E0H0H500004243E0E0H0H500004243E0E0H0H500004243E0E0H0H23000G",
  "18300004243E0E0H0H2308180I180H080H03080338082E0E0J2K2J0J0L2L022K0L0E000B04086E00040818",
  "6E0004080C000G4040404009000G184009083E0E092H1G04250500200C4308V0000000356AH58BEDC12045",
  "02305H58B6AEDC13043503325H5EDC16AXIF0500028XHE6AEDH5XOHC18BXF008000086AH58BXF0XHEXOHED",
  "C1138010086AH58BXF0XHEXOHEDC1138010086AH58BXF0XHEXOHEDC1138010576AXHEXOHC1YHBEDH507000",
  "07XHE6AYHBEDH5XOHC113701007XHE6AYHBEDH5XOHC113701007XHE6AYHBEDH5XOHC1137010456AC1YHBED",
  "H505000076AXHEXOHC1YHBEDH52307020256AC1YHBEDH5135010056AC1YHBEDH5135010056AC1YHBEDH513",
  "501045H5EDC16AXIF1M501017H5EDC16AeHIeFMXIF1970101AH5EDC1eP3eMHeI96AeHIeFMXIF30B4A0300D",
  "eQ0eS4eRBeP3eMHH5C1eI96AeHIeFMXIFED0D0002AeRBeI9eP36AeHIeFMXIFH5C1ED14A0100BeRBeP3eMHH",
  "5C1eI96AeHIeFMXIFED204B02029eI9eP36AeHIeFMXIFC1H5ED0900009eI9eP36AeHIeFMXIFH5C1ED20490",
  "2028eP36AeHIeFMXIFC1H5ED19801008eP36AeHIeFMXIFC1H5ED19801008eP36AeHIeFMXIFC1H5ED198010",
  "53C1ED6A13301006C1hQHED6AhI3hLE196X21006EDC16AhI3hLEhR906G0000ZcZZWiiWdWWdpvyyWWXyWW+W",
  "WiuxZWWWWWZWznmWcXxZsXxZsXxZsXxZWWWuWXxZWWZsdZsdZsdZscWWZWWgrgWWWWWWWusigne50XWWmWaWWW",
  "WWeWWWWWWYWWXWWWWWWWWfWXXXWWWWYaWWWWWWWWWWWWWWWWWaWWYWWWaeWWWWWWWWWWWWWXWaeWWWWaaeWaWW",
  "WWWWW00mWeWYWWYWYaWWWWWenWWemWaWWWWWamWmmmWWWXYWWWWWWWWWWWWWWWWYYWWnWWWYaWWWWWWWWWWWWa",
  "WmYaWWWWoYbWYWWWWWaYG0XYXvWdaWWWYWmeaWaWWqWWgWWakfvWWWWWXaiymXYevvoevvoevvoevvXWeeWWvv",
  "WYXppXppXppXpoYuXWYWWWeWnWaWWkWdWWW00X+l/l/x//v/xp/////cyl/kd/tWZ///suY++l///zv///////",
  "/////////vv/+y///xp////////////p+lxp///+hxqlvZ////neVXmWmWaWWcWaiWWWWWvZmWnuWe/yWWWfdz",
  "XXmWWWYcWWWWWWWWWWWWWWWWccWXZWWWaiWWWWWWWWWWWWiXmaiWWWXqahmcyWWWWkt000010"]
@[expose] def ext_full_sort_tmp : List (SigEntry × Nat) := []

@[expose] def hint_full_min_lit_dfs_m8 : armIsa.Hints := _decH #[
  "cG5J0101021N071A23071O1F131E1P150508100C250C1Q1M1R1K0K0K463D000000053H0B0502200716000L",
  "0C300C000I0C070I0I0C070B0G001L0L16070L080B2B0B0B0B0B0B160505060401080H000H0B0L20000002",
  "2H07071505161615070H0808250704020H0268030G051404160704080323030303030307070B0G001L0L16",
  "070L080B2B0B0B0B0B0B160505060401080H000000022H07071505161615070H080825070H0268030G0514",
  "041607040803230303030303384615050505040502031H0H16070H0804240404040404000GH001900103B4",
  "9TEVP9J7SHANOPFR3ENA10BXW0005249TE1120100E49TEVPXGR9J7SHANOPFXEMR3XKKXCQEN3145E0300E49",
  "TEVPXGR9J7SHANOPFXEMR3XKKXCQEN3145E0307NXQ149TEXR4XTDVPXGR9J7SHANOPFXEMR3XKKXCQENY15YG",
  "LY6BY5HY75YL00NdqWW0003IXTD49TEVPXGR9J7SHANOPFXEMR3XKKXCQENXQ1XR4Y5H0IaWW0002KXTD49TEV",
  "PXGR9J7SHANOPFXEMR3XKKXCQENXQ1XR4Y5HY75Z100KiWW0009IXQ1XTD49VPXGR9J7SHANOPFTEXEMR3XKKa",
  "30XCQENXR40ImW00095XQ149TEa40b95058004IXTD49TEVPXGR9J7SHANOPFXEMR3XKKXCQENXQ1XR4Y5H0Ia",
  "WW0002KXTD49TEVPXGR9J7SHANOPFXEMR3XKKXCQENXQ1XR4Y5HY75bV00KiWW0009IXQ149TEXR4XTDVPXGR9",
  "J7SHANOPFXEMR3XKKXCQENcR00IaWW00085XQ149TEcS0dV5058003349TEeL11030101449TEeL1eQ0040002",
  "649TEeL1eQ0f05f2306G001040120340iWXaWWkWWWWZWWfWWzuWuWXaoXmWWXWWZWWfWWWWWXmWamWdkWWuWX",
  "aoXmiWWWmWXmWamWWWZmaiZmW+YgmiaWbgqjY10mWWWWmWWWWeWWWWWaWWaWWWYemWWWWWeWWWWWaWWWWWWWWY",
  "WWXWWWWYemWWWWWWaWWWWWYWWWXWWWWWWWWWWWWXXYmWWWW00eWWWagWmWmaWWWWXYmaYWYYXaafWqaWaWWWWX",
  "YmaqWWWWWneYWmWoYXaafWqaWWYWWWWWneYgWqeafXWWXWWWXWmmWWXWeG0aWWWWuWWWWWXWWWWWimWeWWWWWW",
  "WWaWWXWWWWWWWWWmWWWWZaWWeWWWWWWdaWYWWWmWWWWWZXmWaXoWWuWWaWWWWWWW00X/d///th+/+/t////zw/",
  "tx/vxyttj+nt/sp///zw/st////+zlx+/+fxyttj+nt//xf///+zlxh+plpjz//z///z+c///z/kVuWWWeqXWX",
  "WeWWWWYbWeaWcaZeeoXkeWfiWWWYbWfeWWWWXYmaXWXsaZeeoXkeWWasWWWXYmaqXimioYWWYWWWYXvWWWYWn0",
  "00070516789"]
@[expose] def ext_full_min_lit_dfs_m8 : List (SigEntry × Nat) := []

@[expose] def hint_full_shrink_lower_m8 : armIsa.Hints := _decH #[
  "X6430513031616230G0110001607100823230309090909130G011000160710082323030909090960019001",
  "0134964950360020000002295L10210020000002295XD1021007020A4B631430B32A020CB062B02A224112",
  "2B002241M22A20wemfXWWWwemfXWo90aWWWWWWWaWWeW00YYmaWWWWYYmaXa00eWWWWWWWeWWWWWW00X////xw",
  "/t////xw/tztVabWeWWWWabWeYe00030"]
@[expose] def ext_full_shrink_lower_m8 : List (SigEntry × Nat) :=
  [(("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]), 64)]

@[expose] def hint_full_shrink_blk_bool_m8 : armIsa.Hints := _decH #[
  "bR6K141R1T1L1E1U1Q1V0B0849092D0D0D0D2H0108BA0G3H0D2D0D1607000G3707030939071F09000C3I0C",
  "0I000C00002N09090S0S48311H06000A08002906001P0P17000807080P0P2D0B0919091616190G011P0P16",
  "070M0809290909090909010G091P0P16070M080121010101010130000B0606370C090G130371030G183108",
  "2J36390911010101030G01100016070008032303030303030508060G312505050531250505053125050505",
  "312505050509010G1831250505050908R001900100FRB83C4KE5X0AK654OOQ7X1ERMUQVGTIL1HFm0100FRB",
  "8365KEC4AK4O5X0QVMUGTILOQ7X1ER2H1FeW02026C4KE5X0AK654O3M9J60300DC4KE5X0AK654OOQ7X1ERMU",
  "QVGTIL5BMIJ3Da05007XLMC4KE5X0AK654O1J70100FXLMC4KE5X0AK654OXKBQVMUGTILOQ7X1ER2J0FeW021",
  "0IXLMC4KE5X0AK654OXKBOQ7X1ERMUQVGTXMIXNJXPAIL10Im0108JXKBXLMYAJ5X0AK65YE34OQVMUGTC4ILY",
  "MFKEOQ7X1ERYJ92GIJgWW4204JYAJ5X0AK65YE34OQVMUGTC4ILZ6NZASYMFZ5IKEOQ7X1ER4BDH0JaYW1400I",
  "ZCDYAJC4KE5X0AK654OYE3OQ7X1ERMUQVGTILZDHZBB0IXW2002MZBBZCDYAJ5X065YE34OZ6NKEC4OQ7X1ZAS",
  "YMFZ5IERZE0AKQVMUGTIL11MYa4111KYAJ5X0AK65YE34OQVMUGTC4ILZ6NZASYMFZ5IKEOQ7X1ERZE03BDHKa",
  "YW1308OZBBZCDYAJ5X0AK65YE34OQVMUGTC4ILZ6NZASYMFZ5IKEOQ7X1ERZE0ZOAZLH0OimeW4004OZBX2ZCX",
  "3YAX45X0AX56X6YEX74OQVMUGTCX8IX9Z6NZASYMFZ5XAKXBOQ7X1ERZEXCZOAaQ10OameW4004OZBBZCDYAJ5",
  "X0AK65YE34OQVMUGTC4ILZ6NZASYMFZ5IKEOQ7X1ERZE0ZOAbE90OameW40033c8MC4KE03000274OC4KEc8MA",
  "K5X0cAJ0700008c8MAK5X0cAJ654OC4KE11801008c8MAK5X0cAJ654OC4KE11801008c8MAK5X0cAJ654OC4K",
  "E118010544OC4KEc8M154010154OC4KEc8MdA505000274OC4KEc8MdA5dE9dM107X00034c8MC4KE2Y0dN319",
  "401004c8MC4KE2Y0dN319401005c8MC4KE2Y0dN32Y0dN0195010B083D20230DC05BZC131XA22EDQQ33F34G",
  "35H37I3643C230A38J3BK31L3233AM39N1Q2F32G42H52I724622C2A02J82KB2L12322MA2N9122MAJ22N99M",
  "2F32G42H52I724622C2A02J82KB2L12320M2F32G42H52I724622C2A02J82KB2L12320M2F32G42H52I72462",
  "2C2A02J82KB2L12320ZiWWZkXtWxmjmWWWWZWWfWXcZpWiWXgreWWWWWWWZWWfWWWZWWfWXamiWWYecWWdWWWW",
  "WkWnuWWWavmduXmiuYrgL0mWWnWWWWWWWWWWeaWWWWaWWWWWWaWnWWWWWeWWWWWWWWWWWWWWWWWmWWWamWWWWW",
  "WYWWWWWWWWWWWWWWWXWWWWWWW00eWWemWWWWWWWWXaYWWWXYmaWWaWYWemWWWYbWWWWWWXYmaWWWXYmaYeWWYg",
  "aWmaaWXWWWnWmaWqWfeWXWWmWWWmWW00XaWeXcWpWfmamWWWWXWWWWWYWXWaWeWWXXWWWmWWXWWWWWWXWWWWWW",
  "WaWWWWYWWZWdWWicWWyWWWWimWWWmaeWWW00dd//kl////////ytv///zw/t//t/v/kl///vrn/////zw/t///",
  "zw/txl//xZt+/tt/zWl+j+lt+t/bl/z/+l//+///VuWWnmWWWWWWWWZecWWWYbWeWWeWcWnmWWWcgkWWWWWYbW",
  "eWWWYbWeamWWayeXWeeWY/mXoXmeXeWwmWYWXmWWXWWW000EB0516789OPQD"]
@[expose] def ext_full_shrink_blk_bool_m8 : List (SigEntry × Nat) :=
  [(("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]), 64)]

@[expose] def hint_full_min_shrink_m6 : armIsa.Hints := _decH #[
  "a22P1R190719090C0C1F1N1U79090309020110001607000803230303030303050859093310000S28290931",
  "0719090C000S090G18311O080509090908010829090841062E1908150906030906090908190G3101081901",
  "0C060G1179010G1829080G010G452309010C18290909250418290909290704050C432001050C190R09190E",
  "190RV0000000034Q6P8R03000124Q8R0200026MUKNIF8R4Q6P06000064QIF8RMUKN6P156010074QIF8RMUK",
  "N6PR507000294QIF8RMUKN6PR5X19X3109a00035IF6P4Q8RKN0500006MUKNIF8R4Q6P1O601008MUY13KNIF",
  "8R4Q6PXPO20S82200AY7SMUKNIF8R4Q6PXPOY13Y600Ae00027Y7SMUKNIF8R4Q6P0700027IF4QY7SMUKN8R6",
  "P1O701018IF4QY7SMUKN8R6PYSO08000554Q6PIF8RKN1E501005IF6P4Q8RKN2E9502006IF6P4Q8RKNZG91E",
  "601025IFKN4QZRE8R0500018ZS56PZV3ZRE4QIF8RKN19801018ZS56PZV3ZRE4QIF8RKN0800029ZS56PZV3Z",
  "RE4QIF8RKNa890900027ZRE4Q6PZS5IF8RKN19701007ZRE4Q6PZS5IF8RKN19701007ZRE4Q6PZS5IF8RKN19",
  "7010534QZRE8R0300015KNIF4QZRE8R0500005IFKN4QZRE8R291502025KNIF4QZRE8R11501017bT5KNIFZR",
  "EbK14Q8R14711007bK1bV4KNIF4QZRE8R0700026bV4KNIF4QZRE8R215602010206B0maaWcuWZZWiiWWjmWW",
  "YWWrgqWWWmiWmWWWZXmWiWWWWuWWYZpWbvsWWWcWWoWjrgmWmL0mWeWXXWWWaXWemWWWWnWaWmaaWaWeXWXYWe",
  "aWXWWmWeWWWeWWWWeWWWWWWWa00eWWmeWaWWmmWXYWmaeWWWYemYWeYYaYWaWmWnWaWWmmWeWaWWWaWWWYbWeW",
  "WWYmY00mWYeWXvWdaWWamWWWWaWWWWWWWaWWWWWXWmWaWmWWeWeWWvWWimWWWYWWWWaWWWWW00////Z/+/l/t/",
  "++d/zx+ltd///vkdx/lxxtv/t+/+b/p/++k/l/t///p///xr/l///u/xVyWXWmWeWXXuWYaXmeuWWWcnuaWmaa",
  "ecWeXWXwWiWXXnWmWeWWWiWWWagWmWWWdWa000080516789O"]
@[expose] def ext_full_min_shrink_m6 : List (SigEntry × Nat) :=
  [(("full_sort_tmp", [i64], []), 16),
   (("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]), 272),
   (("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]), 64)]

@[expose] def hints : List armIsa.Hints := [hint_full_min_mark, hint_full_sort_tmp,
    hint_full_min_lit_dfs_m8, hint_full_shrink_lower_m8, hint_full_shrink_blk_bool_m8,
    hint_full_min_shrink_m6]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Minimize
