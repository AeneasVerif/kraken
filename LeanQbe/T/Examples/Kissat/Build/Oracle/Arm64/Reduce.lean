module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reduce

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X6)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X20)),
  (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X23))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X19))), (.slot 1 .w64),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.slot 0 .w64)]

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

@[expose] def hint_full_red_less : armIsa.Hints := _decH #[
  "B600031010203330435060610016001000Xvud7000XW00yyZ30d/ydVZuWZu00000"]
@[expose] def ext_full_red_less : List (SigEntry × Nat) := []

@[expose] def hint_full_red_sift : armIsa.Hints := _decH #[
  "X4410708340621293A0A3B0B020131093906040604312739093A0A0209390A3A0606110708400000000345",
  "5370317C303014455370DC14401027XF4455370XI1XL7DC167XG101020010XvuddjmZpmkkxW00YWWWWWWWW",
  "WWWWWe00aWWWXWWWWWWYWWWa40yyZZamXvuccfW00Zpyd/yd//vl/ul//pJiZuWZuWWcmWdmWWiC0000"]
@[expose] def ext_full_red_sift : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_reds : armIsa.Hints := _decH #[
  "eU2D1B140D0E0011080F021F0001083506202C39093A0A0200300C3C0605060530213C0C3909020C3C0939",
  "060610010802030215230D350623273C0C3A0A020333073706050605332037073C0C0207370C3C06061300",
  "08090210050G0G0E05050H393A0A392A0A0A09090A190A293F0F392F0F0F09090F1A0A293F0F392F0F0F09",
  "090F1A0A293F0F392F0F0F09090F1A07090H16393A0A392A0A0A09090A190706440479040H1D390D543404",
  "042I0I060A0D0F0906224A09040D0H3A3909092F2A0A3A3909092F2A0A3A3909092F2A0A3A3909092F2A0A",
  "04090H163A3909092F2A0A0406270D1J0G0H443444344434443405040H16443405060H4444444405040H16",
  "4405063F35050505053000000002112937070707073C0C0C070H223A06X80000000338BA453030000353A4",
  "8B1F301014KF53A48B0400004KF53A48B3017403015KF53A48BQ715501028KF53XS5A48BXV0Y21Q7168Z01",
  "0428BA4192010138BA4Z190300003A48BZ1933013030148BZ19A4Z91154010278BZ19aB5A4aE3aH0Z91167",
  "XG1046bJGbKEbM553bG08B0600007bJGbKE53bG0A48BbM517701007bJGbKE53bG0A48BbM517701007bJGbK",
  "E53bG0A48BbM517701044538BbKEbJG11401006bM553bG0bKEbJG8B31C7603009fI1fJC53bM5fK7bG0bKEb",
  "JG8B0900009bM5fI1fJC53fK7bG0bKEbJG8B19901009bM5fI1fJC53fK7bG0bKEbJG8B19901009bM5fI1fJC",
  "53fK7bG0bKEbJG8B1990103953bM5fJCfI1bKEbJGfK7bG08B2AF902009fI1fJC53bM5fK7bG0bKEbJG8B39A",
  "F903017bM553bG08BbKEbJGfK721C702019fJCfI153bKEbJGfK7bM5bG08B090000953bM5fJCfI1bKEbJGfK",
  "7bG08B249902019fJCfI153bKEbJGfK7bM5bG08B14901009fJCfI153bKEbJGfK7bM5bG08B14901009fJCfI",
  "153bKEbJGfK7bM5bG08B14901053538BkDG030000453kDG8BkB11540100453kDG8BkB11540100453kDG8Bk",
  "B115401043538BkDG15301003538BkDG15301003538BkDG15301043A48B531A301005A48B53n4An7F155G1",
  "006A48B53n4An7FnM0156G1000ZWiXudiWdWzmXuWXy+ldWWkyWWzyzyzyzuWWWcuzmWWxZtXsdkZikycuzmWZ",
  "WWWikuXmWbgrWWaWxpsWWeXtdieXtdieXtdieXtdiWXWWWWyyZpsuXvuddjmWcWWWWXvuddjmZpmkkxWWWXWK0",
  "XWYWWWWWWWWWXWXYWWWWWWeWWnWWWWWWWWWWmmWWWYaWWWWWWWWWWWWWWWWaWaeWWWWmYaWWWWaWWWWWemWWWW",
  "WWWWWWWWWWWWWWWWWWaWXWWWWWWWWWWWWWaWWWaWYWWWWWWWWWWWWWeWWWW00mXXWWWWaWWWWmWnWWWWWYaWWe",
  "mWWWWWWWWmeeWWWXYWWWWWWWWWWWWWWWXYWYaWWWWeXYWWWWYWWWWWaeWWWWWWWWWWWWWWWWWWWWeWYYWWWWmW",
  "WWWWXWWWYYWYYaWWWXWWWWWWYWWWaaXaY10XWaewYaXZeemWWWmaYXWWWcWWeiaiaiaiWWWWYgimXWffpWopcX",
  "bciYgimWXWWWbceWmXWWWaWWxfnWWaXspYWXspYWXspYWXspYWYeWWWWkkXnoeWyyZZamWYWWWWWyyZZamXvuc",
  "cfWWWWW00+lzy////t///+l+y/////xp//kl///////+tdd///zv///////////////zv/xoWl//dzv////v//",
  "///td////////////////////l/vv+Z/+Z//yt/yd//vx/xxpyd/yd//vl/ul//ppznuLXmYZWWWWeWWWXmXZW",
  "WWWWaiWWnmWWWWWWWXeuuWWWYcWWWWWWWWWWWWWWWYcWaj/mWWuYcWWWWcWWWWWeuWWWWWWWWWWWWWWWWWWWWm",
  "WccXyWXyWWZeWZuWWcaWaaiZuWZuWWcmWdmWWiiYkdA0000"]
@[expose] def ext_full_sort_reds : List (SigEntry × Nat) := []

@[expose] def hint_full_reduce_m6 : armIsa.Hints := _decH #[
  "eT34041C040D0D150D120H00000405020J04310H010007050004020J041C250215021J021J150J1502150D",
  "140804040D250203150J17191A11151C1B1404150D350505062002150D05000H200004050D1K1L1A1B1F12",
  "44070C0007050D2G3909050D120016290205060000000000221J05020C09090C1J04040H020H0H050D2311",
  "0612050H05051D053H0404000H050104000H050104000H050104000H050105000H0404000D050105050507",
  "07060J12010H050400012001050505000505240D000H05050H0001040501221624301J0000003404000506",
  "150J1502150J150J111C190015170A1303150D350505062402150D05040H240403050D2J0J0J1J021J120K",
  "0J0K1L0M0502051L0502051314040H03040H1302030314030305020NX6001K0010034N5OAC143010144NAC",
  "5OB4154010044NACB45O154010234NAC5O35043030324N5O1P2010124N5O02000314N1K1010134N5OXLP1Q",
  "3010644NY6Q5OXLP040001AYL1YRBYJAYH9YPCYF74NY6Q5OXLP14A0101BYL1YRBYJAYH9YPCYF74NY6Q5OXL",
  "PZ240B000564NZRKZTLY6Q5OXLP1M6010094NZRKZVAa1BY6Q5OXLPZTLa3F23190201Da634NZRKZVAa1BY6Q",
  "5OXLPaB7ZTLa3FaA4a7110DYe0113FaCCaD0ZRKa71aA4a634NZVAa1BY6Q5OaB7ZTLa3FXLP15FYWG100Fa63",
  "4NZRKZVAa1BY6Q5OXLPaB7ZTLa3FaA4a71aU5aD00FYe0002A4NZRKY6Q5OZVAZTLa3Fa1BXLPbB013Am0102E",
  "a634NZRKZVAa1BY6Q5OXLPbB0aB7ZTLbG5a3FaA40Egu0002C4NZRKY6Q5OZVAZTLa3Fa1BXLPbB0a63aB70CY",
  "m0000Ea634NZRKZVAa1BY6Q5OXLPbB0aB7ZTLbG5a3FbP40Egu00064XLP4NY6Q5O04000184NZRKZTLY6Q5Oc",
  "6MXLPcH3158010184NZRKZTLY6Q5Oc6MXLPcH320180200B4NZRKZTLY6Q5Oc6MXLPcH3dD0dC4dG10B000374",
  "NZRKZTLY6Q5Oc6MXLP117010284NZRKZTLY6Q5Oc6MeO1XLP158010294NZRKZTLY6Q5Oc6MeO1XLPeR509000",
  "224NY6Q1P2010034NY6QXLP0300023XLP4NY6Q0300049g30g8Ag29g0Cg77fU1XLP4NY6Q1390101Ag30g8Ag",
  "29g0Cg77fU1XLP4NY6QgF30A000534NY6QXLP0300074hMK4NhOMhNL0400014hMK4NhOMhTL0400013hMK4Nh",
  "OM15301024hMK4NhOMiA5134010E0202372314Y1224144130303G413030304131303041303030413030304",
  "13030304130303c52043ZM224102230Z822300qWaWWWWWWWXWWZWXXmcXaqrYWnXWWdWbxWaWWWWWWWYWWWWW",
  "WWWWWWWZWWWWYWWaeWWcWaZsWcYrgWWuWeiXmfgrgaaWWenXWWWXXeWWWWWWWWH0eWYWYWWqWWWWWmWeeeaWWW",
  "WWWWWeXWWWmWeWWWWWWWWWmWWWWWWWWWYaWeXWeeWenWWXWmWWWWWWWWaWYYYXWWWWWWWWWWWWeaWWeeWYWWWW",
  "nWW00aWaaaWXWXWWYWbbeWeWaaaYWaWWWeYaaWmWWeWaeWWoWWWWagWaWWWWWWWXYWaanaaWaemWWmefWWmWaW",
  "WYWXXXWmXWWWWmWWnYaaYXeaaWXWWYWemq00XYWWWYWWWWWWWWWWpWWnWWcmWWeXWWWsWmWWWXWYWWXWWWWWcW",
  "WWXWYWWfoWYWWWWWemWWWmWWWWWWWaWWWWWWWWWWWWWaWWW00lt/ttt/z/z+dx/nml/Z/pttx/t///lxtt+l//",
  "l/tlmih//udtZ/seeeee+vzx/tsztt/tk/y+/liZsl/t//u/yzz+/z///++/+yhttxyltt/rmdhXk+tVeWeeeW",
  "YWYXuaWklmWyWieeaWeWWWmaeeXmWWmWemlpqWWdueyWftttttXcYaWefYeeWenWZXWmpyfmWeWWdWZYYXWYWW",
  "WXXWXZqeeaZmeeWgluq+nXe0002525678"]
@[expose] def ext_full_reduce_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 48),
   (("full_sort_reds", [i64, i64], []), 0),
   (("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_div", [i64, i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("full_arena_sweep_m6", [i64], [i64]), 384),
   (("full_compact", [i64], [i64]), 624),
   (("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_full_reduce_purge_c0 : armIsa.Hints := _decH #[
  "YE250215021J02150J111C191015171A1303150D350505062402150D05040H240403050D1C330D20050105",
  "070D293505050D1205162702050601050505051108121J000303300003050H2J0J0J1J02D00150010014N0",
  "1000114N01000314N0100017O0UAM9KCS7I14N13701018O0UAM9KCS7I14NX5308000514N01000024NXUC14",
  "2010154NXUCY14Y60Y2315581136Y81Y234NXUCY14Y60156X010064NXUCY14Y60Y23YP506800244NXUCY14",
  "Z6504800414N010001020230mWkWemWWWuWmkuXmjWWiWacWuargrYWWX10XYaWWaYWWWWWaWYWXXXWmWWWWWW",
  "WWe80YoqXWWWnYWWYXXaWYWYWXWWmmmeWmWWWeXea40XcWWXWaWeWXceWmWWWaeWWWeWWWWWWWW00X/uudz//+",
  "zv/pxzzmkv/x/yl+k+/l+////lyltNdduYWWXYcWiaYYlncWaWZmXnXWmXWWWWmZme800012"]
@[expose] def ext_full_reduce_purge_c0 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_arena_sweep_m6", [i64], [i64]), 384)]

@[expose] def hints : List armIsa.Hints := [hint_full_red_less, hint_full_red_sift,
    hint_full_sort_reds, hint_full_reduce_m6, hint_full_reduce_purge_c0]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 48),
   (("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_div", [i64, i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("full_arena_sweep_m6", [i64], [i64]), 384),
   (("full_compact", [i64], [i64]), 624),
   (("m6_hdr_init", [i64], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Reduce
