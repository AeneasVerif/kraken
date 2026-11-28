module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Kitten

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X21)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X6)),
  (XRegOrSp.reg (XReg.X8)), (XRegOrSp.reg (XReg.X9)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X23)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28)), (XRegOrSp.reg (XReg.X29)),
  (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X4)), (XRegOrSp.reg (XReg.X11))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X14))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X28))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X29))), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X15))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.slot 0 .w64), (.slot 1 .w64)]

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

@[expose] def hint_full_m6_max_v : armIsa.Hints := _decH #[
  "B100102030202020103000210012001000000050YG0XydHZuEX0000"]
@[expose] def ext_full_m6_max_v : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_add_ticks : armIsa.Hints := _decH #[
  "73303040105050501020010100000X80uFdG0000"]
@[expose] def ext_full_k6_add_ticks : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_init : armIsa.Hints := _decH #[
  "bB350001050405050501060006160708191A08040B040C051D05050D1505057E0501104E004E1F12050G05",
  "05020207225G0202020H0C0C0C050E0E0E0E0F0F0F0C020202020I0J011202027F0201184F08011202027F",
  "0201184F08011202027F0201184F08014F3G3F320F01184F080102014C0C3F3C320C01184C020801453C35",
  "3205011845080J0208320202020E060606060D040J011202027502011845080J0112020275020118450808",
  "X9000000002425316221049U4O953QATBX5DK6VC4209cD0009X5D53K6VC42U4O9QATB1E9bE1109X5D53K6V",
  "C42U4O9QATB1E9bE1109X5D53K6VC42U4O9QATB1E9bE103AU4O953QATBX5DK6Y2FY0EVC0A+D0017O953QAT",
  "BU4X5DK607YM001CU4YOHZ9IYS5Z4CX5DK6Z0E53O9QATB0CXg1000DU4YKGYOHZ9IYS5Z4CX5DK6Z0E53O9QA",
  "TB1FDYq1100DU4YKGYOHZ9IYS5Z4CX5DK6Z0E53O9QATB1FDYq1100DU4YKGYOHZ9IYS5Z4CX5DK6Z0E53O9QA",
  "TB1FDYq1104BU4Z9IYS5Z4CX5DK6Z0E53O9QATB0Br1000CU4YOHZ9IYS5Z4CX5DK6Z0E53O9QATB1FCXg1100",
  "CU4YOHZ9IYS5Z4CX5DK6Z0E53O9QATB1FCXg1100CU4YOHZ9IYS5Z4CX5DK6Z0E53O9QATB1FCXg1104AU4YS5",
  "Z4CX5DK6Z0E53O9QATB0AgH000BU4Z9IYS5Z4CX5DK6Z0E53O9QATB1FBr1100BU4Z9IYS5Z4CX5DK6Z0E53O9",
  "QATB1FBr1100BU4Z9IYS5Z4CX5DK6Z0E53O9QATB1FBr11049U4YS5X5DK6Z0E53O9QATB09b9000AU4YS5Z4C",
  "X5DK6Z0E53O9QATB12AgH100AU4YS5Z4CX5DK6Z0E53O9QATB12AgH100AU4YS5Z4CX5DK6Z0E53O9QATB12Ag",
  "H1048U4X5DK6Z0E53O9QATB08YL0009U4YS5X5DK6Z0E53O9QATB129b91009U4YS5X5DK6Z0E53O9QATB129b",
  "91009U4YS5X5DK6Z0E53O9QATB129b91058O953QATBU4X5DK6Z0E08YM0008U4X5DK6Z0E53O9QATB128YL10",
  "08U4X5DK6Z0E53O9QATB128YL1008U4X5DK6Z0E53O9QATB128YL1066O953QATBeO4eND06M0007eO4eIEO95",
  "3QATBeND157P1007eO4eIEO953QATBeND157P1007eO4eIEO953QATBeND157P1054O953QATB0460006O953Q",
  "ATBeO4eND156M1006O953QATBeO4eND156M1006O953QATBeO4eND156M10500000000ZmWbgrWWWdWWgrgWWW",
  "WZmWXuWZpppmWdWWkkkdWWWyWXvvvuWdWWgrgWWZmWbgrWWXuWYrgmWWWWWWgoomWfbgWkWWrgqWaWqWWW10XX",
  "WYaWWWWXYWaeWWWWYWWWaemXYWWWWWaWaeWWWWWeeWnWWWWWYWaeWWWWXWYaWWWWWmXYWWWWWmWWWWWWWWWWWW",
  "aWemWWWWWWWWWW00mmXYWWWWanWYaWWWWfWWWYaeWnWWWWXYWYaWWWWYaaWemWWWWnWYaWWWWemXYWWWWaeWnW",
  "WWWYeWWWWWWWaWWWWYWaeWWWWWWXeWWK0XmXWWWcWWZWYWWWiWddXmWWuWnnnnmWZWYdccZXWWiWeuuuuWZWYW",
  "WWiWXmXWWWcWWuWmWWZWZptkyWWWWyWWWWcWaWWWvmWWWWg00/++lzv////oy/xp////b///vtZ+y////zv/xp",
  "////vtn/kl///+y/xp////klzv////td+y////xl///////t////v/td/////mqlm+7XXmYcWWWWjZWaiWWWWw",
  "WWWceyXZWWWWYcWaiWWWWcekWnmWWWXZWaiWWWWnmYcWWWWeuXZWWWWamWWWWWWWeWWWWcWeuWWWWWlhmlXOa0",
  "000"]
@[expose] def ext_full_k6_init : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_watch : armIsa.Hints := _decH #[
  "U5E0C0C0C0C0C0F0F0F0F0F0G0G0G0G0G0E0E0E0E0232070E03023D4D3543000XyyldWyWWW100000uacXWj",
  "vvvO0/////x////VaWWWW00000"]
@[expose] def ext_full_k6_watch : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_assign : armIsa.Hints := _decH #[
  "X1440E1C1F0F0F0G0F0F0F0F0D0F0F0F0F0F04040404043H744C150J05121J030202103QF9E530360000gW",
  "ezdtdWWWX90YWWWWWWWWW00XWWWWWWWWW00iWpZkkkk00u/z/////////VdWYWWWWWWWWW00000"]
@[expose] def ext_full_k6_assign : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_add_clause : armIsa.Hints := _decH #[
  "b44F140J0J0E0E0E0004015C0C0C00040E08140001040E040404010E000E1E071G020202020G07071D1412",
  "010H1208020202020I02020202060E0E0E0E0E011C6F0C0F6C0C0F6C0C0F6C020C01181C6F02080D0F2212",
  "02050002020205141203030303030E0E2C0C22022F1207020D0F0D0H0H1I4I0F0D0D15420E0E0E0E0E0233",
  "07071305140C0E0E0E0F0E0E0E0E0D0E0E0E0E0E03030303031H7344130J03131J020302A0012001003536",
  "5420320014428F655324E4421335365421E321078XLGXPD5365YC6XR4Y7IXVH08bA0009XLGXPD5365YC6XR",
  "4Y7IXVHYHE129bA1009XLGXPD5365YC6XR4Y7IXVHYHE129bA1009XLGXPD5365YC6XR4Y7IXVHYHE129bA104",
  "00000023d4EcJ5cA20360000nWgWezdtaWWWXaXuWXymdoWbpcWbWXYmWluWW/m/m/m/mWWWXXgWXWWWXWWkWW",
  "W50eWWnWWWWWWWWWWWWWWWWWWWWWYWWWWX00XWWWWWWWWWWqWWWWWWWWWWWWWWWWWaWWemWWWWWWWWmWWaaWqW",
  "eWWqXWWYWaG0iWpXvvvuWWfuWucZWuYvpdWXeWaWcyWejujujujudddWWWXyWWgWWXcWaW00l/u/z/////////",
  "+d///////+/////ul//p//kl///////+///nt+d/lm+dyp/wlsVdWYWWWWWWWWWXuWWWWWWWXWWWWWdmWWiWWn",
  "mWWWWWWWXWWWkeXuWmlXuZiWbmf0aWWWWWWW0000"]
@[expose] def ext_full_k6_add_clause : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_mtf : armIsa.Hints := _decH #[
  "XC25011407140E0E0E0E0F0E0E0E0E0C0E0E0E0E0E040404040G341H0D3D0J1D0708080K4K340K55000515",
  "350760000000295342X0GREMC65HFX44X6H09j100495342X0GREMC65HFX44X6H09j100175342X0GREMC65H",
  "F07X100145342X0GRE04100135342X0G0310000ekaXayWZmpmWWekhmWWWa80YWWeWWWWWWWYYYWWWWWWW00X",
  "WWaWXWWaWaXfXWWWWWWX20dWWWiWXmXmWWWdWtdtdm00lz//t/z//t/tyjz//////yBYWWeWYWWeWeZoYWWWWW",
  "WZK0000"]
@[expose] def ext_full_k6_mtf : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_backtrack : armIsa.Hints := _decH #[
  "X73514040406040404040I040404040H050505050D1C1504003F3J243E053G013E4E0E1E001J2500500000",
  "0007TC5342HIC6RDMH1F73101253421C2111065342HIC6RDMH2CF612127XC45342HIC6RDMH1F731000nYWW",
  "efvuyyZdWqWWW50YYWWWWWWWWeWWWW00eXXWWWYWWaWaWWWW00uuaiWZWXvvzO0d/lzz///x//t/t////VmYYW",
  "WWaWWeWeWWWW00000"]
@[expose] def ext_full_k6_backtrack : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_propagate : armIsa.Hints := _decH #[
  "a022090L0M03020N030L0L0O0N0409090P090M0M060M0Q0L1R1B121I007S0R0S330J9E0G1C053F07021J0T",
  "351H050D0D0C3U0V3C07011C350J014C3F0J05082J050707050CAB0J020I121J0C02022J13030G0V0V0501",
  "03030367620J0J07070F0DAB0J020I151J0205022J13030G0V0V05010303030J4G0V0V00520203010V0V0V",
  "A00120010014X04RBIV10470CLPGO4X0HNDX1X2X2I4P6SLRQQMM94RBIVCX0471DXERLPGO4X0HNDX1X2X2I4",
  "P6SLRQQMM94BIVGDY1430EXERLPGO4X0HNDX1X2X2I4P6SLRQQMM9XFS6BIVGA3EeY16X34PXLBXMIYQVXVGXP",
  "AXUEXERLPGO4X0HNDX1X2X2I4P6SLRQQMM9XQ3YPUXFSYKDYBTY8225CPxmaZ3200QXLBXMIYQVXVGXPAXUEXE",
  "RLPGO4X0HNDX1X2X2I4P6SLRQQMM9XQ3YPUXFSYKDYBTY82YHH15QXxmaZ3107IYQVXVGXQ3XUEXERLPGO4X0H",
  "NDX1X2X2I4P6SLRQQMM9XFS2BIIaXWS232NXLBXMIYQVXVGXPAXUEXERLPGO4X0HNDX1X2X2I4P6SLRQQMM9XF",
  "SXQ3ZMCYPU0NbmaZ3004IXNVXVGXQ3XUEXERLPGO4X0HNDX1X2X2I4P6SLRQQMM9XFS2BIIaXWS23602023X04",
  "313301ZB224112250YL2261122700eWWWWYWWbWzkyWWWZmkdkWWeWWqZrxmWWWdkWdeZpmhnXvdWykXgmWWW1",
  "0aXWWWXWWWWWWaYYWWWWWWWWaWWWWWWmWeWWWWYWWWWWWWWWWWWWWWWW00YWmWWWmWWWWWYnXWWWmWWWWYWWWW",
  "WWgaamWYmXeWWWYaWWYWWaWWWWW00gWWuWrmWWWeiYiWWWXmcZcYsWWWXXmfmWWWZcWZWXnpWmWuXWicWWWemo",
  "00kZ/x+yZ/+yld///wzz//+//ml/xny////hto//w/zl///xt//x//t/////VXyWaXZyWXZmuWWWbYYWWXWWlm",
  "WakZWWWWqejWWbWYmWWWaeWWaWWeWWWWW0002B892ABCDEFGH"]
@[expose] def ext_full_k6_propagate : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_ana_clause : armIsa.Hints := _decH #[
  "XP4G140404040D040404040B040404040904040404040E0E0E0E0E0C0C0C0C0C1A361H3J133I030J3E0J1F",
  "170F0F083303070308330303030408400000000A42JB8GED65X7CXD6XFHO9X9A14AsK101B42JB8GED65X7C",
  "XD6XFHO9X9AXK40BsK003D42JB8GED65X7CXD6XFHXK4XPIO9X9AXVE0DcsK0000dWWkWYmyZmkteWWWWW50mW",
  "WeWWmeaXWWWWWWWWWW00eWWamWeaYWmWmWWWWWWW00ZWWcWWWaXuWXZpppxpG0dd//s//ltx+/+////////VuW",
  "WfWWmeaXWXWWWWWWWW00000"]
@[expose] def ext_full_k6_ana_clause : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_analyze : armIsa.Hints := _decH #[
  "hV3D1505050R050505050L0505050509050505050T0505050505040404040404040404040404040404463I",
  "1H0J133F030J3C0J1G170G0G083303070308330303030E080O130E0J270X03U0H331J13070E0713070D0E0",
  "E0E0E0I0E0E0E0E0U0E0E0E0E0N0E0E0E0E0E0C0C0C0C0C0F0F0F0F0F0V3B160J133A030J3C0J1G170G0G0",
  "83303070308330303030E080U0U0E0J130J4E3C0C030E00070G016C0C3C000E0F0308210J133E030E0E0E0",
  "90E0E0E0E0B0E0E0E0E0A030303030I0F130E003D3J2E3C033H013C4C0C1C001J2300430J430E010C070C0",
  "F0F0F0F0I0F0F0F0F0H0F0F0F0F0F0C0C0C0C063C1B0A3A0J0A0708080K3K3C0K3E000E1E3E070D0300071",
  "D1E1C13010H000J011C6F0C0F6C0C0F6C0C0F6C030C01181C6F03080D0H23041E0305050505050C0C2F0F2",
  "3032H13070G030H030I0I16460H030314440305040C2E0E0E0E0F0E0E23032G0G0G1G0G0G0G15031G03441",
  "50J05121J0502020305040C2E0E0E0E0F0E0E23032G0G0G1G0G0G0G15031G0344150J05121J050202X3001",
  "200100942X05M9RTCRHLXAX2X5X1XF4090000D42RT7DM9XF4XOIXQHX05XK6CRHLXAX2X5X11EDh4101E42RT",
  "7DM9XF4XOIXQHX05XK6CRHLXAX2X5X1XSE0Eh4003G42RT7DM9XF4XOIXQHX05XK6CRHLXAX2X5X1XSEY1FY7C",
  "0GXmh4004742X05M9RTXAX2X5X1XF41U70100A42X05M9RTXAX2X5X1XF4CRZ1OHL2E3Ae0232BZ9X042X05M9",
  "RTXAX2X5X1XF4CRZ1OHL0Bm1004K42a7UZTDa2IZEHaRFb0BZ9X0CRZ1OM9HLb26aCNaSVX05RTXAX2X5X1XF4",
  "1EKqsK101L42a7UZTDa2IZEHaRFb0BZ9X0CRZ1OM9HLb26aCNaSVX05RTXAX2X5X1XF4b4E0LqsK003N42a7UZ",
  "TDa2IZEHaRFb0BZ9X0CRZ1OM9HLb26aCNaSVX05RTXAX2X5X1XF4b4Eb9AbFC0NcWqsK0057X0542RTcDUXAX2",
  "X5X1XF4070000842cDUX05M9RTXAX2X5X1XF41380103842RTcDUcUGX05XAX2X5X1XF426F882008X05cUG42",
  "RTcDUXAX2X5X1XF43EF382302942RTcDUcUGX05XAX2X5X1XF4dH6098002EeFF42RTcDUcUGX05XAX2X5X1XF",
  "4dH6e4BdV9eEIe9A1DEH101942RTcDUcUGX05XAX2X5X1XF4dH61F98110D42RTcDUcUGX05XAX2X5X1XF4dH6",
  "e4BdV9eEIe9A2FDD8212EeUE42RTcDUcUGX05XAX2X5X1XF4dH6e4BdV9eEIe9A1DEH102942RTcDUcUGX05XA",
  "X2X5X1XF4dH60980017cDU42X05cUGXAX2X5X1XF4078000842RTcDUcUGX05XAX2X5X1XF41D88101942RTcD",
  "UcUGX05XAX2X5X1XF4g2D098002H42RTcDUcUGX05XAX2X5X1XF4g2Dg63gV6gQFgLHg7EgGIh3Ch5B0HZem80",
  "04H42RTcDUcUGX05XAX2X5X1XF4g2Dg63gV6gQFgLHg7EgGIh3Ch5B0HZem8001F42RTcDUcUGX05XAX2X5X1X",
  "F4g2Dg63gV6gQFgLHg7EgGI0Fem8001C42RTcDUcUGX05XAX2X5X1XF4g2Dg63gV6gQF0Cm8001B42RTcDUcUG",
  "X05XAX2X5X1XF4g2Dg63gV60Bm8006942cDUiCDX05cUGXAX2iEEX5X1iKH09gK000A42cDUiCDX05cUGXAX2i",
  "EEX5X1iKHXF413AgK100A42cDUiCDX05cUGXAX2iEEX5X1iKHXF413AgK100A42cDUiCDX05cUGXAX2iEEX5X1",
  "iKHXF413AgK1053n13mDEcDU0300013oI3nUEcDU030006X0230I4231IF22J012241nS2210122110qWnwaea",
  "iuXmWYmYdenWnpWcWlaXymXivmWmqWZ+WWdydydydyWWbgWWWyeWdWWyXuWWWkhmWWWWXudmYWWefvuyyZdWmW",
  "WWWkmWWkkWWWkyWWWWWdWWkWYmyZmbuWWWWWWaWetdWXWWWyWXuWgZmkWtgqWWWWWWW50aWWWWWWWWWWWWmWWW",
  "WWWWWWWWWWWWWWWWWWYWWaeWWWWWWWWXWWWYWaWWmWWWWWWXXYWWWWWWWWWWWmYYWWWWWWWWeWWWWWWanWWWWX",
  "WWWWeWmWWeWWmeaXWWWWWWWWWWWYYWWWWYWWXWWYXWmaWWWWWWWWWWWW00YWWWWWWWWWWWWeWWWWWWWWWWWWWW",
  "WWWWWWWXWWYaWWWWWWWWaqmWnWYWWeWeWXWYWqnWWWWWWYeWmWeXXWWWYWWaWaWWWWWWYemWWaemWWeaWeWWam",
  "WeaYWmWmWWWWWWWnXXWWaeXWWWoWXWmeYWYWWWWWWWWWW00uXdZsiyuWWWWZWaykvppWcXmucWsivuWXWXtWYZ",
  "kZkZkZkWWWWWWWkWWZWWiWuWWWdWtdtdmWuWWWWWWWuuaiWZWZppxmcWWWdcWWWciWWWWWZWWcWWWaXuWfvvvz",
  "vuWWWXZWWWWWiWWuWWWmdWXWXvvvzvvvO0dn/x/////////+d/l//////////////t//////y//xp////////o",
  "o/+ylx//l/l/z/x+cz//////ul+//lzz///x//t/t//////xkf//tkd//lt/d//s//ltx+/+///////+yjz//t",
  "ly//+x/z+/lx/x//////////VkWaWWWWWWWWWXuWmWWWWWWWWWWWWWWeWWWWWWZWWaiWWWWWWWWjjWXZmaWWmW",
  "mWYWaXvYWWWWWWdmXWWmYYWWWaWWeWeWWWWWWansWWenuWWmeWuWWfWWmeaXWXWWWWWWWXZoYWWemZWWXaWYXW",
  "maWaWWWWWWWWWW00027892ABCD"]
@[expose] def ext_full_k6_analyze : List (SigEntry × Nat) := []

@[expose] def hint_full_k6_solve : armIsa.Hints := _decH #[
  "d13200010203020202010T000T1T071V0X00202020V120N0505050I050505050H050505050D02020202021",
  "C1504003F3J243E053G073E4E0E1E001J2200220J130302110606062J0X00X00X00X0030303030R0303030",
  "30L0T0T0T0T0T730500030J030J0E0J433507070408050505040E0C0C0C0F0C0C0C0C0G0C0C0C0C0C05050",
  "505051D654E050J05151J03050312070403000232073408280E3E07340508170E080232073E08280C3C073",
  "E0508170J0207011434070508173203020203030E040203050E0E0E0C0E0E0E0E0F0E0E0E0E0E020202020",
  "23G6245020J02121J0502021307I0012001002564O1T20103BXKCSV4OKTOX056X8HX3IVNXI2XDD1FBP1016",
  "SV4OVNKTOX0561C6O110ASV4OKTOX056X8HX3IVNXI2XDD2CFAC212BY34SV4OKTOX056X8HX3IVNXI2XDD1FB",
  "P1026SV4OVNKTOX05606O0037SV4OVNZKX0a3TZULZPR12701037SV4OVNZKX0a3TZULZPR0700008SV4OVNZK",
  "X0a3TZULaIEZPR148Y0104ASV4OVNZKX0a3TZULZPRbJCb44aO30Au00028SV4OVNZKX0a3TZULZPRcL3148a0",
  "1008SV4OVNZKX0a3TZULZPRcL32458a02168SV4OVNZKX0a3TZULZPRcL31E8a01019SV4OVNZKX0a3TZULZPR",
  "cL3dH42E59a02167SV4OVNZKX0a3TZULZPR1E701019SV4OVNZKX0a3TZULZPReFEcL3159e0106ASV4OVNZKX",
  "0a3TZULZPRfREfC3fA40Au0001040K10C30aWWWWXeWdfxpmWWWWWdWWdWWWWdZmWkdWWWykWXuyWWWgWXwkym",
  "WWWWWWkyWWWX/WWWWYXYbWeWXXddZpmiyYmWWWaXWWW10YWWWWeWWWWWWWWWWWWeWWWoYWWYWWWaeeWWeWWWmW",
  "WWYWWWWWWWWWYWWWWXXWWWWWWWWWWYWeeWWWWWWWXWWWWWWWWWW00eWWWaWWWWWWWWWWWaamWqfXWeXXWmYaaX",
  "WaaYWemWWXWWWWWWWWWXbWWfWmmWWWWWmWWmXWaaWWWeWWmWmWWWWWWeWWK0ZWfntdddXWZWWZmWWWZXuWcZmW",
  "WidWWukWWWWWWuYiddddWWWYiWWWWWkkkkWaWWWWWWWZZWnmWiWdddtXuWWg00Z///l/Z/t///////////to/+",
  "tjz/lzz+/xttz/ttx/k/u/z/////////yn//j++/////+/X+/z/tt///l/+/+///////lm+7mWyWeWWWWWWWWW",
  "WWejWXeoYWmYYXWaeeYWeeaWnWdWYWWWWWWWWWZkWWoXXWWWWWXW+XWYWeeWWWmWXWXWWWWWWWmlXOa0007892",
  "ABCD"]
@[expose] def ext_full_k6_solve : List (SigEntry × Nat) :=
  [(("full_k6_propagate", [i64], [i32]), 112),
   (("full_k6_analyze", [i64, i32], [.bool]), 80)]

@[expose] def hint_full_k6_flip : armIsa.Hints := _decH #[
  "ZM35000105040505050104000515071X0020202020X0020E040404040D140J0401340J3207020202020T02",
  "02020209020202020B020202020N020202020L050505050G1C4J3H0I15041J0J32070U020V3F140202360J",
  "32070102350J32070115350J3E070208270V3F376207320J3I0E120204010E0E0E03B00120010025342152",
  "11073X3D53SX03IU5323009X3D53SX0Y1BXS9YGGYBLY6NXNT4CAIU92412EYRHYJCYSIX3D53SX0Y1BXS9YGG",
  "YBLY6NXNTYKAYMU0EJ002IYSIZ8UX3D53SX0YRHYKAY1BXS9YGGYBLY6NYJCXNTZM6ZEFZAVZG40IdqX8002HY",
  "SIZ8UX3D53SX0YRHYKAY1BXS9YGGYBLY6NYJCXNTZM6ZEFZAV225HZqX8200IYSIZ8UX3D53SX0YRHYKAY1BXS",
  "9YGGYBLY6NYJCXNTZM6ZEFZAVZG412IdqX8101IYSIZ8UX3D53SX0YRHYKAY1BXS9YGGYBLY6NYJCXNTZM6ZEF",
  "ZAVZG40IdqX8003JYSIZ8UX3D53SX0YRHYKAY1BXS9YGGYBLY6NYJCXNTZM6ZEFZAVZG4aA20JdqX8004GYRHY",
  "KAYSIZ8UX3D53SX0Y1BXS9YGGYBLY6NYJCXNTaP5ZM60GXaX10000XuWXWZmZmkddWWZmyWZmyWZmyhmXuapme",
  "WWWWWWykWmWXWWW10mWWWWWWWWWWmWaWeWaWmmaWWWeYWWaWWWWWWWWWWWWWWWW00eaWWWmWaeeYWaeYWeeYWW",
  "WaXeWYWWWWWWYXWoWWWeWWK0uXeeXmXmcZpmWXmkWXmkWXmkWmWuWWmZpppppmiYWdXyWWg00l//uX/lt//+//",
  "tdlx/tlx/llx///tzl/x//////xz+x///lm+7d+WmeWWXWWeumaWemaWmmaWWWeYmWaWWWWWWaYXaWWWmlXOa0",
  "005892AB"]
@[expose] def ext_full_k6_flip : List (SigEntry × Nat) := []

@[expose] def hint_full_k512_add_live_m6 : armIsa.Hints := _decH #[
  "dG440001040E0404040109000919071204040404021407140J140H0E0E0E0B0E0E0E0E0A0E0E0E0E060404",
  "04040I1F140E003G3J2E3C043D073C4C0C1C001J2400340J040404040E07141C1F010F1G080G0G0G0G0D0G",
  "0G0G0G0G09090909093I7C1C0F0F0F0F0F0G0G0G0G0D0G0G0G0G0G0C0C0C0C0C1C070I0C0H36463I4C1C1E",
  "070707050E1C0G0F0F0F0D0F0F0F0F0H0F0F0F0F0F05050505051I754C150J05151J0305030707030E1C0G",
  "0F0F0F0D0F0F0F0F0H0F0F0F0F0F03030303031I734C130J03131J0503032J45070715041E0F0C0C0C0G0C",
  "0C0C0C0D0C0C0C0C0C05050505051H754E150J05151J0305031JE00000000353654219331034T25365L904",
  "E0004T25365L904E002AXRFT25365L9XFAXABX6HXPIXK61GAT1014T25365L91F4E1109T25365L9XFAXABX6",
  "HXPIXK62FG9E212AYAET25365L9XFAXABX6HXPIXK61GAT1024T25365L904E0051T20100034T2d0FcFE5304",
  "C0034T2eKFe3E6504C0031T20100014T2gHCg045304C006i123030201322230YD230302013222300oaWXeX",
  "Zq+ymWWWamdXWaWqWnwlkeWWWYWWbWakpxoWWWWmWbZvu+kXWWWWetddWWWYYqWYgWmWYYkkddWvubWWWWeYaX",
  "WWW10mWaWmmWWWWWWWYWWWWWWWWWWWW00eWWaWWWWWWWWWYmWYWWWYWWWWWWWWWYmWWmWWWWWWWWWomWWWWWWW",
  "WWWWWWWWWWeeXWeWYWeeWWWmWXWXWWWWWWemWeWWK0XmYiddddWWXWWWWWWWuXcZpppmWWWWWcWfmyyyyWWWWm",
  "eaYW+kkkWXZpkkkWWWkWWWWWWWccXZWWuWkklkWWXyWWg00l//lZ/t/////////w//x/n/x/////////uyl+//",
  "///////+w//////t///////////Zlz/l/x/ll//+//z/z//////k//lm+7myWeWWWWWWWWWbWWaWkWaWWWWWWW",
  "WWdZmXWWWWWWWWWXbWWWWWWeWWWWWWWWWWWymYWmWaWmmWWXWWYWYWWWWWWnWWmlXOa0010"]
@[expose] def ext_full_k512_add_live_m6 : List (SigEntry × Nat) :=
  [(("full_k6_propagate", [i64], [i32]), 112)]

@[expose] def hints : List armIsa.Hints := [hint_full_m6_max_v, hint_full_k6_add_ticks,
    hint_full_k6_init, hint_full_k6_watch, hint_full_k6_assign, hint_full_k6_add_clause,
    hint_full_k6_mtf, hint_full_k6_backtrack, hint_full_k6_propagate, hint_full_k6_ana_clause,
    hint_full_k6_analyze, hint_full_k6_solve, hint_full_k6_flip, hint_full_k512_add_live_m6]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Kitten
