module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Clause

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X7)), (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X20)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X8)), (XRegOrSp.reg (XReg.X4))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X19))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.slot 0 .w64), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.flag LeanQbe.T.Arm64.ArmCond.gt), (.flag LeanQbe.T.Arm64.ArmCond.lt),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.slot 4 .w64)]

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

@[expose] def hint_full_add_clause : armIsa.Hints := _decH #[
  "fV500102030415160507041408092A0971140904040855054B054B054B090508175509070319090A031404",
  "08141C0D12050B0215050B021E1F1B0E0E05053G0G050D0C0859040E082E013E010G130803010C085G0523",
  "090903140408141C0D12050B0215050B021E1F1B0E0E05053G0G050D0C0859040E082E013E010G13080301",
  "0C085G052303130313010A0A1303081B190303030505340402031H070H050507030813037903081739070H",
  "1303690909030A0A0316060816140D12050B0215050B021C151F0C0C0B0B3H0H0B0D040D29060C082C010H",
  "160D0601040D2H0B130316060816190D12040502140405021F141H0F0F05053B0B050D090D29060F082F01",
  "0B160D0601090D2B052603090A0A34041D03043303091D090316060606130308151903030304043A0A0103",
  "1B070B040407030813037903081739070B1606X800160010244I90537H16441024X364I907H0400006X364",
  "I9053X947H19681006X364I9053X947H19681006X364I9053X947H19681045X364I907HYKA05G0002X3J4I",
  "0200017X364I907HYKAYG3YJ907ZG002AX364I907HYKAYL3YJ9YG3YTCYR40AdG000AX364I907HYKAYL3YJ9",
  "YG3YTCYR40AdG006EX364I907HYKAZO5ZCFYL3ZMGZEBYJ9YG3YTCYR40EZiG0073X364I7H0300003X364I90",
  "0300017X364I7H90aV3b19YKA07ZG002AX364I7Hb23YKAb19b8490aV3bAC0AfO000AX364I7Hb23YKAb19b8",
  "490aV3bAC0AfO006EX364I7Hc55bPFb23c3GYKAbRBb1990aV3bACb840EYt00071X360100055X364IdRBdLA",
  "eDH0500007X364IdRBdLAeDHe74eF519701007X364IdRBdLAeDHe74eF519701007X364IdRBdLAeDHe74eF5",
  "197010544IfMAfMJ90046000000000164IfMAfMJ90fK3fJ906XM00294IfMAfMJ90fN3fJ9fT6fK3fV409bM0",
  "0094IfMAfMJ90fN3fJ9fT6fK3fV409bM006D4IfMAfMJ90gQBgE5fN3gOHfJ9gGFfK3fV4fT60DXk600624I90",
  "02000024I9002000154I90hL3fMAfMJ05S00284I90hM3fMAfMJhS6hL3hU908YS00084I90hM3fMAfMJhS6hL",
  "3hU908YS006C4I90iP5iD4hM3iNBfMAfMJiFHhL3hU9hS60CtG006000000344IkN5kH6l9B04000064IkN5kH",
  "6l9Bl3AlB4196010064IkN5kH6l9Bl3AlB4196010064IkN5kH6l9Bl3AlB4196010R04001023ZF630332031",
  "10204316230202211F63033203110204316230202211YJ63033203110204316230202211I4303320020430",
  "223004230202F4303320020430223004230202YJ4303320020430223004230202ZG2230A2301E2210I2210",
  "Y622100YWcWWrgqWWWmkWqaXXZmpmeWZWWXWcWWuWkXeWYWWWqaWWiWWaWuWZWXubWWeWWYmmYYfanWZWWgrgW",
  "WWedWgYWYaaWWzmWWmXuiWXxWXubWWeWWYmmaWZsWWYWdXmWdiWdWqWXWWWgYYWdmWZu+dnyWedkcaXe10YWem",
  "WWWWaWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWeWWWWWWWWWWWWWWWWWWWWXWWWWWWWWWXWaeWWWWYWWWWWWWmWWW",
  "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWXWWaWYaWWWWWWWWWWWWWW00XWaeWWWXYYYWWXWW",
  "WWWWWWWWaeaWmeWXaWWWXWaaYXWWWWnWmYXWWamWWWaWmmeaWWWWWWWmYaWWWWnXXWWWmWeWWWWWYaYWaXWmWW",
  "amWWWaWmmeaWWWWWemeWmaYWWWoWWWWmYYXWmWYWXYWWWWWWeYWWWWeWK0YWaWWWmmmWcaWmWWXmXmWWXYWWWY",
  "aWencaWWWWWWWmWWaeWWWemXYaumWWWWWWYWWWWWWWXWYWWWeeeWZYWeWWWWWWinWWWWuaeWvYaumWWWWWWYWW",
  "WXoaWWWZWnWZaepYWWWWWWWeWWWmXWiZWuaZWZcYWaY00Z//y/td///yxux//z//x/z/////plt+/d/yp///z/",
  "ttxz///+j+/xy//ol///t++/lt//////+lxp///+jyj//+//l/////vtx/tz+l//ol///t++/lt/////c/l+/t",
  "v//+f///+/xxz+//v/zv//////lx//+/Xk7ZWeuWWWZadaWWYWWaWYWWWWWimeXWuWZiWWWYWeeaYWWWXoXWaZ",
  "WWjmWWWeXXWmeWWWWWWXmaiWWWXoZoWWXWWmWWWWWceaWeYXmWWjmWWWeXXWmeWWWWWvWmXWecWWXsWWWXWaaY",
  "XWWcWYcWWWWWWmaWWXW+nO003252"]
@[expose] def ext_full_add_clause : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_add_bin_m6 : armIsa.Hints := _decH #[
  "cE450A0C0K0F0K0H011A140L1B0L0M0M1M010M141B4A450K050H050A0A0A0A0A35050507341D0A04010A17",
  "04040A0A1A1H0D12050B0215050B021N151E0N0N0B0B3G0G0B0D0H0D240A0N082N010G140D04010H0D2G0B",
  "140408141C0D12050B0215050B021E1B1H0E0E05053G0G050D0C0D2A040E082E010G1A0D0A010C0D2G053A",
  "04053B0B1D030B33031D09031303290908151B080D151B1H1F1G140C4A1D1A0D0A1A012D0A0A4A0A1A0A2A",
  "092303030308141508140D1E151B1C1G144A1D1A0D0A1A012D0A0A4A0A1A0A2A032303O001600105A46HAE",
  "HCF856953ACJ4MB0A/C002646HAEHCF856906XC00354669CFAC5305I0008XEHX1B465369XQ5CFAC1A8P101",
  "8XEHX1B465369XQ5CFAC1A8P1035466953CFYBO05M00014J01000064669YBOCF53Y9406XM00294669YBOCF",
  "ACY94YDA53YFH09b600094669YBOCFACY94YDA53YFH09b6006D4669YBOCFZABYU5ACZ8GY94Z0E53YFHYDA0",
  "DXi6006346695303600014J0100014466953YBO04E0027466953CFYBOa94aBC07M0007466953CFYBOa94aB",
  "C07M006B466953b65aQBCFb4GYBOaSHaBCa940Bc6006000000394653dDFdFGcU9dH4dBHd9Bd7509I002846",
  "53dDFdFGcU9dH4dBHd9B08I001000000394669f9CfBGeO3fD4f7Bf55f3E09I00284669f9CfBGeO3fD4f7Bf",
  "5508I00OYT2341483033163243370208318230261242273F83033163243370208318230261242273Y38303",
  "3163243370208318230261242273A63033163240201316230261242F63033163240201316230261242O221",
  "4G2214J2214563033163240201316230261242X12230222300ccagucYWesvgrYbWWWuunhWueXYxYrgXeYee",
  "fufuoWXmWWmZWWiWdWqWXWWWgWWZWWXWcWWuWkXeWYWWWqWWWhWdWW++qWeWeqW10mYYWWWWWWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWXWWWWWWWWWWWWWWWWWWeWWXWWWWWWWWWWWYeWWW00eXXWWWWemeWW",
  "WWWWWXWaaWWWWqYWWWWWWWWWWYaYWeaWWoWWWWmYYXWmWWaeaWmeWXaWWWXWaaYWWmmmYWWWWWXgXbYXaG0YWW",
  "WWWWWWYeWWWWYWWeWWWWWWWWfWWWWWmWWWuWuWWWnWWWXYWaepYWWWWWWWeWXYWWWYaWencaWWWWWWWWWWXWpY",
  "mkkWWWWWWW00d///////llzz////k/l//////zz/tt///+tx//+/+/////vtx/lp/+f///+/xxz+///plt+/d/",
  "yp///z/ttx/++k/x//p//zhzrxyWVmmYYWWWWnWmWWWWWWYYWeeWWWXeaWWXWXWWWWWceaWmiWXsWWWXWaaYXW",
  "WWimeXWuWZiWWWYWeeaWXXnWaWWiWWYqYgaZ/00050"]
@[expose] def ext_full_add_bin_m6 : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_add_bin : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_add_bin : List (SigEntry × Nat) :=
  [(("full_add_bin_m6", [i64, i32, i32], [i64]), 192)]

@[expose] def hint_full_add_unit : armIsa.Hints := _decH #[
  "X7390D09091A08142A0L0M151B081D1G151B1H1F1A0C441D140D0414012D040444041A0A2A092303500160",
  "010024653022004000000294653X3HX5FA9X7AX1BV5TG09I00284653X3HX5FA9X7AX1BV508I00254303314",
  "042302410eWuunhWueXYxYrgeqZem10YWeeWWWWWWWWW80XWaaWWWWoXeYW40eWWWWWWWWfWWWWWWWa00l////",
  "//zz/tt///+xylx/NYYWeeWWWXaZmaW80020"]
@[expose] def ext_full_add_unit : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96)]

@[expose] def hints : List armIsa.Hints := [hint_full_add_clause, hint_full_add_bin_m6,
    hint_full_add_bin, hint_full_add_unit]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_backtrack", [i64, i64], []), 96)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Clause
