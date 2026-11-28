module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Parse

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.gt), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X24)))]

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

@[expose] def hint_full_activate_lit_fid : armIsa.Hints := _decH #[
  "XU3001021324150413031413060703181914272702400010140424035305040A17101305130A0403330A08",
  "0B0C1000040A0D23051E0519093707030A230255500000002581514FR3X1405B00100000084YJB8151YI81",
  "0441107YJB8151YI8Z0EYKC4F107411304001023Y42301122100XuXtZWyWnmYWdWerWaiqfYfmgwqYnXj10e",
  "WWWWWWWWWWWWWXWWWWWWWWWWWWWW00aWeeWYabWYWXYWemWWWWWaWWWWWYW80uWpXWjWWmWWZWWWWWWWWWWmWW",
  "WmWWW00////t/ll/xtn/x/zx/k//////t//+l/x/FeWmmWaekWaWYaWnWWWWWWeWWXmWaWG001220"]
@[expose] def ext_full_activate_lit_fid : List (SigEntry × Nat) :=
  [(("f64u_inv_u64", [i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0)]

@[expose] def hint_full_ingest_cl : armIsa.Hints := _decH #[
  "c631131G1H10070I500D17090806090J001D07000J001D12070J0C0C07060C000D20000806090006090C00",
  "0C0A070D000J070D000000020C0C07060C000D20000806090006090C000C0A070D000J070D0000001J0J17",
  "0000080A2C0J0C0A090C100707290909200J050E00080A2B350A4000000706103000000706103000000706",
  "10300000070614000A1D4000000706140D0557240K0J30130D1544040L0D0J0J1J03040303100A10170A00",
  "27051H19181C1B170E4015100500100J2500004000100020032303V0013001004934F71BG3BE84030094FD",
  "HHI549371BG2Y0eWWWW0M2Y0AN2BE90200BLBME934F71BGDHHI542Y0eWWWW0M2Y0AN10B0100BLBME934F71",
  "BGDHHI542Y0eWWWW0M2Y0AN10B0100BLBME4FDHHI549371BG2Y0eWWWW0M2Y0AN10B0101BLBME4FDHHI5493",
  "71BG2Y0eWWWW0M2Y0AN10B0102BLBME4FDHHI549371BG2Y0eWWWW0M2Y0AN10B0105BLBME934F71BGDHHI54",
  "2Y0eWWWW0M2Y0AN0B0001BLBME934F71BGDHHI542Y0eWWWW0M2Y0AN27CB0207BLBME934F71BGDHHI542Y0e",
  "WWWW0M2Y0AN0B0002BLBME934F71BGDHHI542Y0eWWWW0M2Y0AN27CB020ABLBME934F71BGDHHI542Y0eWWWW",
  "0M2Y0AN27CB0231CLBME934F71BGDHHI54ZE72Y0eWWWW0M2Y0AN1CCm0114671BGaGB4FaHEaI80600007934",
  "F71aGBaHEaI8BG14701007934F71aGBaHEaI8BG14701007934F71aGBaHEaI8BG14701028934F71aGBaHEaI",
  "8BGaL40800018934F71aGBaHEaI8BGaL40800018934F71aGBaHEaI8BGaL40800018934F71aGBaHEaI8BGaL",
  "40800038934F71aGBaHEaI8BGc2408000424F711O20100471BGaGB4F20340202571BGaGB4FcG3105010234",
  "F71d1O03000034F71d1O1L30104000000394FdG4e7Ce9BdI3eB7e58e39e1H09I00284FdG4e7Ce9BdI3eB7e",
  "58e3908I001020230iiermiaWnjngrZXemWWWyWWkWxmWXWdWWaWyeXumZnWdWWXmWcWWWXmXWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWWWWygL0XWaaWWWWWWWWYXWWWmWmWWXWeWaeXWWYWWaWWeWWmWWWWWWWeaWWWWWXWWeeWWmW",
  "WWWeWYYWWaWWmWeeWWWW00mYYWWWWeaYWXemWeeWgWXWmaWYaWmWXWWYWWaWYeWYWmWWYaXWgWYeWoWaaWeeeW",
  "fWamXXWYYXaeaabWaWW00aWWWWWWWWamWWXWWaWWWiWWcWfmWWWZWYWWkWWyWXuWZWWWmWYmWWWmWWWuWWWmWW",
  "WWWWXWWWaWWWWWWWWWWWWWWW00Z//////++/xx////ltx/ikl/ld/h/z+lt/xp+//z//x//t/vl/xu///xtz/Z",
  "/ul+f/vp/ldl/X/ol+i/xvztlttslt//VXXWaaWWWWmeaWpnmWmuWqWYXmeWaiXWWYWWaWWeWcmWadWWWaeYWy",
  "WdmXsWciWmumW+WjmXpWacYemeefmeWW000042045"]
@[expose] def ext_full_ingest_cl : List (SigEntry × Nat) :=
  [(("full_activate_lit_fid", [i64, i32], []), 32),
   (("full_add_clause", [i64, i32, i32, .bool], [i64]), 192)]

@[expose] def hint_full_tumble_finish_fid : armIsa.Hints := _decH #[
  "X7240C0210170504040C141J040A040A393J09193J09193J0919082J09040A1D34092J040D04040C500000",
  "0023437CC70300005437CC7A02Y0X/////VB18501005437CC7A02Y0X/////VB18501006437CC7A02Y0X///",
  "//VB2Y0X/////VE14601000YWWiuWWvXwZqdiWWnWb10mWXYWWWWWWWWXWWXW00eWWnWWWWWWWWemWWm80aeWm",
  "eWeWmXaaWWWW00X//k/+yz/x/t/l/cz/+bFnWXZYWaWeWmWvYWXwG0000"]
@[expose] def ext_full_tumble_finish_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_parse_body_m6 : armIsa.Hints := _decH #[
  "YJ3323000D17051A130374030A1D440D73057003065P1J0J0J030J0P04060L0Q1J0J300306230D14000706",
  "000J031D04030J031D15130C021410050A373J07173J07173J0717082J07030A1D33072J030D03030CK001",
  "30010024F5O02000144FB0E75O144010044FB0E75O144010044FB0E75O144010525O4F192010025O4F3LP1",
  "2030024F5O37L02030024F5O2L12020135O4FXI1397P3030535O4FXU1397P3030A34FYK95O133010034F5O",
  "YK9133010134F5OYK9133010234F5OYK9133010424FYK902000144FYK9ZCCZH004000064FYK9ZCCZH0ZF42",
  "Y0X/////VB186010064FYK9ZCCZH0ZF42Y0X/////VB186010074FYK9ZCCZH0ZF42Y0X/////VB2Y0X/////V",
  "E1370101040510230YWWiuWWvXwZqdiWgYWWWWWWYWWWWWWWWWWWWX/YZYWYrgmWnWL0mWXYWWWWWWWWYWWXWW",
  "mmWWWmWeWemWWWeaWWXWXYWWWWWWe00eWWnWWWWWWWWfWmmmeegWeWeWbWaWrWWaWaWWmWnWWWWaaa00aeWmeW",
  "eWmXaWWWWWWWWWWWWWWWWWWWWWWWWWXWWmWWYWWW00X///k/+yz/x/t/l/b+++/lli/l/Z/n/tsX//n/t/+l+y",
  "////pttVnWXZYWaWeWmWwXXXWmmpWmWyWkWef+WWkWeWXmXZWWWWiee00006204567"]
@[expose] def ext_full_parse_body_m6 : List (SigEntry × Nat) :=
  [(("full_skip_cl", [i64, i64], [.bool]), 0),
   (("full_ingest_cl", [i64, i64], [i64]), 240),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_wstack_defrag_m6", [i64], []), 48)]

@[expose] def hint_full_parse_body : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_parse_body : List (SigEntry × Nat) :=
  [(("full_parse_body_m6", [i64, i64], [i64]), 624)]

@[expose] def hints : List armIsa.Hints := [hint_full_activate_lit_fid, hint_full_ingest_cl,
    hint_full_tumble_finish_fid, hint_full_parse_body_m6, hint_full_parse_body]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_inv_u64", [i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("full_add_clause", [i64, i32, i32, .bool], [i64]), 192),
   (("full_skip_cl", [i64, i64], [.bool]), 0),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_wstack_defrag_m6", [i64], []), 48)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Parse
