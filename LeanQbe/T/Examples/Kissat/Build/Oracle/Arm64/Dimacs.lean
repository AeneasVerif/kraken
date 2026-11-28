module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Dimacs

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X4)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X2)),
  (XRegOrSp.reg (XReg.X3))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X1))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.flag LeanQbe.T.Arm64.ArmCond.lt), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.flag LeanQbe.T.Arm64.ArmCond.gt), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X13)))]

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

@[expose] def hint_kissat_is_ws : armIsa.Hints := _decH #["41001020000000000020JC0000"]
@[expose] def ext_kissat_is_ws : List (SigEntry × Nat) := []

@[expose] def hint_kissat_is_digit : armIsa.Hints := _decH #["2110200000000010160000"]
@[expose] def ext_kissat_is_digit : List (SigEntry × Nat) := []

@[expose] def hint_kissat_skip_ws_comments : armIsa.Hints := _decH #[
  "E23140506020507011304010701134001100100150111010115011101021501110100000aWYYW00YXXXe10",
  "00XxzzzpTaYYYi20000"]
@[expose] def ext_kissat_skip_ws_comments : List (SigEntry × Nat) := []

@[expose] def hint_kissat_skip_ws1 : armIsa.Hints := _decH #[
  "N34080506050206050306090602090403150605020604032001100104250411420100010XXWWYWem00mmXX",
  "Wae4000X+ldz+lppNXmuYXmii80000"]
@[expose] def ext_kissat_skip_ws1 : List (SigEntry × Nat) := []

@[expose] def hint_kissat_read_nat : armIsa.Hints := _decH #[
  "N35080909040209050324040602010402010904090A050330011001021502591020025041259202000XWWW",
  "WWWW10XWWXWWe00oWmmaa40mWWWW00/+f/cltpNXsWvmei80000"]
@[expose] def ext_kissat_read_nat : List (SigEntry × Nat) := []

@[expose] def hint_kissat_parse_header : armIsa.Hints := _decH #[
  "ZS331506090206070113050107011318050B0118050605020601031506050206010301020502050B150B15",
  "0B0108050605020601031506050206010305080909010209050321010602060102060901090A05034C0108",
  "05060502060103150605020601030508090901020905032101060200010200011901090A050321G0011001",
  "00264501120100264501120101264501120102264501120105264500200022645011201082506402000225",
  "06411201032645002000226450259202002645025920205364Z8C5003000235064Z8C1130105264Z8C2592",
  "0200364Z8C50259302000YWWWeWWWWWWWWWWWXYWWWWWWWWWWWWWWYaWWWWWWWYWWWWWW00eWWaaWXWWeeWXWW",
  "WYWWYWWmWaaWWmWWWWWeeWXWWWaWYYW00amWYYWmmmaaWemeWXaXXWeeeYYWaeaenamaaWemefYXXXe10aWWWW",
  "WWWWWWWWWWWXWWWWWWWWWWWWWWYWWWWWWWWWWWWW00d///ol/yv++k/pv/ldl/yp+i/ldlvy/tptkzo/pv/ldl",
  "jxzzzpTjmWZcXXnWicWmumWZiXpWmumcZWeienYjWicWmumoaYYYi20000"]
@[expose] def ext_kissat_parse_header : List (SigEntry × Nat) := []

@[expose] def hint_kissat_next_lit : armIsa.Hints := _decH #[
  "YB3403150609020607041305040704131805070909050209050324040602010402010904090A0503410704",
  "03010104080909050209050324040602010402010904090A050341070403010101B0011001002415014201",
  "00241501420101241501420102241501420105150010001150259102002504125920207150010002150259",
  "1020025041259202000nWWWWWWWWWWamWWWWWWWWWWWWW10XWWXWWeWWWWWmWWmWaWWmWeeW00oWWoWmmaaaWa",
  "mWfWeeYYXaeaabW40cWWWWmWWWWWWmWWWeWWWWWWWWWWW00/+Z/+f/cltpt/m//a/pdxvztlttslNXyWXsWvme",
  "ieWlWWxWiuacYemeefm80000"]
@[expose] def ext_kissat_next_lit : List (SigEntry × Nat) := []

@[expose] def hint_kissat_check_model : armIsa.Hints := _decH #[
  "ZC6D02310B210316090C020907011306010701131806070C0C06020C010321010902090102090C010C0A06",
  "03010703010101080C0C06020C010321010902090102090C010C0A0603010703010101170701060606270E",
  "0F0G0F0H06020103150609020607011305010701131B01H001100102250640200006506475AD2Y0eWWWW0I",
  "2Y0AJ1H6010195064HH75AD2Y0eWWWW0I2Y0AJ2Y0eWWWW0K2Y0AL1F90100A506475HHIFAD2Y0eWWWW0I2Y0",
  "AJ2Y0eWWWW0K2Y0AL11A0100A5064HHIF75AD2Y0eWWWW0I2Y0AJ2Y0eWWWW0K2Y0AL11A0100A5064HHIF75A",
  "D2Y0eWWWW0I2Y0AJ2Y0eWWWW0K2Y0AL11A0101A5064HHIF75AD2Y0eWWWW0I2Y0AJ2Y0eWWWW0K2Y0AL11A01",
  "02A5064HHIF75AD2Y0eWWWW0I2Y0AJ2Y0eWWWW0K2Y0AL11A0105A5064HHIF75AD2Y0eWWWW0I2Y0AJ2Y0eWW",
  "WW0K2Y0AL0A0001A5064HHIF75AD2Y0eWWWW0I2Y0AJ2Y0eWWWW0K2Y0AL26CA0207A5064HHIF75AD2Y0eWWW",
  "W0I2Y0AJ2Y0eWWWW0K2Y0AL0A0002A5064HHIF75AD2Y0eWWWW0I2Y0AJ2Y0eWWWW0K2Y0AL26CA020C250641",
  "12010025064112010125064112010225064112010508330301312323222210220372210042102320cWWWWW",
  "WWWWWWWWWWWWWWWWWWWWWWWWWWWk00eWaaWWYYWWWWWWWeWYYWWaWWWWaWXXWWYWWeWaaWWWW20aYYYmYXWWeX",
  "eWgWamXXWYYYWYmYeWmmXXWoaYYYmYXWG0uWZWWWaWWWWWWWeWWYWWWWWWWWWWWWWWW00Zttxxxdxyljlyl/Z/",
  "ol+i/xvx/u/vd/clzy+xtxxxdxz+VeeaaauaZmomZmWyWjmXpWacaWdWcuWvmYZXaeaaauaYX00040"]
@[expose] def ext_kissat_check_model : List (SigEntry × Nat) :=
  [(("kissat_parse_header", [i64, i64, i64], [.bool]), 0)]

@[expose] def hint_full_skip_cl : armIsa.Hints := _decH #[
  "YD4403150609020607041305040704131805070909050209040324040602060402060904090A0503040705",
  "03040404080909050209040324040602060402060904090A0503040705030404041707B001100100441502",
  "Y0eWWWW0C2Y0AF040000441502Y0eWWWW0C2Y0AF1440100441502Y0eWWWW0C2Y0AF1440100441502Y0eWWW",
  "W0C2Y0AF1440101441502Y0eWWWW0C2Y0AF1440102441502Y0eWWWW0C2Y0AF1440105441502Y0eWWWW0C2Y",
  "0AF040001441502Y0eWWWW0C2Y0AF25940207441502Y0eWWWW0C2Y0AF040002441502Y0eWWWW0C2Y0AF259",
  "40200030aWXXWWYWWWWXWWeeWWmWYWXXWW00XeWfWYeWmmXXXWXaWoWaaWeeanWmmqWG0ZWWWYWWWWWWWaWWWm",
  "WWWWWWWWWWWW00Xyl/X/vd/clzyz/yd+f/vp/ldsz+++v+VZmW+WcuWvmYZYWZuXsWciWmufYXXXcX00000"]
@[expose] def ext_full_skip_cl : List (SigEntry × Nat) := []

@[expose] def hints : List armIsa.Hints := [hint_kissat_is_ws, hint_kissat_is_digit,
    hint_kissat_skip_ws_comments, hint_kissat_skip_ws1, hint_kissat_read_nat,
    hint_kissat_parse_header, hint_kissat_next_lit, hint_kissat_check_model, hint_full_skip_cl]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Dimacs
