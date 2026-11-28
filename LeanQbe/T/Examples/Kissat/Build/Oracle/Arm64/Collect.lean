module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Collect

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X28)), (XRegOrSp.reg (XReg.X2)),
  (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)),
  (XRegOrSp.reg (XReg.X26)), (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X29)),
  (XRegOrSp.reg (XReg.X7)), (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X9)),
  (XRegOrSp.reg (XReg.X10)), (XRegOrSp.reg (XReg.X11)), (XRegOrSp.reg (XReg.X13)),
  (XRegOrSp.reg (XReg.X12))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X0))), (.flag LeanQbe.T.Arm64.ArmCond.gt),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X14))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.flag LeanQbe.T.Arm64.ArmCond.lt),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X29))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.gpr (XRegOrSp.reg (XReg.X26))),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X28))), (.slot 1 .w64),
  (.slot 2 .w64), (.slot 3 .w64), (.slot 0 .w64), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.slot 5 .w64)]

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

@[expose] def hint_full_lit_rank_m6 : armIsa.Hints := _decH #[
  "B500102033000033000000010010001000kXu3000X80YdWy10///yFZG0000"]
@[expose] def ext_full_lit_rank_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_sweep_bins_range_m6 : armIsa.Hints := _decH #[
  "YV340415161718191A130A0B0C13037D030C1E3D0E2B1303030F0F3G0G02032302210H1G0I0E4J1B0K0E03",
  "2K0B0K0E5D130K0K0E0L3L021L010H1K0E2L020M0J0B0J0K0E4D0K0M0J0B0J132E1E030C13037D030C1E3D",
  "0E0303030G030N0E0N0EK0000000094084A5NAC6E7G85OI909000094084I9A5NAC6E7G85O1D9010094084I",
  "9A5NAC6E7G85O1D9010094084I9A5NAC6E7G85O1D9010594084A5NAC6E7G85OI91N90102CXMF40XHNI984N",
  "AA5C6G85OE7XRG1PCYW1104C4084A5NAC6E7XHNY7GXMFG85OI91JC0100ENAA5C684G85OY7G40XHNY8II9Y6",
  "PE7XMF23DEm0201E40XHNY8II984Y6PNAA5C6G85OY7GE7XMF23DE4201F40XHNY8II984Y6PNAA5C6G85OY7G",
  "E7XMFYA31DF4103IYBD40XHNY8II984Y6PNAA5C6G85OY7GE7XMFYA3Z2KYEJ1LIcWW8105F40XHNY8II984Y6",
  "PNAA5C6G85OY7GE7XMFYA31DF4100HYBD40XHNY8II984Y6PNAA5C6G85OY7GE7XMFYA3Z2K0HYWW8002I40XH",
  "NY8II984Y6PNAA5C6G85OY7GE7XMFYA3YBDYEJZ2K0IcWW4004H40XHNY8II984Y6PNAA5C6G85OY7GE7XMFYA",
  "3YBDYEJ0HYWW4004D4084A5NAC6E7G85OI9XHNY7GaBJXMF0D0000D4084A5NAC6E7XHNY7GaBJXMFG85OI91D",
  "D0100D4084A5NAC6E7XHNY7GaBJXMFG85OI91DD0100D4084A5NAC6E7XHNY7GaBJXMFG85OI91DD010102001",
  "0uWYrgmWWWWWXpWWWZWWWekWWzmXmYuWWcZWyWZWiWXgreWXgr90YXWWeXYWWWWWnWaeWWeYameWaYWeWWaeWW",
  "WWXWmWWWWaWnWWWWWmWW00XWmWaWnWWWWaemYaWWaXYeaWnXWaWWYaXaWmaeeaWWaYWemWWWYeWW00XYWeWmWW",
  "YYWWWYWnWWWXWWWWdWWinWmWeWWWXmieWWaWeWWXWWWW00Xy+l/p+y////pk/xt//tzxlt+fz/t//utyt+/oll",
  "t//tv/kl///vl//VZXmWiXZWWWWinWaeWWeYameXsYWeWWdeZeXWjmmeWWecWnmWWWcmWW00003230"]
@[expose] def ext_full_sweep_bins_range_m6 : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 48)]

@[expose] def hint_full_rewatch_range_m6 : armIsa.Hints := _decH #[
  "bK4Q1O1R100S6E460C302A01020038080030000008190909642J0102043404043A0A0A041M00080G0E1B0A",
  "33302A01020038080030000008742J0102043404043A0A0A041M00080G0E1B0A333T2U3V030X00U00000C0",
  "0080B1M0A0D0M0A0A0D0M1J0G0D0J0J0A0A34040A0B080C5A000J0C2J023J0204000C0002080C540A2U0V0",
  "0000C00080B1M0A030M0A0A030M1J0G0D0J0J0A0A34040A0B080C5A00060D0E030C2302330204000C00020",
  "80C540A060D0E260D0EO001000100647CRAO8QFS6X11D60101847CRAO8QFS6X1R6ND08Y00028CRAO8QNDR6",
  "47FS6X1188G1029CRAOXN947ND8QR6FS6X1109Y01109CRAOXN98QNDR647FS6X1308G9X0300CCRAOXN98QND",
  "R647FS6X1XQGXP8XO014CX01039CRAOXN947ND8QR6FS6X109Y00019CRAOXN947ND8QR6FS6X1189Y0102947",
  "CRAO8QFS6X1R6NDXN9109Y01109CRAOXN947ND8QR6FS6X13G089Y0300CCRAOXN947ND8QR6FS6X1ZNGZP8ZO",
  "014CY0104B47CRAO8QFS6X1b1TR6bAX0b8Vb4U0BXy0000147010001C47CRAO8QFS6X1b1TR6bAX0b8Vb4Ub9",
  "30CZy0002F47CRAO8QFS6X1b1TR6bAX0b8Vb4UbBUb93bG8bF00Fdy0000F47CRAO8QFS6X1b1TR6bAX0b8Vb4",
  "UbBUb93bG8bF00Fdy0006J47CRAO8QFS6X1b1TR6bAX0b8Vb4Uc8AbTGbBUc64bUDb93bG8bF00JYvy0007847",
  "8QCRAOFS6X1b1TR608a0000147010001BCRAO8QFS6X1b1TR647b8VdEUbAX00BXw0002ECRAO8QFS6X1b1TR6",
  "47dFVbAX0dEUdJ0b8VdK80Ebw0000ECRAO8QFS6X1b1TR647dFVbAX0dEUdJ0b8VdK80Ebw0007ICRAO8QFS6X",
  "1b1TR647eCAe1GdFVeA4bAX0e2DdEUb8VdK8dJ00IXtY0001060450610370fWYWWXxWWWWdXmWWdiWdWWWWWW",
  "WWaWZsWWWWkZWWkuWkWWWWWWWWkvudWWWdWyXtWkXuZkZmWWZmkWxmWyZmcyZm/oL0aWemWWemeXWeaaWWXWWW",
  "WmWXYmWWmWWnWmYWmeWWYWWWXWWYaWWWWWWaeWWWWWWWWWWWWWYaWWWWWWWWWWWWXWWWW00YWWeWWaeaWmaYYW",
  "WWoWWWYWmmemWWWWemeXWeaWWXaWWWaXXWnWWWWWYaWWWWqWWWWXeWWXYWWWWgWWWWWYmWmXWW00mWYWvYWWWZ",
  "WnWmZaepYWWWWWWeWWXoaWWWcXYWcencaWWWWWWmceuZWWXZmkWpYdWyXcXmWWnudWfpakXuYiXmWW00Z/v//d",
  "//plt+/tvv//+f///x++/k/////c/lz/lp//yp///tzz+z/////xol//+d////yl//zvd///Z/////u/+/z//V",
  "cWWuWWimeXWeccWWXsWWWaXXWnWWWWWvWmYWmiWWZiWWWeYYXYWWWWWajmWWXuWWWWZmWWYcuWWWyWWWWWdWXW",
  "YWW0000B23089ABCD4E"]
@[expose] def ext_full_rewatch_range_m6 : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_rewatch_arena_m6 : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_rewatch_arena_m6 : List (SigEntry × Nat) :=
  [(("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 240)]

@[expose] def hint_full_sweep_bins_m6cf : armIsa.Hints := _decH #[
  "Z028081P1L1O1G191A13070B0C1A0A730A0C1E330E2B1606060F0F3D0D020A2A02211A2A022H1I0R0D0E4J",
  "1B030A0A0E0N3N021N011A0E0N3N021N0H120A0E2N020A0M0A0B0A130A0E44032E1E0A0C1A0A730A0C1E33",
  "0E020A0A0A0D0A0K0E0K0EM00000000840789PBLDOM7FGH908000084078H99PBLDOM7FG138010084078H99",
  "PBLDOM7FG138010084078H99PBLDOM7FG1380105840789PBLDOM7FGH91K80102CXLFH9789PBLM7FGDOXGKX",
  "J640XQD1ACYW1102CXLFH9789PBLM7FGDOXGKXJ640XQD15CYW1104CDOXGKXJ6XLFYGDFG40789PBLM7H914C",
  "0100F40XGKYEIH978YFRYD59PBLM7FGYGDDOXJ6XLF234FX4201FYEIH978YFRYD59PBLM7FGYGDDOXGKXJ6XL",
  "F40234F9201JYJ49PBL78M7FGYGDDOXGKXJ6XLFYI340YQAYMJYEIH9YFRYD51NJbuW0103JYJ49PBL78M7FGY",
  "GDDOXGKXJ6XLFYI340YQAYMJYEIH9YFRYD51NJbuW0105IYJ4YEIH978YFRYD59PBLM7FGYGDDOXGKXJ6XLF40",
  "YI3YQA0IaWWI000JYEIH978YFRYD59PBLM7FGYGDDOXGKXJ6XLF40YI3YJ4YMJYQA0JiWW9005GYEIH978YFRY",
  "D59PBLM7FGYGDDOXGKXJ6XLF40YI314G9102IYEIH978YFRYD59PBLM7FGYGDDOXGKXJ6XLF40YI3YJ4YMJ0Ia",
  "WW9002D40789PBLDOM7FGH9XGKYGDaC4XJ6XLF0D0000DDOXGKXJ6aC4XLFYGDFG40789PBLM7H913D0100DDO",
  "XGKXJ6aC4XLFYGDFG40789PBLM7H913D0100DDOXGKXJ6aC4XLFYGDFG40789PBLM7H913D0105B40789PBLDO",
  "M7FGH9XGKYGDaC40B00000XmWbgrWWWXpWWWWWuWWekWWadWWsWWicWcZWyWZWiWXgreWXgr90maWWWmYaWWWW",
  "XYWWeWnWWYWWYWemXWaWWWWXWeWmWWWWaWnWWWWWmWW00eYWWaeXYWWWWenWWaWemYXaXXWaWmmYXWaWmmWeea",
  "WWaYWemWWWYeWW00aWmWmXWWWaaWWnWWWeWeWWWdWWWZmWYWWWZWWXmieWWaWeWWXWWWW00ldv//tdzv////cz",
  "//t/k/xydzz/t++/xz/t++//llt//tv/kl///vl//VucWWeuYcWWWWvYWWeWnWaZuYYWeXXWaYWeXXWWmmeWWe",
  "cWnmWWWcmWW000042308"]
@[expose] def ext_full_sweep_bins_m6cf : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 48)]

@[expose] def hint_full_sweep_bins : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_sweep_bins : List (SigEntry × Nat) :=
  [(("full_sweep_bins_m6cf", [i64], []), 96)]

@[expose] def hint_full_sweep_copy : armIsa.Hints := _decH #[
  "d6651P1F1L1J0303030A0A0A0B0D0C5G0G480G480G48000G0C1E0D5G000E0D0A0K0A1I0K1N0N0N0B5G0404",
  "0E2912040E2402240B013A180E1202020D2A3J03030808040D0D0C1D1N0B1M0G090M1G0G090M1I191K0I0I",
  "0G0G3L0L0G0B0N0B230D0I0C2I020L130B03020N0B2L0G2A03030C1D190B1M030G0M13030G0M1N13140N0N",
  "0G0G3K0K0G0B090B2G0D1A0A0N0C2N020K1A0B0A02090B2K0G1A0A2A0A040A0A0C1J130A0A0A08083G0G02",
  "0A1D0E0A08080E030C13037D030C1E3D0E0A1A0A732A0H020A0A0D0C1D1G0C0D1G0B18041J191K0G0N4D1B",
  "1D0B0D1D022B0D0D4D0D1D0D2D0A2A0AS001D0010137DL3OA103110037DL3OA103110037DL3OA103110544",
  "0CPA5631A40100BEFY7IIJY8K40CPA5637DYCNGL2A8Be0201FYEAEFY7IIJY8K40CPA5637DYF8YJGYCNGLYK",
  "40Fom0003CEFY7IIJY8K40CPA5637DYCNGLYF81ACe0100ECPGLIJEFY7IY8K40A5637DYF8YEAYJGYCN0Eam0",
  "008640ZLX2ZT8ZTX3ZPJZPX406XU00014X5010001740ZPJZPX4ZT8ZTX3ZLX2ZR307ZU002A40ZPJZPX4ZT8Z",
  "TX3ZU4ZR3a3DZLX2a5N0AhU000B40ZPJZPX4ZT8ZTX3ZU4ZR3a3DZLAZLX2a5N0BxU006E40ZPJZPX4ZT8ZTX3",
  "b0GaK9ZU4aULZR3aMKZLX2a5Na3D0EYyU006140010000240ZLX2022001640ZLX2ZPJZPX4ZT8ZTX306XU002",
  "940bSAZT8ZTX3c1DZLX2ZPJZPX4c3909dE000940bSAZT8ZTX3c1DZLX2ZPJZPX4c3909dE006D40cUGcI3bSA",
  "cSKZT8ZTX3cK4ZLX2ZPJZPX4c39c1D0DXxO009440e7Je24ePA040000640e7Je24ePAeJGeR81D60100640e7",
  "Je24ePAeJGeR81D60100640e7Je24ePAeJGeR81D601070000003940fU3gN9gPKg5AgQGgLJgJ4gI809I0028",
  "40fU3gN9gPKg5AgQGgLJgJ408I00QaQ233F3232G323116230702057162702G22F3F230702057162702G22F",
  "3Y3230702057162702G22F3E2307020570227002270F2307020570227002270YB230702057022700227062",
  "211YQ22700ZZYbiZXWahibfYYmWcvaoemXmWbgrWWWaZmbWXWXWuWWeXmXWiWdWqWXWWWgWeWcWWYWiWXmWyYm",
  "WaWWXeWdiWWXuWuiWhWZmYeWZuWW+dnylWWWgL0mYaWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWWYWWaYXWWgWWWWYWWnWWWWWWWWWW00aWmmWWWeeaYmWWWWWeXYWWWWemmmWWeWWWWXYXWaY",
  "WWWoWWWWmYYXWmWWWemeXWmWYeWWWYWeeaYWWWgnWWoXWmmXWXWWXWWemWWWWWYaWW00XWWWWWWWWXaWWWWWmW",
  "eWWWWWmXWWWaaaWXnWaWWWWemWWWnWWaepYWWWWWWWeWWYaWWWaeWnYieWWWWWWXWZaWWWuWeaWXWXmiXWWeWe",
  "ZWucXWXsW00l//////tt++////lltu//////dzv////c+c///l////yxz/tv//+f///+/xxz+////c/lz+l/vd",
  "///x/lltx///Wy/+hz++/z/z//y//kl/////vt//VeeXXWWWWmmedWWWWWWuYcWWWWvXvWWWmWWWWZaYWecWWX",
  "sWWWXWaaYXWWWWvWmYXmWcuWWWaWmmeaWWW/ZWXqYXXWYWYWWZWWnmWWWWWceWW00040"]
@[expose] def ext_full_sweep_copy : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_rewatch_arena : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_rewatch_arena : List (SigEntry × Nat) :=
  [(("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 240)]

@[expose] def hint_full_move_red_pass2_m6 : armIsa.Hints := _decH #[
  "XA6017160D0D0B1P0N0F3K0K0K050L0L0B0C140804092929240J080C1E480J0E1B38080E250P0F1I0E0M0A",
  "7034O5A7X50300009C7E68GA05A4O7X563GD1I90101EA05A8G4O7X563IIRKLFGDJPC7S5E60Ee0000GC7S5E",
  "68GIILFRKULKNA05A4O7X563GDJP1JGX0100GC7S5E68GIILFRKULKNA05A4O7X563GDJP1JGX0100GC7S5E68",
  "GIILFRKULKNA05A4O7X563GDJP1JGX0105DC7E68GA05A4O7X563IIRKLFGDJP0DXW00030200752306YO2260",
  "0aWeZWyeXuWXpcWWWdWWL0aWWeXXWXYWWWWXWWWW00YWWaWmmWnWWWWamWWe00XWiWWWWmWWWWapWY00zv//t+",
  "+l+y////o///lVYcWWeXXmXZWWWWjWWWm00013230"]
@[expose] def ext_full_move_red_pass2_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_move_red_end_buf_m6 : armIsa.Hints := _decH #[
  "ZU56151I1F0E3909033L0L0J1B0B0N0N0B0C180G080K2K2K28040G0C1E4G040E1B0B540G0G0E2401240402",
  "08080E230P0N0N0B0C180G080K2K2K28040G0C1E4G040E1B000B035804040E28012808023G0E03002A0E23",
  "0O0605050B1I0K0P3909090F0N0N0B0C180G080J2J2J28040G0C1E4G040E1B3G0G0E2F0I0P1L0E0E0AO037",
  "D4R672A03020077D964R67DIB5FF3AP07030197D964R67DIB5FFHASJ2P090201CJ07D964R67DIB5FFHASJI",
  "PM30CYW0001EJ07D964R67HASJIPM3DIB5FFX1NQL0Eee0000FJ07D964R67HASJIPM3QLX1NL9DIB5FF14Fu0",
  "100FJ07D964R67HASJIPM3QLX1NL9DIB5FF14Fu0100FJ07D964R67HASJIPM3QLX1NL9DIB5FF14Fu0106EJ0",
  "7D964R67HASJIPM3DIB5FFX1NQL18Eee0101FJ07D964R67HASJIPM3DIB5FFX1NQLY180Fee0004FIP7D964R",
  "67HASJJ0DIB5FFL9YRNM3QL0FuW0000FYRNM3QLIP7D964R67HASJJ0L9DIB5FF14F6100FYRNM3QLIP7D964R",
  "67HASJJ0L9DIB5FF14F6100FYRNM3QLIP7D964R67HASJJ0L9DIB5FF14F6105BIP7D964R67DIB5FFHASJJ00",
  "B0001FIP7D964R67HASJJ0DIB5FFL9YRNM3QL1GFuW0101GIP7D964R67HASJJ0DIB5FFL9YRNM3QLZTG0GuW0",
  "00534RaQA670300009aTOaU67DaS3aQA4R67aR0b051L90101EaS3aQA7D4R67aR0b2LbB9b5Pb05b3IaTObCF",
  "aU60Ee0000GaTObCFaU67Db2Lb5PbB9bENb4KaS3aQA4R67aR0b05b3I14GX0100GaTObCFaU67Db2Lb5PbB9b",
  "ENb4KaS3aQA4R67aR0b05b3I14GX0100GaTObCFaU67Db2Lb5PbB9bENb4KaS3aQA4R67aR0b05b3I14GX0105",
  "DaTOaU67DaS3aQA4R67aR0b2LbB9b5Pb05b3I0DXW0001040350870YWaXmkaWyWWvpWWWZmWWWWXucZWlWWmZ",
  "mWZciWWWiWWicW+WeXuWXpcWWWYdWYL0YWWaWmmWnWWWWWmWWWWmXWYWmeWWWYWYaWWWWYWWmaXWmWXXWXYWWW",
  "WXXWWWW00XWWYWeeWemWWWYeWWaWeWmXWeaWWnXWXYWWWWfWWeYWmeWammWnWWWWamqWWe00mcWWWWeWWWWYfm",
  "XWWWWuoXWdWWWWWXWWWWWeaWXaYWkWWWWWmWWWWaWpaW00ky//x/ld/kl///vl//t/d+lz/lt/+zy/zv////b/",
  "/dx+/l/s+l+y////o+t//lVXZWWaWmuWnmWWWcmWWeWuXmYWmeWXYZWYcWWWWwWWuaXWmWfXmXZWWWWjXeWWm0",
  "00042308"]
@[expose] def ext_full_move_red_end_buf_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_move_red_end_m6 : armIsa.Hints := _decH #[
  "S4D0E543808081B040G0A0E121A0X60G1A0X60E5G28080A0G0A0E1A0D1D4000000004405J638D1G4010044",
  "05J638D2AG4020545J40638D1A40101020F10nWaWjumeeWakuH0YWWWWWWeWWW00XWWWbXYaWWW40YWeauWWW",
  "Wnce00d//y///qihol//NZWWWhpqjmWW80000"]
@[expose] def ext_full_move_red_end_m6 : List (SigEntry × Nat) :=
  [(("full_move_red_end_buf_m6", [i64, i64, i64, i64], []), 48)]

@[expose] def hint_full_arena_sweep_m6 : armIsa.Hints := _decH #[
  "a92X01T1R1U1V100X11002170B0E0B2A0M23301B0M00000M0D0E220A101B0A00000E3A331B0A0003000E2E",
  "7J0M2Q3D080G0408000M293808080M1B041E200B080E04040404041I1B0M0D0J0M12020202000G09097B0J",
  "0B440D0D0E2401240402080B1B0G0G080E1B0B0L0K020O0N4700070E7E80020E1E4023030O000O0E481D0D",
  "7G000C1M3G0M100B1000P00100010074S6X0HX1EVAR8TCU27Q7020486X0M7EV4SHX1AR8TCU20Q8020074S6",
  "X0HX1EVAR8TCU07000084S6X0HX1EVAR8TCUM720D8020796X0M7XEQEV4SHX1AR8TCU1090100A6X0M7XEQEV",
  "4SHX1AR8TCUXI00Am0002B6X0M7XEQEV4SHX1AR8TCUY03XP00Bm000244SY8X76X0HX177OQULRV4070084SY",
  "8X76X0HX1EVAR8TCU767OKNLP8070084SY8X76X0HX1EVAR8TCU767OKNLP80702IYC7YDOYEKYFNYGLYHP4SH",
  "X16X0EVY8X7YMQARYB68TCUYQDYIJ14IYYW0113KYSGYT4YC7YDOYEKYFNYGLYHP4SYMQ6X0YB6YQDHX1EVYIJ",
  "AR8TCUY8X718Kam0100KYC7YDOYEKYFNYGLYHP4SHX16X0EVY8X7YMQARYB68TCUYQDYIJZE8YT40KYYW0009H",
  "YEKYGLZSIYHP4SY8X76X0HX1EVAR8TCUa80YC7YFNYDOYMQ0HYaW0001LYEKYGLZSIYHP4SY8X76X0HX1EVAR8",
  "TCUa80YC7YFNYDOYMQaB9a9GYB6aKJ18LgaW0101MYEKYGLZSIYHP4SY8X76X0HX1EVAR8TCUa80YC7YFNYDOY",
  "MQaB9a9GYB6aKJaM80MgaW0007CZSIYHP4SY8X76X0HX1EVAR8TCUa80YC74OKNLCXW04037cDV4SY8X7c77cC",
  "RcAUc9Q070000AcDV4SY8X7c77cCRcAUc9Qc8O6X0HX10A000684ScAUc9Qc776X0cDVY8X7cCR1O801015cDV",
  "4SY8X7c77cCR0500006cDV4SY8X7c77cCRd581G601006cDV4SY8X7c77cCRd581G601006cDV4SY8X7c77cCR",
  "d581G6010B020E7Z42353Y4A30H31I32J34K33LOA2H02J22L32K42I13A2H02J22L32K42I10A2H02J22L32K",
  "42I1XTA2L32H02I12J22K4082L32H02I12J2082H02I12J22K4082H02I12J22K4Z120170eXmWbgrWreWXtWe",
  "WXWWWWWWmWWeWcZWkWbxmWWWYWWWuWmkuWzmWWWXkuWXeWWWYzmWWmngL0mYaWWWWWWeWWaWfeYWWmWWYWXWYW",
  "meWWmWWWWWWWWaYWWWWWWWWYWaWXWaXWaWWWWXaaWW00XWeXYWWWWWWaWWYWaaXWWeWXXWWoXWeaWaeWWbgeqW",
  "WYXXaWYWWaaXWYWWmYWmYeqWaaoYWW00mXWWWaWWXWpWWWWWWWYWWWWWWWoXWcWWvoWWcWWaWeWXceWimWWeWc",
  "eaWWWWYWimWWWWW00lz/dzv//////p//x/ttz//lxry/+xz/lt/tl//mZct/pxzzmkv//pty/x/+lx+/uct/ps",
  "hx//VYWuYcWWWWWWiWWaWeeYWWmagZWXaYWmeWemWWlyveWiaYYlncWWieZWaWXmaXWdveWifqaWW0006B2308",
  "9ABCD4E"]
@[expose] def ext_full_arena_sweep_m6 : List (SigEntry × Nat) :=
  [(("full_sweep_bins_range_m6", [i64, i64], []), 80),
   (("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]), 192),
   (("full_move_red_end_m6", [i64, i64, i64], []), 64),
   (("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 240)]

@[expose] def hint_full_mark_reasons_m6 : armIsa.Hints := _decH #[
  "V33021J1K1N1813191L1D0D130M3303030E2G0B130M030G0C2G040G0G0D030M3000000018G85AMLENCKK9A",
  "J401D801019G85AMLENCKK9AJ40TD0900000cWYZWiYgrgH0aWWmmmeWWWWW00YWWeeeaWeWWW40YaWWWaWWWW",
  "00Zu//dllt/l///NdWWummeWmWWW80000"]
@[expose] def ext_full_mark_reasons_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_arena_sweep : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_arena_sweep : List (SigEntry × Nat) :=
  [(("full_arena_sweep_m6", [i64], [i64]), 384)]

@[expose] def hint_full_mark_reasons : armIsa.Hints := _decH #[
  "V33021J1K1N1813191L1D0D130M3303030E2G0B130M030G0C2G040G0G0D030M3000000018G85AMLENCKK9A",
  "J401D801019G85AMLENCKK9AJ40TD0900000cWYZWiYgrgH0aWWmmmeWWWWW00YWWeeeaWeWWW40YaWWWaWWWW",
  "00Zu//dllt/l///NdWWummeWmWWW80000"]
@[expose] def ext_full_mark_reasons : List (SigEntry × Nat) := []

@[expose] def hints : List armIsa.Hints := [hint_full_lit_rank_m6,
    hint_full_sweep_bins_range_m6, hint_full_rewatch_range_m6, hint_full_rewatch_arena_m6,
    hint_full_sweep_bins_m6cf, hint_full_sweep_bins, hint_full_sweep_copy,
    hint_full_rewatch_arena, hint_full_move_red_pass2_m6, hint_full_move_red_end_buf_m6,
    hint_full_move_red_end_m6, hint_full_arena_sweep_m6, hint_full_mark_reasons_m6,
    hint_full_arena_sweep, hint_full_mark_reasons]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 48),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Collect
