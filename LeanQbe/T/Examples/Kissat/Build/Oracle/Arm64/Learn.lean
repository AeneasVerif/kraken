module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Learn

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X1)),
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X7)), (XRegOrSp.reg (XReg.X6)),
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)),
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)),
  (XRegOrSp.reg (XReg.X26)), (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28)),
  (XRegOrSp.reg (XReg.X29))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X1))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X29))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X22))), (.slot 1 .w64),
  (.slot 2 .w64), (.slot 0 .w64), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X15))), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.flag LeanQbe.T.Arm64.ArmCond.gt),
  (.gpr (XRegOrSp.reg (XReg.X14)))]

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

@[expose] def hint_full_det_new_level : armIsa.Hints := _decH #[
  "830010002031405061001600101040010120e1000X4000XyiNZp80000"]
@[expose] def ext_full_det_new_level : List (SigEntry × Nat) := []

@[expose] def hint_full_one_lit_confl : armIsa.Hints := _decH #[
  "d72718160129090610053A0608080B8C003000010D05030C0D0E010E06010E010E4F0541100DAG0H3F0I05",
  "6C0C3C0D0F0E0H051B3J02043K0403040D040B0403040D140J0303020H0L0B1D030F0D03030F0D1M0N0F0M",
  "0M03033O0O030B0L02500H0002200130010O000200010L025O033D02100100020614050014060600021013",
  "0210230B1O0H1F1E1N130L401B100B0010012B00002130001000200626062A2P063806370208070001160D",
  "01050Q0A08160106020014050010000B160A361B040B00180606140214130214230B1F0C1H1E1N130L441B",
  "140B0414012B0404213000100020062606U00160010254RQ8NA67E94HSTU5K400567Q84RNAE95HE64F5O50",
  "1667Q84RNAE9X0F4HE646O40484RQ8NA67E9Y0SY1TY2U08K00154RE9Y2UY0SY1T05200084RQ8NA67E9Y0SY",
  "1TY2U1P8K100B4RYNINA67Q8Y0SY1TYHGE9YDPY2U1QBi6100B4RQ8YDPYHGNA67E9YNIY0SY1TY2U3FEHBcO3",
  "529YNI4RQ8NA67E9Y0SY1TY2U09X9002E4RYNIQ8NA67Y2UY0SY1TYHGE9ZAQZFJYDPZLK0EguA001E4RYNIQ8",
  "NA67Y2UY0SY1TYHGE9ZAQZFJYDPZLK0EguA002DYNI4RQ8NA67Y2UY0SY1TYHGE9ZAQZFJYDP0DYu900014R01",
  "0001EYNI4RQ8NA67Y2UY0SY1TYHGE9ZAQZFJYDPa140Egu9002HYNI4RQ8NA67Y2UY0SY1TYHGE9ZAQZFJYDPa",
  "2Ja14a7La6H0Hwu9000HYNI4RQ8NA67Y2UY0SY1TYHGE9ZAQZFJYDPa2Ja14a7La6H0Hwu9006LYNI4RQ8NA67",
  "Y2UY0SY1TYHGE9ZAQZFJYDPaV3aKNa2JaTOaLFa14a7La6H0LhYu900944RE9Y2UY0S10421020000003C4RY2",
  "CY2Ud9EdBNcL6dD3d7FE9cJ4d5Hd4O0Cv0002A4RY2Ud9EdBNcL6dD3d7FE9cJ4d5H0AiG00154RY2Ud9EdBNc",
  "L605G00274Rf77f68eQPeNAeV8f4707ZU00244RfFQfH8fGA104A10234RfFQfH810321110000003B4RfFQh4",
  "Eh6NgF6h83h2HgC0gD8h0CgVF0BiI002A4RfFQh4Eh6NgF6h83h2HgC0gD8h0C0AiI00154RfFQh4Eh6NgF605",
  "I00702031XR6314321300cU221262241A224102250YM22500iiageucYWesurfZeqeWtaWWmYWWeXvvsWWiia",
  "geucYWesurfZeqWWeXWYWmWXxWWWWdXmWWzmWyWWWWWWWWmWWWyWyWWyyXvx+WmWWWWXvuWyeuL0YWWWWWWWWW",
  "WWWWWmYYWWWWWWWWWWWXWWYWWWemeXWeaWWWaWWWYWWaeWWWWnWWWXYWWWWWWWaWmWWWWWWWWWW00YWWeXXWWW",
  "WeYXWWWWmWYeXXYWWWWWWWWWWYWWeXXWWWWeYXWWXaemWWWWWaeaWmaYWWWYeWWWeYYXYWYWemWYWnWWWeWWWY",
  "aeWWXeWWmXWY00aWWWWWWWWWYeWWXWWYWZmWWWWWWWWyyWWWaWWWWWWWWWYeWWXWWaWWWWWWWWWvYWWWZWnWWi",
  "nYieWWWWWXWXWWeiWiWWkiWyuWWWWWWWWyuciWW00X//////x/llzz////lxz/r/+/uvkXzwd/////////x/ll",
  "zz////lxz/yitk//////plt+/tv///vd///lxxzx/v/kl/u+yp//l///xtchWXl/+/ylxVaWmmYYWWWWmaYWgW",
  "XWdcn+YbuWWWWWWWWWaWmmYYWWWWmaYWZpenWWWWWWimeXWecWWWcuWWWmaaYaWcWnmWdXZiWWmWWWaevq/+mW",
  "XWZma0003B67839ABCDEF"]
@[expose] def ext_full_one_lit_confl : List (SigEntry × Nat) :=
  [(("full_backtrack_ac_fid", [i64, i64], []), 96),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_unwatch_large", [i64, i32, i32], []), 0)]

@[expose] def hint_full_eager_subsume : armIsa.Hints := _decH #[
  "ZF34131R1E1V1X0181F0B023C5C5C5C2H0C02153C2H059M0B0M0H0C0X107070A3N111B0N0D0H0X10X20B6L",
  "2L0B0O050C012H05110X20B4C0C0L0L0D1L0X30C3L0B1C010H050A0H0H0N0H0B0H0H0H1X40D1B023H5H5H5",
  "H260H02153C2605430B24160D1D060216067406021D340D0D2634230B06R00000000ALFBR46DE7493J8HX0",
  "FV5U0A0000ALF7493BR46DEJ8HX0FV5U1HA0100ALF7493BR46DEJ8HX0FV5U1HA0100ALF7493BR46DEJ8HX0",
  "FV5U1HA01055LF7493DE5U1050100ALFBR46DE7493J8HX0FV5U2X40A0200BLFBR46DEJ8HX0FV74935UY2X4",
  "10B0106HY30LFBR46DE7493Y2X4Y6MJ8HX0FVYNNYD7YEAYIN5U1CHXme0100IY30LFBR46DE7493Y2X4Y6MJ8",
  "HX0FVYNNYD7YEAYIN5UYRX23COHIXme0301JY30LFBR46DE7493Y2X4Y6MJ8HX0FVYNNYD7YEAYIN5UYRX2YVH",
  "2COJXme0205ELFBR46DEJ8HX0FV74935UY2X4YNNYD7YEA0EeW0000IY30LFBR46DEJ8HX0FV74935UY2X4Y6M",
  "ZIX2YNNYD7YEAYIN1HIcaW0101JY30LFBR46DEJ8HX0FV74935UY2X4Y6MZIX2YNNYD7YEAYINZKH0JcaW0005",
  "BLFBR46DEJ8HX0FV74935UY2X40B00023DE5UaN00300006aN0LF7493DE5U16601006aN0LF7493DE5U16601",
  "006aN0LF7493DE5U16601052DE5U0200012DE5U14201002DE5U246202003DE5Uc0614301022DE5U1420100",
  "2DE5U14201002DE5U14201062DE5U1620103H2302fH2220G22200XscWZWWgrgWWWZXmWxWWjxkxsuWWWWWWW",
  "adWmZmWWWWcyWWXYyWWj+WxWWjxkxsuWrgL0mWWnWaeWWWWYaWeYeWaeWWWWWWaeWYWXWXWaaWWaeWWWWXYaeW",
  "aYWWeWaeWWWWWWaWW00eWWemYaWWWWnYWaWaWYaWWWWWWoaWXWWmmmYYWXYaaamWenYaWYXWWaWYaWWWWWWoWW",
  "00oWWXWYWWWeeWXWmWfWYavcfoeWWWWYWWWXmXXmWWWWYiWeWWimWaWWfWYavcfoeWWW00/X//klxp///+jv/t",
  "/p/xp/////+hp/z/+k+/xx/zxppo//kjxt/uz//p/xp/////+h//V+WWnmaiWWWXocWeWiWaiWWWWWXqiWYWXn",
  "XWaaWYaiijWWnoaeWdYWWiWaiWWWWWXqWW000146783"]
@[expose] def ext_full_eager_subsume : List (SigEntry × Nat) := []

@[expose] def hint_full_learn_clause_m6 : armIsa.Hints := _decH #[
  "bL381L1Q0R1601023N0N032O120E2H0H0C2C054F051606062P0P1602040P0106020413050G260406061405",
  "1614060D160B160406061405110B060B260B100I610D0101310B060B060B060B101A01060B0B160D162404",
  "04010604040B1306361B030B041P06061302131H02031H0B1O0F1C1E1N1H0L431B130B0313012B03032134",
  "0414042406260616010601100500360B0606100210140200140B130H1F1C1E140N401B100B0010012B0000",
  "40001000200626061601M0016001016475IBQCR9L780680007789L47E65IBQCR1F7Y0101A78PO9L47E6HFK",
  "N5IBQCR13Ao2100A789L47E65IBQCRHFKNQ30Ag00036475IBQCRXOP781G68102747BQCRY1GXOP785I07400",
  "0747BQCRY1GXOP785I074002747BQCRY1GXOP785I074006747Z6IBQCRY1GXOP7820A7A200647XOP78ZB0BQ",
  "CR06X0002847Z6IBQCRY1GXOP78ZCA08A001847Z6IBQCRY1GXOP78ZCA168A108547ZB0CRXOP78054002447",
  "ZB0CRXOP1444115C47ZB0CRbLEbNNb26bPHbJCaV4b0PbHFbGO0Cv4002B47ZB0CRbLEbNNb26bPHbJCaV4b0P",
  "bHF0Bv4001647ZB0CRbLEbNNb2606X4001347CRBQ1032103147010003947CRe3Ce5EdG6e74e1FdVHdU309I",
  "002847CRe3Ce5EdG6e74e1FdVH08I003040B2071a72021X920210meWuunhWueXYxYraegaZWaXWWXnmnfZWu",
  "eXYxYraegaWhoWWZeeWXWWWWWWWkaWiWWmmaWqeeXWWpYWvmuuZZWaL0YWeeWWWWWWWWWWmeWYYWWYWWWWWoWW",
  "WWWaWXWWWWWWWWWWeWaWXWWWW00XWWWWWWWXWaaWWWXXWmeWXaWWWWWWWeWXWaaWWWXXWmWWWeaWXXfWXWaomg",
  "fWWXXbYWWmaXWWWamWWaWYWWmWYm00eWWWWWWWWfWWWWWXWWWWWWWmWWWWWWWWWfWWWWWXWXuWWXWWWWWWWWWW",
  "WWWWaWWaWWYWYWWWaXuWemkeXvWW00/z//////zz/tt///zz+/l+at///////lzz/tt///zz+/w//lt/yjj/z/",
  "su/hj//zznu/+/pyl/nop//p/x/+//w/VYWWWWWWYYWeeWWWYYXWmXxeWWWWWWWmYYWeeWWWYYXWbWWmeWZooW",
  "YWfdWqoWWYYkdWXWiZmWkjiWWiWaWXWWbW0000867839ABC"]
@[expose] def ext_full_learn_clause_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack_ac_fid", [i64, i64], []), 96),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_reduce_m6", [i64, .bool], [i64]), 688),
   (("full_add_clause", [i64, i32, i32, .bool], [i64]), 192),
   (("full_reduce_purge_c0", [i64], [i64]), 576),
   (("full_eager_subsume", [i64, i64], []), 48)]

@[expose] def hints : List armIsa.Hints := [hint_full_det_new_level, hint_full_one_lit_confl,
    hint_full_eager_subsume, hint_full_learn_clause_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack_ac_fid", [i64, i64], []), 96),
   (("full_wstack_defrag_m6", [i64], []), 48),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_unwatch_large", [i64, i32, i32], []), 0),
   (("full_reduce_m6", [i64, .bool], [i64]), 688),
   (("full_add_clause", [i64, i32, i32, .bool], [i64]), 192),
   (("full_reduce_purge_c0", [i64], [i64]), 576)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Learn
