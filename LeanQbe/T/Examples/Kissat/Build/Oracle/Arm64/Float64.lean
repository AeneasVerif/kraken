module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Float64

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X20)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X21)),
  (XRegOrSp.reg (XReg.X19))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X19)))]

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

@[expose] def hint_f64u_msb64 : armIsa.Hints := _decH #[
  "R100102010003040201000304020100030402010003040201000202000000000XWWWW20ammmmHZllllE000", "0"]
@[expose] def ext_f64u_msb64 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_round_pack : armIsa.Hints := _decH #[
  "YR250006000002020300070802030007080203000708020300070802030002020203060201020300020302",
  "00070803020007080302000708030200030202030317090101022506020100051901051003010005190100",
  "01020022010270012001010221002032YB2YC1020002012001001YG10100050221002002YB2YQ102000102",
  "0010YWWWXWWWXWWWWWWWWWWWWW00mWmWWWeYeWWWWWWWWWWWWWf00eeagaaYbXaWWWWWWWWWWWWWaL0vWWWYWX",
  "WWWWYW00l/ddtZtpxnzttymmmn+ammmmns5uueyeiakYeeZlllkXxllllkfQ0000"]
@[expose] def ext_f64u_round_pack : List (SigEntry × Nat) := []

@[expose] def hint_f64u_add : armIsa.Hints := _decH #[
  "cL250506040103020009090200040404010101090707120901021200010401040203000102000519020002",
  "030023020207020802020801020301000904041A09020212050006000004040700080A040700080A040700",
  "080A040700080A0407000404040B0102030100040104000708010400070801040007080104000101010404",
  "17090202032506010200051902050001020005190200020300230202100200010003010300040701030004",
  "070103000407010300010301040411090202012506010200051902050003020005190200020100210202I0",
  "01200103394B3A10300032B3K412201020232002002X83XB20200064Y23Y31XQ7XV8124010201200101023",
  "2002032aJ3aK20200021aO20100050232002002aJ3b12020006012001000212002012cK1cL20200021cP20",
  "100050212002002cK1d220200000YWWWYWWWYWWWWWWWWWWXWWWXWWWXWWWWWWWWWWWWWWWeWWWWWWWmWWWYWW",
  "WWW00eWeWWWWYeWWWWWWWWWWWWWYWWWmWWWWaWaWWWWaWXaW00eeagaeagYeWWWWWWaeWaaYbYaYbXaWWWWWWW",
  "WWWWWWfgWWgWWWYYXYnWWWYWeom50XoWWWaWWWWWWWWWWWWWWvWWWYWYWWWWaWWWcWXWWWWWWWWWXmWWWW00d/",
  "/ddtZtdtZxllvXXXZtd/ppxnxpxnzttymmmn+fXXXXZigz/f///vvzuzWdlx/cwy5uueyeueyammc+++yeuWii",
  "akaiakYeeZlllkXs++++yprYWsWWWccYdY/umaWvbZQ0000"]
@[expose] def ext_f64u_add : List (SigEntry × Nat) := []

@[expose] def hint_f64u_sub : armIsa.Hints := _decH #[
  "ZP2C0503070004080D08080D08010A01010A0307010009020211090A0A1D05000600000101040007080104",
  "00070801040007080104000708010400010101040601020301000401040007080104000708010400070801",
  "04000101010404120907020325060102000519020500010200051902000203002302021280012001043N3B",
  "4GD1A30102012001010232002032ZA3ZB20200021ZF20100050232002002ZA3ZO20200000eWWWeWWWeWWWW",
  "WWWWWWWWWWXWWWWW00YWYWWWWWoWWWWWWWWWWWWWWeWWYWWWW00XXWnenWnefWWWWWWWWWWWWWXbeWXeWWY50c",
  "eWWWmWeWWWWmWWWuWeaW00d//yy+yky+yljz/aaaalnaaaaajnltzd//pHZZXZnZXZmoYWxxxxmkxxxxxokmeY",
  "uWWiE0000"]
@[expose] def ext_f64u_sub : List (SigEntry × Nat) := []

@[expose] def hint_f64u_mul : armIsa.Hints := _decH #[
  "e425050A04000007020802080103010A040A0003030400070D030400070D030400070D030400070D030400",
  "03030302072003030400080A030400080A030400080A030400080A03040003030401032402070108020104",
  "0102011902040704190202000104010403020601050006000004040700080A040700080A040700080A0407",
  "00080A04070004040403060302010300040304000708030400070803040007080304000303030404170902",
  "02012506010200051902050003020005190200020100210202110003031109020205000100030103000407",
  "01030004070103000407010300010301040411090202012506010200051902050003020005190200020100",
  "210202F0012001042J1G8227202011XL221310202012001010212002032bQ1bR20200021bV201000502120",
  "02002bQ1c82020006012001010212002012e31e420200021e820100050212002002e31eH20200000aWWWaW",
  "WWaWWWWWWYWWWWWeWWWeWWWeWWWWWWWWWWWWWWWWmeWWWWWWWWWWWWWWWWWW00XWWWWWWWmWWWWYWYWWWWWoWW",
  "WWWWWWWWWWWWeWWWWWWWWWWWWWmWWWWWYWWW00mmeqemeqamWWWWWWgWaWXXWnenWnefWWWWWWWWWWWWWXbfWW",
  "WWWWWWWWWWWWWWWWWWWg50ZaWWWeWXmWWWWWWWWWWWWceWWWmWeWWWWmWWaWaYWWYWWWWaWeWWWWmWWW00X//+",
  "klkdklkds+/oYYYdhlp/yy+yky+yljz/aaaalnaaaaajnjWb+///vXXXXZ/aaaaal//hLXnmnunmnufXWjzzzu",
  "qmiWZZXZnZXZmoYWxxxxmkxxxxxoko/wXWWWc++++yWxxxxxmWWqA0000"]
@[expose] def ext_f64u_mul : List (SigEntry × Nat) := []

@[expose] def hint_f64u_div : armIsa.Hints := _decH #[
  "e12505080D0302040207010404080D00010103000A0E0103000A0E0103000A0E0103000A0E010300010101",
  "02000301030A3003030700080E030700080E030700080E030700080E03070003030304032602090D070D0A",
  "3D0A310C070801020203062902010C0D050006000002020300040702030004070203000407020300040702",
  "0300020202030602010D0200030203000407020300040702030004070203000202020303140901010D2506",
  "030200051902050002010005190100010D002D01021A0A0002021309020205000100030103000407010300",
  "04070103000407010300010301040411090202012506010200051902050003020005190200020100210202",
  "I0012001023JDH4E7321A303013XOAXN1XM2243302012YN4YO332DA203012Z4AZ3D212202003Z4AZ3DYN43",
  "123303020120010102D1002032bTDbU10200021c2201000502D1002002bTDcB10200060120010102120020",
  "12e71e820200021eC20100050212002002e71eL20200000aWWWaWWWaWWWWWWYWWWWWaWWWaWWWaWWWWWWWWW",
  "WWWWWWWWWWWWWWWWWWWWWWWWWWW00XWWWWWWWfWWWWWWWmWWWWXWXWWWXWfWWWWWWWWWWWWWWaWWeWWWaWWWWW",
  "WeWWWWWWYWW00mmeqemeqamWWWWWWgWaWWmmeqemeqamWWWWWWWWWWWWWoqmaWWWYWWWWWWWWWWWWWWWW50ZaW",
  "WWeWXnWWWWWWWWWWWWZaWWWeWaWWWWeWWWWWWWWXWWWWYWWeWWWWmWW00l/+klkdklkds+/oYYYdhlp/+klkdk",
  "lkds+/oYYYduoYYYYcusppX/Xxymmmmnydaaaaal//LXnmnunmnufXWjzzzuqmiWXnmnunmnufXWjzzzudjzzz",
  "zvdfii+W+aZllllkZuxxxxxmWWA0000"]
@[expose] def ext_f64u_div : List (SigEntry × Nat) := []

@[expose] def hint_f64u_inv_u64 : armIsa.Hints := _decH #[
  "hB1505000101030004070103000407010300040701030004070103000101031500040304040204040B0519",
  "0300020404023D06030804040609300304070A040808010929020805000600000202010003040201000304",
  "02010003040201000304020100020202010602080D02000102010003040201000304020100030402010002",
  "02020101130908080D2506010200051902050002080005190800080D002D08021401020408010902020500",
  "060000010103000407010300040701030004070103000407010300010101030601020D0100030103000407",
  "010300040701030004070103000101010303140902020D2506010200051902050001020005190200020D00",
  "2D020211030102030902020500060000010103000407010300040701030004070103000407010300010101",
  "030601020D0100030103000407010300040701030004070103000101010303140902020D25060102000519",
  "02050001020005190200020D002D020210020202N00120010303421003012X11X730200051XQD284102002",
  "XQDXO23184203020120010102D8002032aPDaQ80200021aU201000502D8002002aPDb78020005012001010",
  "2D2002032e5De620200021eA201000502D2002002e5DeJ20200050120010102D2002032hGDhH20200021hL",
  "201000502D2002002hGDhU20200000XWWWXWWWXWWWWWWWWWWWWWWWWWWWWmWWWmWWWmWWWWWWWWWWWWWWWWWW",
  "WaWWWaWWWaWWWWWWWWWWWWWWWWWWWWWXWWWaWWWWW00XWXWWWWWfWWWWWWWWWWWWWWaWYWWWWWWWeWYWWWWWW0",
  "0aaYbYaYbXaWWWWWWWWWWWWWarWWWYYXYnYXYmoWWWWWWWWWWWWWYgmWWWmmeqemeqamWWWWWWWWWWWWWoqXWW",
  "bWmWYbWXeWWWWW50XmWWWWWWWWWWWWvWWWYWXWWWWYWWYaWWWWWWWWWWWWimWWXWWmWWWXWWWmWWWWWWWWWWWW",
  "ZaWWWeWaWWWWeWWWaWWWWmWWhWYmWWWX00Xyl/ppxnxpxnzttymmmn+ammmmnsbZ//vvzuzvzu+xx+eeee/Yee",
  "eeexYp//+klkdklkds+/oYYYduoYYYYcuqy/xr+yZxn/zkeeeee1ZmWiiakaiakYeeZlllkXxllllkfwyWWccY",
  "dYcYdXaaXttttWztttttaziWWXnmnunmnufXWjzzzudjzzzzvdhZWagXZyakWYntttttU0000"]
@[expose] def ext_f64u_inv_u64 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_from_u64 : armIsa.Hints := _decH #[
  "XM150001010300040701030004070103000407010300040701030001010306070407070207070B05190400",
  "02010304230402010203020230012001020234002003X13X01X440300000mWWWWWWW00aWWWWWWW00XYmXWW",
  "WWW10YWeWWbmaWWWW80l/+Xzu/zoYYYY1X+YdWYjzzzzU0000"]
@[expose] def ext_f64u_from_u64 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_to_u64 : armIsa.Hints := _decH #[
  "C110603000202000303010202100120010000000I0cm00dmiBlpK0000"]
@[expose] def ext_f64u_to_u64 : List (SigEntry × Nat) := []

@[expose] def hint_u64_mul128 : armIsa.Hints := _decH #[
  "M23020401070304020108010801070807030204020101000000000XgmW00d///V00000"]
@[expose] def ext_u64_mul128 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_log10_u64 : armIsa.Hints := _decH #[
  "dU16000101030004070103000407010300040701030004070103000D0D06010103020231020301020A040A",
  "04030A03010202040202030207000103020708061D070D030D0103040D0702070207010202030D040D070D",
  "05060003030400070803040007080304000708030400070803040003030401030301030405000101030004",
  "07010300040701030004070103000407010300010101030305020134090304020903020500060000030304",
  "00070803040007080304000708030400070803040003030304060302010300040304000708030400070803",
  "04000708030400030303040417090202012506010200051902050003020005190200020100210202A00120",
  "01011X0D17101001X0D3278103010323100303012001010212002032dK1dL20200021dP201000502120020",
  "02dK1e220200000XWWWXWWWXWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW00eWeWWWeYeWWW",
  "WWWWWWWWWWfWWWWWWWWWWWWWWWWWeWWWWWmWWWWWWWWWWW00aaYbYaYbXaWWWWWWWWWWWWWarWWWWWWWWXWWWW",
  "WWWbWWWWWeWWWWWWWWWWW10vWWWYWXWWWWYWWWWXaWWWWeXnWWWWYWgqWWeWmsoeWjaWWWW80//ppxnxpxnztt",
  "ymmmn+ammmmnsbtltoYYYYX/ymmmmmn/////ad////WoYYYY1iiakaiakYeeZlllkXxllllkfwemejzzzz+WZl",
  "llllkWWWWWxuWWWW/jzzzzU0000"]
@[expose] def ext_f64u_log10_u64 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_nlogpown : armIsa.Hints := _decH #[
  "XS20020219330B150001010300040701030004070103000407010300040701030001010306070407070F07",
  "070B0519040007010304230403110F030F03500120010014F121010034F5G9H22I302041G2234102004G2X",
  "D3XC1XG404000204023041320510eWWWWWWWWWW00YWWWWWWWWYW00neWmWWWWWnWG0YWaWWYuYWWWWaWW20X/",
  "//W+yl+vXXXXWy+P/XZmXc++++/ZX600046254"]
@[expose] def ext_f64u_nlogpown : List (SigEntry × Nat) :=
  [(("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0)]

@[expose] def hint_m6_wm4_get : armIsa.Hints := _decH #["511010902021001200100000004000lN80000"]
@[expose] def ext_m6_wm4_get : List (SigEntry × Nat) := []

@[expose] def hint_m6_wm4_set : armIsa.Hints := _decH #["423030902100000000000004000lN80000"]
@[expose] def ext_m6_wm4_set : List (SigEntry × Nat) := []

@[expose] def hints : List armIsa.Hints := [hint_f64u_msb64, hint_f64u_round_pack,
    hint_f64u_add, hint_f64u_sub, hint_f64u_mul, hint_f64u_div, hint_f64u_inv_u64,
    hint_f64u_from_u64, hint_f64u_to_u64, hint_u64_mul128, hint_f64u_log10_u64,
    hint_f64u_nlogpown, hint_m6_wm4_get, hint_m6_wm4_set]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Float64
