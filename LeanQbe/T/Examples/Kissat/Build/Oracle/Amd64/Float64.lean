module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Float64

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rcx, Reg64.rdi, Reg64.rbx, Reg64.rax, Reg64.r9, Reg64.rbp, Reg64.rdx, Reg64.rsi,
  Reg64.r13, Reg64.r12]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rax), (.gpr Reg64.rcx), (.gpr Reg64.rdi), (.gpr Reg64.rdx), (.gpr Reg64.rsi),
  (.flag CondCode.nc), (.flag CondCode.z), (.flag CondCode.c), (.gpr Reg64.r8), (.gpr Reg64.r9),
  (.flag CondCode.nz), (.gpr Reg64.rbx), (.gpr Reg64.rbp), (.slot 0 .w64), (.gpr Reg64.r13),
  (.gpr Reg64.r12)]

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

@[expose] def _rLoc (cs : List Char) : Option (Loc x64Isa.Reg x64Isa.VReg
    x64Isa.Cond) × List Char :=
  let (i, cs1) := _rNat cs; (_locs[i]?, cs1)

@[expose] def _rMove (cs : List Char) : Option (Move x64Isa.Reg x64Isa.VReg
    x64Isa.Cond) × List Char :=
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

@[expose] def _rEntry (cs : List Char) : Entry x64Isa.Reg x64Isa.VReg
    x64Isa.Cond × List Char :=
  let (nl, c1) := _rNat cs
  let (lv, c2) := _rList (fun s => let (sa, s1) := _rSymArg s
    let (lo, s2) := _rLoc s1; (lo.map (sa, ·), s2)) nl c1
  let (np, c3) := _rNat c2
  let (pl, c4) := _rList _rLoc np c3
  let (lz, c5) := _rBools c4; let (pz, c6) := _rBools c5
  ({ live := lv.filterMap id, ploc := pl.filterMap id, liveZ := lz, plocZ := pz }, c6)

@[expose] def _rPre (cs : List Char) : PreStep x64Isa.Reg x64Isa.VReg
    x64Isa.Cond × List Char :=
  let (pk, c1) := _rNat cs
  let (ms, c2) := _rList _rMove (pk / 2) c1
  ({ clearFlags := pk % 2 == 1, moves := ms.filterMap id }, c2)

@[expose] def _rVar (cs : List Char) : VariantHint × List Char :=
  let (t, c1) := _rNat cs
  match t with
  | 0 => (.default, c1) | 1 => (.adcx, c1) | 2 => (.adox, c1)
  | 3 => (.mulxFast, c1) | 4 => (.decInc, c1)
  | _ => let (o, c2) := _rNat c1; (.disp (Int64.ofBitVec (BitVec.ofNat 64 o)), c2)

@[expose] def _decH (chunks : Array String) : x64Isa.Hints :=
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

@[expose] def hint_f64u_msb64 : x64Isa.Hints := _decH #[
  "R100102000103040200010304020001030402000103040300050100001P51000000XWWWW00a////VZWWWW0",
  "0000"]
@[expose] def ext_f64u_msb64 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_round_pack : x64Isa.Hints := _decH #[
  "YR260507050300000302080900030208090003020809000302080900030500000003070004010003020003",
  "020809000302080900030208090003050202020000130A0404022607000405061A040615000405061A0405",
  "04020522040070010001010224002032YB2YC4020002010001001YG40100050224002002YB2YQ402000102",
  "0012X351T51YWWWXWWWXWWWWWWWWWWWWW00mWmWWWeYeWWWWWWWWWWWWWf00eeagaaYbXaWWWWWWWWWWWWWaL0",
  "vWWWWWXWWWWWW00l/ddtZtpxnztty////+a/////s5uueyeiakYeeZWWWWXxWWWWWfQ0000"]
@[expose] def ext_f64u_round_pack : List (SigEntry × Nat) := []

@[expose] def hint_f64u_add : x64Isa.Hints := _decH #[
  "cH26060700040103050A0A03050000020400000A0404130A0000100304020402000105030005061A000500",
  "010521000002030803030804040103050A0000190A00001006050705020404080209140902081408020914",
  "090208140805040404070300010304020304020809030402080903040208090304050303030404120A0000",
  "012607010005061A000605030005061A000500010521000015000501030401030402080103040208010304",
  "02080103050103010404110A0000012607010005061A000605030005061A0005000105210000I001000103",
  "390B1A40300032B1K210201020210002002X81XB00200064Y21Y33XQ2XV81040102010001010210002032a",
  "J1aK00200021aO00100050210002002aJ1b10020006010001000210002012cK1cL00200021cP0010005021",
  "0002002cK1d200200003a851S51YV51YWWWYWWWYWWWWWWWWWWXWWWXWWWXWWWWWWWaaaaWWWWeWWWWWWWmWWW",
  "YWWWWW00eWeWWWWYeWWWWWWWWWWWWWYWWWmWWWWaWaWWWWaWXaW00eeagaeagYeWWWWWWaeWaaYbYaYbXaWWWW",
  "WWWWWWWWWfgWWgWWWYYXYnWWWYWeom50XoWWWWWWWWWWWWWWWWWWvWWWWWYWWWWWWWWcWXWWWWWWWWWXmWWWW0",
  "0d//ddtZtdtZxllv////td/ppxnxpxnztty////+f/////igz/f///vvzuz/tlx/cwy5uueyeueyammcWWWWeu",
  "WiiakaiakYeeZWWWWXsWWWWWprYWsWWWccYdYWemaWvbZQ0000"]
@[expose] def ext_f64u_add : List (SigEntry × Nat) := []

@[expose] def hint_f64u_sub : x64Isa.Hints := _decH #[
  "ZP250601080503000900000009040B0404040B0801050A0202110A04041006050705030101030402080103",
  "04020801030402080103040208010305010101030701000B01030401030402080103040208010304020801",
  "03050101010303140A00000B2607010005061A000605010005061A0005000B052B00001080010001043NBB",
  "3G014301020100010102B0002032ZABZB00200021ZF001000502B0002002ZABZO00200002Y951T51eWWWeW",
  "WWeWWWWWWWWWWWWWWXWWWWW00YWYWWWWWoWWWWWWWWWWWWWWeWWYWWWW00XXWnenWnefWWWWWWWWWWWWWXbeWX",
  "eWWY50ceWWWWWeWWWWWWWWuWeaW00d//yy+yky+yljz/d////nd////znltzd//pHZZXZnZXZmoYWuWWWWkuWW",
  "WWYkmeYuWWiE00012"]
@[expose] def ext_f64u_sub : List (SigEntry × Nat) := []

@[expose] def hint_f64u_mul : x64Isa.Hints := _decH #[
  "dS260600010505030208020804090400010001000001030909000103090900010309090001030909000105",
  "0000000201230000080309100903081008030910090308100805000000040120020304080204000403041A",
  "030002001A0300030402040201000703060507050204040802091409020814080209140902081408050404",
  "0401070100010104020104020809010402080901040208090104050101010404120A000001260701000506",
  "1A000605030005061A000500010521000011050303110A0000060501030401030402080103040208010304",
  "02080103050103010404110A0000012607010005061A000605030005061A0005000105210000F001000104",
  "2J4G8221202011XL224110202010001010210002032bQ1bR00200021bV00100050210002002bQ1c8002000",
  "6010001010210002012e31e400200021e800100050210002002e31eH002000EO2303423140432424102242",
  "223140432424102242223140432424102242223140432424102242522005XG51X051Y751T51Z751aWWWaWW",
  "WaWWWWWWYWWWWWeWWWeWWWeWWWWWWWmmmmWWWWWmeWWWaaaaWWWWWWWWWWW00XWWWWWWWmWWWWYWYWWWWWoWWW",
  "WWWWWWWWWWWeWWWWWWWWWWWWWmWWWWWYWWW00mmeqemeqamWWWWWWgWaWXXWnenWnefWWWWWWWWWWWWWXbfWWW",
  "WWWWWWWWWWWWWWWWWWg50ZaWWWWWXmWWWWWWWWWWWWceWWWWWeWWWWWWWaWWWWWYWWWWWWeWWWWWWWW00X//+k",
  "lkdklkds+/p////hlp/yy+yky+yljz/d////nd////znj/r+///v//////d///////hLXnmnunmnufXWiWWWWq",
  "miWZZXZnZXZmoYWuWWWWkuWWWWYkoWgXWWWcWWWWWWuWWWWWWWqA0030"]
@[expose] def ext_f64u_mul : List (SigEntry × Nat) := []

@[expose] def hint_f64u_div : x64Isa.Hints := _decH #[
  "e126060800010203020304090408000100000C010B090B0C0109000B0C0109000B0C010900090C05010100",
  "02010900090B33010103020C080103020C080103020C080103020C08010305010101040C27090A03010001",
  "3B0C310308090100000407200301050B060507050300000304020800030402080003040208000304020800",
  "0305000000030700010B0003040003040208000304020800030402080003050000000303140A01010B2607",
  "000105061A010605000105061A0105010B052B01001C0C050000130A000006050103040103040208010304",
  "020801030402080103050103010404110A0000012607010005061A000605030005061A0005000105210000",
  "I0010001023JDH4E3390B303013XOBXN0XM922C302012YN2YOC39B1203012Z4CZ3B210202003Z4CZ3BYN23",
  "104303020100010102B1002032bTBbU10200021c2101000502B1002002bTBcB10200060100010102100020",
  "12e71e800200021eC00100050210002002e71eL0020001G23037XB51X451A5l///////////V051XR51T51Z",
  "851aWWWaWWWaWWWWWWYWWWWWaWWWaWWWaWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW00XWWWWWWWfWWWWWW",
  "WmWWWWXWXWWWXWfWWWWWWWWWWWWWWaWWeWWWaWWWWWWeWWWWWWYWW00mmeqemeqamWWWWWWgWaWWmmeqemeqam",
  "WWWWWWWWWWWWWoqmaWWWYWWWWWWWWWWWWWWWW50ZaWWWWWXnWWWWWWWWWWWWZaWWWWWaWWWWWWWWWWWWWXWWWW",
  "WWWeWWWWWWW00l/+klkdklkds+/p////hlp/+klkdklkds+/p////up////+us/p//Xxy///////d///////LX",
  "nmnunmnufXWiWWWWqmiWXnmnunmnufXWiWWWWdiWWWWXdfWiWW+aZWWWWWWWuWWWWWWWA001225"]
@[expose] def ext_f64u_div : List (SigEntry × Nat) := []

@[expose] def hint_f64u_inv_u64 : x64Isa.Hints := _decH #[
  "hB16060100000103040800010304080001030408000103040800010500000116050103010102010107061A",
  "030102040002300700080303070A3501030409030808000A20010806050705010000010304020001030402",
  "00010304020001030402000105000000010700080000010300010304020001030402000103040200010500",
  "00000101130A0808002607000805061A080605010805061A08050800052008001301020308010300000605",
  "07050301010304020801030402080103040208010304020801030501010103070100010103040103040208",
  "010304020801030402080103050101010303140A0000012607010005061A000605030005061A0005000105",
  "21000011010002010103000605070503010103040208010304020801030402080103040208010305010101",
  "03070100010103040103040208010304020801030402080103050101010303140A0000012607010005061A",
  "000605030005061A000500010521000011000000N00100010303021003012X10X730200051XQD283102002",
  "XQDXO2308320302010001010208002032aP0aQ80200021aU80100050208002002aP0b78020005010001010",
  "210002032e51e600200021eA00100050210002002e51eJ0020005010001010210002032hG1hH00200021hL",
  "00100050210002002hG1hU002000AY12303X12230U220032200ZA2200U226032260Z92200U2260322607T5",
  "1Z151T51ZF51T51ZE51T51XWWWXWWWXWWWWWWWWWWWWWWWWWWWWmWWWmWWWmWWWWWWWWWWWWWWWWWWWaWWWaWW",
  "WaWWWWWWWWWWWWWWWWWWWWWXWWWaWWWWW00XWXWWWWWfWWWWWWWWWWWWWWaWYWWWWWWWeWYWWWWWW00aaYbYaY",
  "bXaWWWWWWWWWWWWWarWWWYYXYnYXYmoWWWWWWWWWWWWWYgmWWWmmeqemeqamWWWWWWWWWWWWWoqXWWbWmWYbWX",
  "eWWWWW50XmWWWWWWWWWWWWvWWWWWXWWWWWWWYaWWWWWWWWWWWWimWWWWWmWWWWWWWmWWWWWWWWWWWWZaWWWWWa",
  "WWWWWWWWaWWWWmWWhWYmWWWW00X///ppxnxpxnztty////+a/////sbx//vvzuzvzu+xx+l////Yl////xY///",
  "+klkdklkds+/p////up////+uty/xr+/xxn/zkl////1iiakaiakYeeZWWWWXxWWWWWfwaWWccYdYcYdXaaXmW",
  "WWWzmWWWWazWWWXnmnunmnufXWiWWWWdiWWWWXdeZWagXWaakWYnmWWWWU0010"]
@[expose] def ext_f64u_inv_u64 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_from_u64 : x64Isa.Hints := _decH #[
  "XM1601000001030408000103040800010304080001030408000105000001070403040402040407061A0304",
  "02000103210300000201020030010001020213002003X11X00X430300001R51mWWWWWWW00aWWWWWWW00XYm",
  "XWWWWW10YWeWWbmaWWWW00l//zzu/zp////PYYdWYiWWWW60000"]
@[expose] def ext_f64u_from_u64 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_to_u64 : x64Isa.Hints := _decH #[
  "C100701050202010303000200100100010000000I0Ym00d/yBZK0000"]
@[expose] def ext_f64u_to_u64 : List (SigEntry × Nat) := []

@[expose] def hint_u64_mul128 : x64Isa.Hints := _decH #[
  "M20020104030001020804080408030403000201020802000000000mW00d///V00000"]
@[expose] def ext_u64_mul128 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_log10_u64 : x64Isa.Hints := _decH #[
  "dU17010000010304080001030408000103040800010304080001050B0B0001010302003100030100090409",
  "04030903010000040000030002030104000208071B020B030B0103040B0200020002010000030B040B0201",
  "06070403030402080903040208090304020809030402080903040503030401030301030406030101030402",
  "080103040208010304020801030402080103050101010303060001340A0304000A03000605070504030304",
  "02080903040208090304020809030402080903040503030304070300010304020304020809030402080903",
  "040208090304050303030404120A0000012607010005061A000605030005061A0005000105210000A00100",
  "01011X0B12101001X0B3028103010303100303010001010210002032dK1dL00200021dP001000502100020",
  "02dK1e200200005R51YS51X451XK51T51XWWWXWWWXWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW",
  "WWWW00eWeWWWeYeWWWWWWWWWWWWWfWWWWWWWWWWWWWWWWWeWWWWWmWWWWWWWWWWW00aaYbYaYbXaWWWWWWWWWW",
  "WWWarWWWWWWWWXWWWWWWWbWWWWWeWWWWWWWWWWW10vWWWWWXWWWWWWWWWXaWWWWWWnWWWWWWWaWWWWWaoeWbaW",
  "WWW00//ppxnxpxnztty////+a/////sbtltp////v/y////+n/////d//////p////PiiakaiakYeeZWWWWXxW",
  "WWWWfwemeiWWWWcWZWWWWXkWWWWWuWWWWWWiWWWW600012"]
@[expose] def ext_f64u_log10_u64 : List (SigEntry × Nat) := []

@[expose] def hint_f64u_nlogpown : x64Isa.Hints := _decH #[
  "XS2502021A3107160100000103040800010304080001030408000103040800010500000107040304040E04",
  "0407061A030408000103210301100E010E01500100010014E121010034E5C9F22B302041G2213102004G2X",
  "D1XC0XG30400030405708132093420132159X751eWWWWWWWWWW00YWWWWWWWWYW00neWmWWWWWnWG0YWaWWYu",
  "YWWWWWWW20X///++yl+v////yy+PXXZmXcWWWWZZX600042598"]
@[expose] def ext_f64u_nlogpown : List (SigEntry × Nat) :=
  [(("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24)]

@[expose] def hint_m6_wm4_get : x64Isa.Hints := _decH #["23A1010010001000J0004000lN80000"]
@[expose] def ext_m6_wm4_get : List (SigEntry × Nat) := []

@[expose] def hint_m6_wm4_set : x64Isa.Hints := _decH #["14A1000000000J0004000lN80000"]
@[expose] def ext_m6_wm4_set : List (SigEntry × Nat) := []

@[expose] def hints : List x64Isa.Hints := [hint_f64u_msb64, hint_f64u_round_pack,
    hint_f64u_add, hint_f64u_sub, hint_f64u_mul, hint_f64u_div, hint_f64u_inv_u64,
    hint_f64u_from_u64, hint_f64u_to_u64, hint_u64_mul128, hint_f64u_log10_u64,
    hint_f64u_nlogpown, hint_m6_wm4_get, hint_m6_wm4_set]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Float64
