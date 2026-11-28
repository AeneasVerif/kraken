module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Compact

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rbx, Reg64.rdi, Reg64.rax, Reg64.r9, Reg64.rbp, Reg64.r12, Reg64.r13, Reg64.r14,
  Reg64.r15, Reg64.rdx, Reg64.rcx, Reg64.rsi, Reg64.r8]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.flag CondCode.nz), (.gpr Reg64.rax), (.flag CondCode.c), (.gpr Reg64.rcx),
  (.flag CondCode.nc), (.flag CondCode.z), (.gpr Reg64.rbx), (.gpr Reg64.r9), (.gpr Reg64.rdx),
  (.gpr Reg64.r8), (.gpr Reg64.r15), (.gpr Reg64.r12), (.gpr Reg64.rsi), (.gpr Reg64.r14),
  (.gpr Reg64.rdi), (.gpr Reg64.rbp), (.gpr Reg64.r13), (.flag CondCode.g), (.slot 1 .w64),
  (.slot 3 .w64), (.slot 2 .w64), (.slot 0 .w64), (.flag CondCode.l), (.slot 5 .w64),
  (.slot 4 .w64), (.slot 6 .w64), (.slot 8 .w64), (.slot 7 .w64), (.slot 9 .w64),
  (.slot 10 .w64), (.slot 12 .w64), (.slot 11 .w64)]

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

@[expose] def hint_full_compact_needed : x64Isa.Hints := _decH #[
  "93020110213040303021001200104K10101010afJ000nY40YWW00lkbxNmnwa80000"]
@[expose] def ext_full_compact_needed : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_flush : x64Isa.Hints := _decH #[
  "830202031021500103001100101146010002146010001020010rWaWdcXJ0XWWa00femeY4000///ik/lxNpn",
  "Wma800010"]
@[expose] def ext_full_compact_flush : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696)]

@[expose] def hint_full_compact_mark_live : x64Isa.Hints := _decH #[
  "b627081319161A1B11000460350C70350C70350C70350C110C041260350C11020041013707070D0D1E323C",
  "10010C0F020100011501250120010C0C400111120G021A001B020C0C0F3F010G070D01026E0E0102100112",
  "30010207010107071115040F0B04313101022H050101410D0G072B02300004173707022507074017073707",
  "0225070740170737070225070740170737070225070740110704121737070225070740110202X008D6B993",
  "78HBFA4IJJ080000993B97867D6FA4IHBJJ1190100993B97867D6FA4IHBJJ1190100993B9D67867FA4IHBJ",
  "J1190102A93B9D67867FA4IHBJJM11CA0101A93B9D67867FA4IHBJJM11CA0101A93B9D67867FA4IHBJJM11",
  "CA0101A93B9D67867FA4IHBJJM11CA0103A93B97867D6FA4IHBJJYF11CA010264IJJB99378D60600008D6B",
  "99378HBFA4IJJ1G801019D6B99378HBFA4IJJYVG090000CD6ZEEB993YVGZCD78HBFA4IZA7JJ11C0101CD6Z",
  "EEB993YVGZCD78HBFA4IZA7JJ11C0109000000084E4IJJaQAB99378D61180102C4E4IJJaQAB99378b0Cb1K",
  "b5FD6aTB11Cu0103Eb7Gb87aQAaTBb5Fb1K4E4IJJB99378b0CD611EXG100E4E4IJJaQAB99378b0Cb1Kb5FD",
  "6aTBbP1b870Eu00029c714E4IJJaQAB99378D6090003Cc7L4E4IJJaQAD6B99378b0Cb5Fb1K2G7CZW0200Cc",
  "7L4E4IJJaQAB99378b0Cb1Kb5FD63G7BCXm0300Dc7L4E4IJJaQAB99378b0Cb1Kb5FD6cGB2G7DXm0204CD6B",
  "99378b0Cc7L4E4IJJaQAb5FdB70CXW0003BD6B99378b0Cc7L4E4IJJaQAb5F11BXW0100BD6B99378b0Cc7L4",
  "E4IJJaQAb5F11BXW0100BD6B99378b0Cc7L4E4IJJaQAb5F11BXW0101CD6B99378b0Cc7L4E4IJJaQAb5FdG1",
  "0CXW0003CD6B99378b0Cc7L4E4IJJaQAb5FdG10CXW0003CD6B99378b0Cc7L4E4IJJaQAb5FdG10CXW0003CD",
  "6B99378b0Cc7L4E4IJJaQAb5FdG10CXW0005CD6B99378b0Cc7L4E4IJJaQAb5Fg110CXW0007G4332311bO22",
  "118223342324XE223202302XC22221dS51YdmiZmWXZucXue+XmkYdmiZmnyZWyWWaWXyWudWWYWWXuWmluWyW",
  "XWWaZuZXmmWWsZqZpmWXu/WWXu/mylukdydZyWgr90XYWmXXWXYWeWmmWYWaaWWmXXWWaWeeWXWmmWWeYWYYeW",
  "WaYWWWWWWWWaaWWWWWWWWWWWWWWWaWYWaeWYWWXWWWmWWeWYWW00nWeWmmWnWaWeeWXWYYWWeWmmWYWaaWamee",
  "WWbXWXXaWWYXXaWYWWaaYYWaWaYXXYXWaWWWXYWXWYaWXWWWmWWeWWaWfWW00eWXuWmWaWW+WXWWdmWeWXyWYW",
  "WkWWWWWcWWZmuWWaWeWXceWimWWWWWaWWWWWWYWWfnWWWeWWYWeWWaWWYWWXWWWWW00+y/l++/+y/t/ll/z/xx",
  "//l++//x/tt/s/ld//nz/yzt/pxzzmlv//ptvx/t/txzyuz/t///zvxz/xpxz/z+/+/l/lt/b//VXZWmXXWXZW",
  "eWmmWYWaaWWmXXWWaWeeWfWmuWWkYWZYeWiaYYlmcWWiecaWeWeaYZdYWeWWWYcaYWaiaYWYXWXWmWmeWwWW00",
  "046045678"]
@[expose] def ext_full_compact_mark_live : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_assign_map : x64Isa.Hints := _decH #[
  "C2917181E0050350C2C01330240011001004CEA88769213402015CEA88769F311501006E1CEA88769F3060",
  "0000icXuyYL0eWWaYWW00aWWYXWe00aYWeaW00Zp//xz/lViWWaYWm00000"]
@[expose] def ext_full_compact_assign_map : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_record_ext : x64Isa.Hints := _decH #[
  "X7343102191F1750080103021101080308022820080M0E082803110231010101002103046C010302700110",
  "01026I7E94B66GF5C116010064B665CE9I7GF2136020244B66I7GF13401006I7E94B66GF5C213602007I7E",
  "94B66GF5CX41137010244B66I7GF21340201040090511J51+WcWZWXmZWWWdbeS0XWWWWWWaWWeWWeWWW00mW",
  "YWaWYWWaYWaWWY10gWYWXWWmWXYWnWW00d+l/udt/v/utudol/xTXmWdueWcWdedujmWa20003045"]
@[expose] def ext_full_compact_record_ext : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_bins : x64Isa.Hints := _decH #[
  "bV311316191310510138080501302518025F10010A010A020107072700012501070F0727070B0701322201",
  "04A10704123102050101181D020D021G1004131E000E000E071818070718081807071808180E0E13031307",
  "031E000E000E071818070718081807071808180E0E13031301030412131E000E000E071F1F07071F0F1F07",
  "071F0F1F0E0E13031301020201041103130313031101110103130313031101110103130313031101110103",
  "1303130311011801041211031303130311011802M000000005D9B66N5C4E1G5010085C4J7KD99OB66NF32G",
  "D80202CIGOLF39OB67KD9JD5C4J6NT81IC0102BD9JDOLX88F35C4J7K9OB66N2GBB0200CF39OB67KX7IX88D",
  "9JDOL5C4J6N3G1BC0301CF39OB67KX7IX88D9JDOL5C4J6N371BC0306DYHG5C4J7KD99OB66NF3JDX88YIBOL",
  "0D0000DD9JDYIBOLX88F3YHG5C4J7K9OB66N11D0100DD9JDYIBOLX88F3YHG5C4J7K9OB66N11D0100DD9JDY",
  "IBOLX88F3YHG5C4J7K9OB66N11D0105CYHG5C4J7KD99OB66NF3JDX88YIB0C000336N5CD90300004D9B66N5",
  "C11401004D9B66N5C11401004D9B66N5C11401025D9B66N5CZP10500025D9B66N5CZP10500045D9B66N5Cc",
  "2105000325CD9182010025CD9182010025CD9182010C8234A26322359331D2302641203122222414110311",
  "0411131102250X02214Y0222092213b622950XYaeWWnYaaenXYaeenYWWWamoYegWXWWXaamoYmWeamoYegWX",
  "WXWWYmWWiWXgrhWWWXmZWuWWbmWuyZpmrA0mWWWemWWWWWWWWWWWWWWaeWWWWWWaeYaWWWWWWXYWWWWWWWaeWe",
  "YXWWWaWnWWWWWemWWWWWWWWWWYWWWWW00eWWWaeWWWWWWWWWWWWWXYaWWWWWWYaXYWWWWWWWnWWWWWWWYaXaXW",
  "mWXYWemWWWYaeWWaYWaWeXXXWmWXW00vpaWaivopciqvpbcivWmWZijnsbWWWXWxZijneWWZijnsbWWWWWWXWa",
  "WaWeWWXXWWWmWWiWWWmWWaXnWW00dd///td/////////////yxp//////utzv//////+b///////utyty+l/zv",
  "/kl///vtl//tx/ntlzzz+//z/VuWWWeuWWWWWWWWWWWWWZaiWWWWWWdeYcWWWWWWXwWWWWWWWdeZeZXmWYcWnm",
  "WWWcemWWeaWkemYYYXWWYW00066045678"]
@[expose] def ext_full_compact_bins : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_arena : x64Isa.Hints := _decH #[
  "b93116180C1E705E020C0C0937010A080101026909010210011230010208010108081A1002070E02010121",
  "3101022H05090929050E3901090813021505052175010E09000B0G0D0F080F023C3E080801010C01010401",
  "090012090702090907022907290939090900090029010704350101000105010021092C0101040108001209",
  "07020909070229072707380807000700280122080435010100010501002107224272A8A30C04123302P001",
  "1001002434L5FBGD1205008434L7JEEEOBK96CI51FBGD8050064L7JEOBK96CI51FBGD60502GOFPBQGRD434",
  "L7JEOBK96CIVCSEX47X09X0P1AGXuW0103HX6AX78OFPBQGRD7JEOSEX47X0P434LBK96CIVC11HXm0100HOFP",
  "BQGRD434L7JEOBK96CIVCSEX47X0PXO1X780HuW0005DOFPBQGRD434LY6A7JEOBK96CIX0P18DaW0100FY6AO",
  "FPBQGRD4L7JEOYENBK96CIVCX0PX47283FuW0200GY6AOFPBQGRDYENBK96CIVC4L7JEOX0PX47YG318GuW010",
  "9FOFPBQGRD434LY6A7JEOBK96CIaIPaEEaEN0FuW00005OFPBQGRD4L050001HOFPBQGRD434LY6A7JEOBK96C",
  "IaIPaEEaENaACaG80HXuW0002KOFPBQGRD434LY6A7JEOBK96CIaIPaEEaENaJCaG8aACaOQaN10KauW0000KO",
  "FPBQGRD434LY6A7JEOBK96CIaIPaEEaENaJCaG8aACaOQaN10KauW0006POFPBQGRD434LY6A7JEOBK96CIaIP",
  "aEEaENbG9b5RaJCbESaG8b67b6TaACaOQaN10PaeuW0006CY6AOFPBQGRD434L7JEOBK96CI0C00005OFPBQGR",
  "D4L050001FY6AOFPBQGRD434L7JEOBK96CIaEEaENaIP0FiW0002IY6AOFPBQGRD434L7JEOBK96CIcBCaIPaE",
  "EaENcG8cF10IXmW0000IY6AOFPBQGRD434L7JEOBK96CIcBCaIPaEEaENcG8cF10IXmW0007NY6AOFPBQGRD43",
  "4L7JEOBK96CId87cT9cBCd6QaIPcU8cUSaEEaENcGRcF10NXnWW00092eO1eU813201002eO1eU813201002eO",
  "1eU8132010XF043010A1G834131B32933262293923521236C622C5522C5X42352K221292225722A0A22B3D",
  "2236D22234235142362A42A02151238CF42A02156237C443BC2C70239C322C872297423A36223A42297A22",
  "385222A12297642A0215F22A0H22A06239342379023893229754296219J229922226C229754296229E22A0",
  "B22A0222A0922A0022A01Y251cWWrgroreWWoXoWZWuWWWdWXmcWZpaWWWWWWaWZWWWWyWXmWyvWWWWWWWdkWW",
  "XkyuWWWkZWcXuWXWWWyWedyWkWX/qL0YWemWWWWWWmWWeWemWYaYWmeeWWmWWWeWWneWWmWemeYXWWaWWWYWWa",
  "eWWWWeWWWWWWmWWmYWmWWWWWYXWWWWWWWWWW00XWaeWWWWWWeWWaWWeWXYXWeaaWWfWWWXWeeaeWWWaeaXWmWY",
  "eWWWeYYXYWWWaWWWWYqeWWeXeeWagWWXWmoWXWWYYWW00YWaWWWmWWWWWWWWWWemWWXYWWYafnWWWWWWaWWXYW",
  "WWaeWnYieWWWWWXWZcXWWcieWWWdXmWWypWWYWaWWpaWceWWW00y/td//////l//t//l/yxz/lpt//a///z/ll",
  "tl///pltz+l/vd///lxxzx///tnx//udd//lyll/ph/vz++udy//vx//VZWeuWWWWWWmWWeWWmWZaYWmieWWxW",
  "WWYWmmemWWWimeYXmWcuWWWmaaYaWWWekaWWduuWWmZmmWiqWcYXXduZWWcaWW000C6045678"]
@[expose] def ext_full_compact_arena : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hint_full_compact_vars : x64Isa.Hints := _decH #[
  "XO41131B1G191719171C161F1E1D1A11110100041178010412280200511121211111200101000808214121",
  "2102220104XS8010412F802B21101B00000000J686S5IEGCBUESFQ6OCM7K9A3X6T4QIUGVX4LX2AX0D0J000",
  "0L6SX7K818J5IEGCBUESFQ6OCM7K9A3X6T4QIUGVX4LX2AX0D18L0100L6SX71X7K8J5IEGCBUESFQ6OCM7K9A",
  "3X6T4QIUGVX4LX2AX0D18L0100L6SX71X7K8J5IEGCBUESFQ6OCM7K9A3X6T4QIUGVX4LX2AX0D18L0105I686",
  "S4QIUGV5IX4LX2AX0DUEQ6OCM7K9SFEGCBA32ONI0200J686S5IEGCBUESFQ6OCM7K9A3X6T4QIUGVX4LX2AX0",
  "D3ON1J030264Q6SZ7NZ6OIUGV060000K4Q6SZ7NZ6OIUGV5IX41X4LX2AX0DUEQ6OCM7K9SFEGCBA318K0100K",
  "4Q6SZ7NZ6OIUGV5IX41X4LX2AX0DUEQ6OCM7K9SFEGCBA318K0100K4Q6SZ7NZ6OIUGV5IX41X4LX2AX0DUEQ6",
  "OCM7K9SFEGCBA318K010X6D23BC123C31231B5238112278122881433222814302228043A22211432239952",
  "223G2222H6120342352061203423522432229A423320229222223222231436229316372296222122971222",
  "402294122950434222522223043592924222332223D2221ZG2221X7222B0222C12218B222412225122992Z",
  "351251fXgrgrWYrgrriWXgrgwtgrgsrwrgrrkrgrjhWWXfpvmYrcjiWYWWrgqWXgrgrgL0aWWWWXWWWWWWnWWW",
  "WWWWWWWWWWWWWWWWWWWWemWWWWWWWWWXWemWWWWmWWWWW00YWWWWWmWWWWWemWWWWWWWWWWWWWWWWWWWWWYaeW",
  "WWWWWWWWemaeWWWYeWWWWW00mWWeWWWeWWWWYWWWWWmWWWWaWXWWWXeamWWWWWWWaWWWWWWWWWW00Z/x////+l",
  "/////kl/////////////////////vtd///ol////kltd///vl/////VaWWWWXmWWWWWnmWWWWWWWWWWWWWWWWW",
  "WWWWceuWWWjmWWWWnmeuWWWcmWWWWW000D6045678"]
@[expose] def ext_full_compact_vars : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_sift_q : x64Isa.Hints := _decH #[
  "L43010457072F08022E0E230208070F5101342301043000000003465C7B3319303014465C7BD9387F40301",
  "0405A0010XnvmciZc00XWW00mYWWWWmW40mimZaXo00+lx/u/+l/JXmaWdWXmWC0003045"]
@[expose] def ext_full_compact_sift_q : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_vmtf : x64Isa.Hints := _decH #[
  "ZT2518161911043707270727072703070412370302040A001A0E07045B0B2G03022D0D2E02030B0E5G0G34",
  "2E0704000A001327025B0B2D03022G0G2E02030B0D5G0G342G07040A00043707253F2F042F2F0B2707250F",
  "2F042F2F0B2707250F2F042F2F0B2707250F2F042F230F0704123707253F2F042F230F0203034101T00000",
  "00165C88E14EA6C906000065CE1884EA6C9136010065CE1884EA6C9136010065CE1884EA6C913601046E18",
  "8C95CA64E0600016E15C884LC9A606000065C88E14LA6C91A601017XFA5C88E14LA6C90700007XFA5C88E1",
  "4LA6C93E7F703018XFA5C88E14LA6C9XLF33BE803046E15C884LA6C91A601017E15C884LA6C9YTA0700007",
  "E15C884LA6C9YTA3G7F703018E15C884LA6C9YTAZ5F33BD8030435C4EE10300006E15C4E88C9A613601006",
  "E15C4E88C9A613601006E15C4E88C9A613601018E15C4E88aD3C9A6aH71F801018E15C4E88aD3C9A6aH71F",
  "801018E15C4E88aD3C9A6b771F801018E15C4E88aD3C9A6b771F801018E15C4E88aD3C9A6bQ71F801018E1",
  "5C4E88aD3C9A6bQ71F801018E15C4E88cD7aD3C9A61F801018E15CA64E88cD7aD3C91F801038E15C4E88d5",
  "7d13C9A61F801018E15CA64E88d57d13C91F80103XN2301XT2210XP22100YrfgpqWacadciWWmumcieieZca",
  "caXpYZYZpcWWWikiXpWvmZWWWZZpWiuciWWWWuWXnnnmgK0aWWWWWWnWWWWWWWWWWWWWWWWWWWWWWWmWWWWWWe",
  "WWWWYWWWWWWYWWWWemXYWWWWWW00YWWmWeWemWYWeWWXWaWWWmYWWWeWaWaeaWmWWWaWXWXXXWaWWWXWWeYaeW",
  "nWWWWXW10XmWWYWZXaWeWeWXaWaWWoWYWWfWXWXmoWWWaZaWvWimXWWWXWvWceZaWWWWeWmmmmmW00//////ul",
  "+l/l/kl/v/l//y/t//+lx///d/t/tdp+/+d/p/z/zzy/t/n/y//dxtd+y////z/TdmXmWmWnmWcWmWWZWeWWXm",
  "aWWWuWeWeuiXWXuWiWYWYYZWeWkWZWWuaeuXZWWWWYW20016045678"]
@[expose] def ext_full_compact_vmtf : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_sift_h : x64Isa.Hints := _decH #[
  "P7A0A2G0C010457072603022F0F2C020307063427280C0104533046DCABA59134410076DCABA594E8BFG3C",
  "18743018L86DCABA594E8BFG3376883010605C0790CB0cuWiuWvmiuXJ0aWWW00eWYWWYWWm00YeWceWimceW",
  "H0X//d/xZ/v/+lVuWayWcWXm00006045678"]
@[expose] def ext_full_compact_sift_h : List (SigEntry × Nat) := []

@[expose] def hint_full_compact_heap : x64Isa.Hints := _decH #[
  "XH3D1318000439192919291929110904123911021401001621012A0F010459092B0G022F0F27020E090B34",
  "29260F010456009055C7D93B84E05000055C4EB8937D115010055C4EB8937D115010055C4EB8937D115010",
  "5000000145C7D93B811401017XJL5C7D93B8XNIXMI167Y01008XJL5C7D93B8XNIXMIXQA3F168Y03019Y06X",
  "JL5C7D93B8XNIXMIXQA3E9B9a0304YG231212300XC2221322210xWXpWZcXpWciWYWpWWfoipauWL0eWWWWWW",
  "WmWWWWWmeWaeWWWWWWa00aWXWWeWWeWYWWaeaWYaWWWWWWo00fWWvWXoWvWYaWWWWWYWWWWWWW00Zt/y//il/d",
  "/v//tlp/xp/////+hVeWZWWpmWuWcWWemiWaiWWWWWXq00026045678"]
@[expose] def ext_full_compact_heap : List (SigEntry × Nat) := []

@[expose] def hint_full_compact : x64Isa.Hints := _decH #[
  "K30101B050E17131C0050350929083102152505185001100103246BB1F201006JCH3F746BBDE281602017J",
  "CH3F746BBDEM118701008L8JCH3F746BBDEM108000202001XR23020fYaWWWWuiZnubea30mXWmWWeaWWWW00",
  "XeWaeWWaYWmWn40eaWmeWWW00X///yl/td//tx+/+zNZmWeuWWeaXWXY80013045"]
@[expose] def ext_full_compact : List (SigEntry × Nat) :=
  [(("full_compact_flush", [i64], [i64]), 712),
   (("full_compact_mark_live", [i64], []), 88),
   (("full_compact_record_ext", [i64, i64, i64], [.bool]), 24),
   (("full_compact_bins", [i64, i64, i64], []), 104),
   (("full_wstack_defrag_m6", [i64], []), 136),
   (("full_compact_arena", [i64, i64], [i64]), 376),
   (("full_compact_vars", [i64, i64, i64], []), 152),
   (("full_compact_vmtf", [i64, i64], []), 56),
   (("full_compact_heap", [i64, i64], []), 72),
   (("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 344)]

@[expose] def hints : List x64Isa.Hints := [hint_full_compact_needed, hint_full_compact_flush,
    hint_full_compact_mark_live, hint_full_compact_assign_map, hint_full_compact_record_ext,
    hint_full_compact_bins, hint_full_compact_arena, hint_full_compact_vars,
    hint_full_compact_sift_q, hint_full_compact_vmtf, hint_full_compact_sift_h,
    hint_full_compact_heap, hint_full_compact]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_wstack_defrag_m6", [i64], []), 136),
   (("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 344)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Compact
