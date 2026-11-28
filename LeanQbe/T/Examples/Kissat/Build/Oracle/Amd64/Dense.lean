module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Dense

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r8, Reg64.rdi, Reg64.r12, Reg64.rsi, Reg64.rbx, Reg64.rax, Reg64.rcx, Reg64.rdx,
  Reg64.r14, Reg64.rbp, Reg64.r13, Reg64.r15, Reg64.r9]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rax), (.gpr Reg64.rsi), (.gpr Reg64.rcx), (.gpr Reg64.rdi), (.flag CondCode.nc),
  (.gpr Reg64.r8), (.flag CondCode.c), (.flag CondCode.nz), (.flag CondCode.z),
  (.gpr Reg64.rdx), (.gpr Reg64.rbp), (.gpr Reg64.r15), (.gpr Reg64.r12), (.flag CondCode.g),
  (.gpr Reg64.r13), (.gpr Reg64.r14), (.gpr Reg64.r9), (.gpr Reg64.rbx), (.slot 2 .w64),
  (.slot 1 .w64), (.slot 4 .w64), (.slot 3 .w64), (.slot 0 .w64), (.flag CondCode.ge),
  (.flag CondCode.l), (.slot 6 .w64), (.slot 5 .w64), (.flag CondCode.le), (.slot 7 .w64)]

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

@[expose] def hint_full_dense_occ_cnt_fid : x64Isa.Hints := _decH #[
  "M400132023303041503064700020208264701020200062001000103369M5N322030201020014Q51052C510",
  "52lWW+XXvP0eWWmWW00mWamWeeW00YXWaYWWuK0X+e/sn/dl/VXtWfkWumW00000"]
@[expose] def ext_full_dense_occ_cnt_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_enter_dense_ex_fid : x64Isa.Hints := _decH #[
  "ZU4727272A2727173006180717371818272717300618071750121000971B0B013C18043000062D12390906",
  "2D00060100000C000007000E0F1031010000040002071609030609090306250G230339090307020452000A",
  "06090438480000040008020450030A062A061109020100066303000617001637000602020202021216O001",
  "00010024H5C02000334H5CHA103010134H5CHA03000234H5CHA03000524H5C02000424H5C02000224H5C02",
  "000554HY3IY8JY52Y5K10501015Y3IY8JY5K4HYJ00500028Y3IY8JY5K4HYJLYQCYLBYM108b000074HYLBYJ",
  "LYQCY3IY8JY5K078000AY35Y3IY83Y8JY5K4HYJLYQCYLBYM110Aq0102BY35Y3IY83Y8JY5K4HYJLYQCYLBYM",
  "1Z700Bq000494HZSEZTFYLBYJLYQCY3IY8JY5K1A9X0100A4HZSEZTFYLBYJLYQCY3IY8JY5KZUA0AX000014H",
  "010001B4HZSEZTFYLBYJLYQCY3IY8JY5KZUAa310BXX0002E4HZSEZTFYLBYJLYQCY3IY8JY5KZUAa41a31a92",
  "a800EYX0000E4HZSEZTFYLBYJLYQCY3IY8JY5KZUAa41a31a92a800EYX0007I4HZSEZTFYLBYJLYQCY3IY8JY",
  "5KZUAb13aM5a41aVMaNGa31a92a800IXeX00094Y3IY8JY5K4H12401036cF9cG2Y3IY8JY5K4H10601006Y3I",
  "Y8JY5K4Hd10cG206000704023041ZV2325E431534692335E2272X62283XH23071i051eWWdWYX/WWWWWWdiW",
  "WWXykWWXxWXvoWWWWWWdWWWWWcXucXuYyWl/beYebWYWZoXpWWXeWmWymixci30XWWWmeWWWWWaWnWWXYXWaXW",
  "mmWWeWWWaWWeqWWWYWWmWmWWmYeWWWWWXWWWWWWWWWWYaWWWWaWXWWWW80mWWeaamWeWYWWmWWnWmYWmeeWWam",
  "WWWmaaYaWWXWWeeeWeeXaWWmWWWWWWWaqeaYafXWWXbYXWnWem40mXWWavWWWWWWZaeWWWiYaWWvYaumWWWWWY",
  "ZmWYWWWWyWWmWimWWWWWWWWWWWWWWWWWWWWWWWWWWW00d+/+lltsX/d/v/+l/+j+/x+/dd//ol//+/ttxt//z/",
  "/dll/llzt/+////////sdltxtjz//znxz+z/k/NXWXmmef+WuWcWXmWXoXWaXWuuWWjmWWXWeeaeWWYWWummWm",
  "mYeWXWWWWWWWWfumeaeoYWWYkaYXYWnW80056492A8B"]
@[expose] def ext_full_enter_dense_ex_fid : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_arena_sweep_m6", [i64], [i64]), 504),
   (("full_sweep_bins_m6cf", [i64], []), 264),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hint_full_enter_dense : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_enter_dense : List (SigEntry × Nat) :=
  [(("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 792)]

@[expose] def hint_full_rebuild_watches_nosort_fid : x64Isa.Hints := _decH #[
  "A38080828082808081808400100010226H4A02000314A01000224AFH0200030209122045H20450eXW10YWW",
  "We00gXgYmb8000//hzZw/qFqYybWhG000249"]
@[expose] def ext_full_rebuild_watches_nosort_fid : List (SigEntry × Nat) :=
  [(("full_arena_sweep_m6", [i64], [i64]), 504),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696)]

@[expose] def hint_full_rebuild_watches : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_rebuild_watches : List (SigEntry × Nat) :=
  [(("full_rebuild_watches_nosort_fid", [i64], [i64]), 728)]

@[expose] def hint_full_m6_dense_prop_lit : x64Isa.Hints := _decH #[
  "ZF2115050104112N121C1930003E0E0ED6320G17042F0B0F00160A0A093C17060C0006303000062D080904",
  "22060000000C06280809280202141G040H270G0C0F0A0G0A09095709070918270909A902463A09042D0O0H",
  "0H1410040F27000B0000000009095709070918270202A0004656E0010001020000000843APD195MIKCKMX1",
  "E1080100843APD195MIKCKMX1E1080107BXRB43APD195MIKMX1EYACY1AY2J0BXW00009XSF43XRBAPD195MI",
  "KMX1E29090200DXRB43APD195MIKMX1EYACY1AY2JXSFY6C39H2DbW0300EXRB43APD195MIKMX1EYACY1AY2J",
  "XSFY6CYF2290EbW02078XRB43APD195MIKMX1E080005GXRB43APD195MIKMX1EZ70ZSJZTLZF2ZUAZRFZQCZP",
  "K0G0002FXRB43APD195MIKMX1EZ70ZSJZTLZF2ZUAZRFZQC0F00059XKG43APD195MIKCKMX1E090003IXKG43",
  "APD195MIKCKMX1Eb5AbQLbRKbDHbS0bPJbOBbNQXJ20IaWW0002GXKG43APD195MIKCKMX1Eb5AbQLbRKbDHbS",
  "0bPJbOB0G000R823632225652302922C6I2327J226272317XB2220T234C02319A233CH22C4G22C332271A2",
  "220722200222002220S2355023150233502345S227552261A226432263G22360XgmWxZjwucaWZwWWufWiWX",
  "gWZijthWumWleWZXaZWWWWWWcXuWbuacYid//Zprfq20YWWYWWWWWWWmaeWWWWWWWWWWeWWWWWWYWnWWWWWWea",
  "YWYWYWmWWWWWWWWWWWWWWWW00XWWXWWWWWWWeYaWWXXYYnWWWaWWWWWWXWemWWaaeaYnWXWneeWneWeWqWeWWW",
  "WWYX00XWWWWWWWWfWWWWWWWWWWWaWWWWWWWXaWWWWWWWaWWWWWyeWvWYWaWWWfnWWW00dz//z//////llxt//z",
  "zxuyl//t/////zz/k///ttltwz/y+ill+jl/d+t/l/////xzVYWWYWWWWWWmmaeWWYYadZmWWeWWWWWYYWnWWW",
  "eemebYWZXpmmXomWuXeWmWWWWWaY00076492A8B"]
@[expose] def ext_full_m6_dense_prop_lit : List (SigEntry × Nat) := []

@[expose] def hint_full_m6_dense_prop : x64Isa.Hints := _decH #[
  "82A30161818182100200100010024H6A020001020410XofaT0XWXWm00me00mWW00l/sxlVfam0000249"]
@[expose] def ext_full_m6_dense_prop : List (SigEntry × Nat) :=
  [(("full_m6_dense_prop_lit", [i64, i32], [.bool]), 104)]

@[expose] def hint_full_dense_prop_unit_m7 : x64Isa.Hints := _decH #[
  "YV30001H02042R101C1E010130003F0F0F16310B1704220B02050500173G073232022D0809042006000000",
  "0G000628080000000G002601012O08162630003505051642170422030209090G17311720002D041232022D",
  "00060G00000100060616I0010001027AHLEJC4AH9HIB207000074AHIBJX2FAHLEJC107010074AHIBJX2FAH",
  "LEJC1070104BXGB4AHIBJX2FAHLEJCXQGXJ5XKM0BXe0000B4AXGBHIBJX2FAHLEJCXQGXJ5XKM291BXe0200B",
  "XGB4AHIBJX2FAHLEJCXQGXJ5XKM3910BXe0302CXGB4AHIBJX2FAHLEJCXQGXJ5XKMXU0291CXe02038XGB4AH",
  "IBJX2FAHLEJC0800018XGB4AHIBJX2FAHLEJC08000900000005AHLEJCZM54A13501005AHLEJCZM54A13501",
  "049a43AHLEJCZM54AaE1a79a8G09g00006a43AHLEJCZM54A0600009a43AHLEJCZM54AaE1a79a8G109g0105",
  "6a43AHLEJCZM54A0600016a43AHLEJCZM54A06000502091M23254227262316J23050ckWcihoWuhmnvuYWWi",
  "WYWWWWWWWWZdWkeZXcYddYqu90aXXWWaWWWWXWWWWWWWWXWfaWXWeWeaWWmXWWWWWWWWWWWWWW00YWmmWYeWXe",
  "WmaWYmXWWWmaYmWmWWbYWWeeqWXWmWgWaWWWXY00XWWXdWXaXmeeWmaumWWWYWWWmWWaWWWWpmcXXWYWpYmWW0",
  "0lx++//vl/zl+/t/w/z//+/tu/+///nx//dct/z+//h/t///zxVaXXWWcmWYmXWeWbWYWWXWedWXWWWkaWWuve",
  "WYXWWqWeWWWYa00036492A8B"]
@[expose] def ext_full_dense_prop_unit_m7 : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 232)]

@[expose] def hint_full_dense_flush_units_m7 : x64Isa.Hints := _decH #[
  "A2C104618210A12040018300100010024H6C102010024HB0020001020410aWZYbL0XWem00ae00XWW00Xk//",
  "tlVnWWem00003492"]
@[expose] def ext_full_dense_flush_units_m7 : List (SigEntry × Nat) :=
  [(("full_dense_prop_unit_m7", [i64, i32], [.bool]), 312)]

@[expose] def hint_full_watch_large_clauses_fid : x64Isa.Hints := _decH #[
  "c62F1H1E2089060505003G0B02010006630300061700163700060200000000101804000G000420002D0800",
  "0029090000200000004131012D080101210101012101010116030900061700033230002D08000029090000",
  "200000004131012D08010121010101210101011603090006170003325133090002020402050716050G0605",
  "050G06250G25053G0G0507050459020G043848020004000802045205210002020402090716090506090905",
  "06250929093G0G0907090459020G04384802000400080204520944R000000005AE8H6FDS4A1C50101B4A6F",
  "LCVBAE8HP5DSM9UGQM10BXm0103CX02M9AE8H6FLCDSUGQM4AVBP510Ci0100C4A6FLCVBAE8HP5DSM9UGQMXH",
  "00CXm00027XV0AE8H6FDS4ALC07000384AXVI6FLCVBAE8HDS080001AAE8HP56FLCUG4AVBXVIDS19AX0102A",
  "AE8HP54AVB6FLCUGXVIDS13Aa0100AAE8HP56FLCUG4AVBXVIDS3390AX0300DAE8HP56FLCUG4AVBXVIDSZ00",
  "YV9YU311DX0103AAE8HP54AVB6FLCUGXVIDS0Aa0001AAE8HP54AVB6FLCUGXVIDS19Aa010294AXVI6FLCVBA",
  "E8HDSP51390100AAE8HP54AVB6FLCUGXVIDS3039Aa0300DAE8HP54AVB6FLCUGXVIDSaV0b19b0311Da0104C",
  "4AXVI6FLCVBcH3cHJAE8HDScD1cDM0CZZ000014A010001D4AXVI6FLCVBcH3cHJAE8HDScD1cDMcI90DZZ000",
  "2G4AXVI6FLCVBcH3cHJAE8HDScD1cDMcJ0cI9cOQcN20GZZ0000G4AXVI6FLCVBcH3cHJAE8HDScD1cDMcJ0cI",
  "9cOQcN20GZZ0006L4AXVI6FLCVBcH3cHJAE8HDScD1cDMdG5d5LcJ0dEPd6Gd6KcI9cOQcN20LXZZ000714A01",
  "0001BXVIAE8H6FDS4ALCcH3cHJeM1VB0Bi0002EXVIAE8H6FDS4ALCeN0VBeM1cH3cHJeSLeR20EZW0000EXVI",
  "AE8H6FDS4ALCeN0VBeM1cH3cHJeSLeR20EZW0006JXVIAE8H6FDS4ALCfK9f95eN0fIKVBfAGfAMeM1cH3cHJe",
  "SLeR20JZXW000U02091F2375E2305X9226002325bE230332311C421123012350F4211230623304434C2C30",
  "236C322055220452203B22C4C2273A22C5522645227364211230I2337M23075234C3227352270H22C0N22C",
  "3522601XV51oeWdiWWWXykWWzmWyvWWWWWWWmWkuWWWZuyWXxWXvoWWWWWWZsyZmWWXmcWvuXmcWvukWWWcWuZ",
  "dWcWuZcWWaWWZmXW/mZmX/sL0XWWXYXWaXWmWWaWWWYWWaeWWYWWYaYWeYXWWWeWWWaWWemWWWWWXYWWWWWWWW",
  "WWWWWWaeWWWWWWWWWWWWeamWWeaWWWWWWmWW00aWWWWWnWmYWmeWWYeWWWeYYXYWWWWXYXWaXWmWWamWWWmaaY",
  "aWWWWWnWWWWbWWWWWbWWWYaWWWWqWWWWWqWaYeWWaYYeWaWWeWW00ZaeWWWiYaWinYieWWWWWXWWWcemWWWuae",
  "WvYaumWWWWWYXoiXuWWeuZWayeuZWaudWWXZWiWpnZWiWoZWWWeWmWYimXoWWW00Zt////+j+/x+/d//vd///l",
  "xxzx////yxz/tz+l//ol//+/ttxt////+yp///n/////n///xol//+d////+d/pxl/dtxxW/p//l//VeWWWWXo",
  "XWaXWuWWcuWWWmaaYaWWWWZaYWeYXmWWjmWWXWeeaeWWWWXZiWWWkWWWWWkWWWajmWWXuWWWWXuWiamWueaa/W",
  "iWWmWW00086492A8B"]
@[expose] def ext_full_watch_large_clauses_fid : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hints : List x64Isa.Hints := [hint_full_dense_occ_cnt_fid,
    hint_full_enter_dense_ex_fid, hint_full_enter_dense, hint_full_rebuild_watches_nosort_fid,
    hint_full_rebuild_watches, hint_full_m6_dense_prop_lit, hint_full_m6_dense_prop,
    hint_full_dense_prop_unit_m7, hint_full_dense_flush_units_m7,
    hint_full_watch_large_clauses_fid]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_arena_sweep_m6", [i64], [i64]), 504),
   (("full_sweep_bins_m6cf", [i64], []), 264),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_add_unit", [i64, i32], [.bool]), 232)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Dense
