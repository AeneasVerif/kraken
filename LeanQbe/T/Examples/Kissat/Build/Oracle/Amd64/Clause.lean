module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Clause

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rbp, Reg64.rdi, Reg64.rcx, Reg64.r8, Reg64.r9, Reg64.rdx, Reg64.rax, Reg64.rbx,
  Reg64.rsi]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rbx), (.flag CondCode.z), (.flag CondCode.c), (.gpr Reg64.rsi), (.gpr Reg64.rax),
  (.gpr Reg64.rdi), (.gpr Reg64.rcx), (.flag CondCode.nc), (.gpr Reg64.rdx), (.gpr Reg64.r8),
  (.gpr Reg64.r9), (.flag CondCode.nz), (.gpr Reg64.rbp), (.slot 2 .w64), (.slot 0 .w64),
  (.slot 5 .w64), (.slot 4 .w64), (.slot 6 .w64), (.slot 3 .w64), (.slot 1 .w64),
  (.flag CondCode.g), (.flag CondCode.l)]

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

@[expose] def hint_full_add_clause : x64Isa.Hints := _decH #[
  "eR50010203041516050204140708250871190409071A440A0A440A0A440A0A44080A07121A440802031808",
  "050314040714190B12090A0219090A02391A29093909090B090758040A0731410414070401040754092308",
  "080314040714190B12090A0219090A02391A29093909090B090758040A0731410414070401040754099104",
  "04180807151833033A0A020922000303020807A80907123802009808080306060314040714150B12050902",
  "15050902351929093A0A090B090B28040A073104140B0401040B2409130314040714150B12080902180809",
  "02381929093A0A090B050B26040A073104140B0401050B240924060803030825051B06050628082B030835",
  "051404071914360633030108220A0606020407A408071234020AX800140010244C90537D16441024X364C9",
  "07D0400006X364C9053X897D18681006X364C9053X897D18681006X364C9053X897D18681045X364C907DY",
  "O50500002X3E4C0200017X364C907DYO5YK3YN807X0002AX364C907DYO5YP3YN8YK3Z1FYV40Aa0000AX364",
  "C907DYO5YP3YN8YK3Z1FYV40Aa0006EX364C907DYO5ZS9ZGGYP3ZQHZIIYN8YK3Z1FYV40EYe00073X364C7D",
  "0300003X364C900300017X364C7D90b33b58YO507G002AX364C7Db63YO5b58bC490b33bEF0Ae0000AX364C",
  "7Db63YO5b58bC490b33bEF0Ae0006EX364C7Dc99bTIb63c7HYO5bVGb5890b33bEFbC40EYY00071X3601000",
  "55X364CdV5dP4eH00500007X364CdV5dP4eH0eBAeJ318701007X364CdV5dP4eH0eBAeJ318701007X364CdV",
  "5dP4eH0eBAeJ3187010544CfQ6fQE90040000000000164CfQ6fQE90fO3fN806G00294CfQ6fQE90fR3fN8g1",
  "4fO3g3J09a000094CfQ6fQE90fR3fN8g14fO3g3J09a0006D4CfQ6fQE90gU9gI5fR3gSDfN8gKIfO3g3Jg140",
  "DXa000624C9002000024C9002000154C90hP3fQ6fQE05400284C90hQ3fQ6fQEi04hP3i2508Y000084C90hQ",
  "3fQ6fQEi04hP3i2508Y0006C4C90iT9iH8hQ3iRJfQ6fQEiJDhP3i25i040Cn0006000000344CkR9kL5lDA04",
  "000064CkR9kL5lDAl73lF6146010064CkR9kL5lDAl73lF6146010064CkR9kL5lDAl73lF6146010XS020014",
  "2322H2212YR23530430231124220211F4302311242202118234344373234023632233402235B2234B2243C",
  "2254B224552263522543430231124220211H2353023021222002220F230212220022208233344373233023",
  "632234402235B2213B2244C2253B22455226452253323021222002220ZG2220A2302E222012311G2220823",
  "33523243223152233D2243G22415226382220XD23235231492212D2242M22620dWZWWgrguWWuddgYZmvmfm",
  "aWXmWWmdWWiWdcsWXWWWgYWWcWWYWyWXmWywuWaWWXeeXXaohmXmWbgriWWiZprXWZkkWWkuWWeXykWWzmWywu",
  "WaWWXeeYWXxWWXWdnuWZsWZphWWmWWbXXWZuWW+ZulXyWedkcaXe10XWaeWWWWYWWWWWWWWWWWWWWWWWWWWWWW",
  "WWWWWWWaWWWWWWWWWWWWWWWWWWWWWmWWWWWWWWWmYaWWWWXWWWWWWWeWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWWWWWWmWYWWnWWWWWWWWWWWWWWW00mYaWWWWnXXWWWmWWWWWWWWWYaYWeaWWoWWWWmYYXWmW",
  "WWemeXWmWYeWWWYWeeaYWWWWWWWeXYWWWWemmmWWeWaWWWWWXYXWYWmeWWYeWWWYWeeaYWWWWWaeaWeYXWWWfW",
  "WWWeXXWmeWXWWemWWWWWWaYWWWWeWK0XWYWWWeeeWZYWeWWWuWuWWWnWWWXYWaepYWWWWWWWeWWYaWWWaeWnYi",
  "eWWWWWWXWWWWWWWWmXWWWaaaWXnWaWWWWWWcemWWWiYaWinYieWWWWWWXWWWWvYWWWXmemXoafnWWWWWWWaWWW",
  "qWebmsYugXWZcYWaY00X//+lxp///+jyz//+//z/+/////vtx/lp/+f///+/xxz+////c/lz+l/vd///x/lltx",
  "///////dzv////c+k///l/t/////yxz/x+/d//vd///x/lltx/////plt/lxy///a////lzz+/l/y//kl/////",
  "/tx//+/Xk7XmaiWWWXoZYWWXWWYWXWWWWWceaWmiWXsWWWXWaaYXWWWWvWmYXmWcuWWWaWmmeaWWWWWWWuYcWW",
  "WWvXnWWWmWeWWWWWZaYWaXWuWWcuWWWaWmmeaWWWWWimeWmaZWWWxWWWWmYYXWmWZWWnmWWWWWWeaWWXW+nO00",
  "8270"]
@[expose] def ext_full_add_clause : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hint_full_add_bin_m6 : x64Isa.Hints := _decH #[
  "bH430400070C070A0116140K190K0L0L1L010L161A9407090309340439090902361B040601041206060404",
  "14130B1203090213030902331929093A0A090B090B26040A073106160B06010A0B260916060716140B1203",
  "090213030902391A23033404030B030B240604073104140B0401060B24033406030629091B0A090623031B",
  "080358080733070B13191C141A140A0A5B160B06212B0606B40444040733072B1319101313130A5B160B06",
  "212B0606B604O001400105A45H6EACC836850A0J4M90Ax0002645H6EACC836806X000354568CCA05005I00",
  "08XE3X1A455068XQ9CCA0148O1018XE3X1A455068XQ9CCA0148O1035456850CCYBD05600014E0100006456",
  "8YBDCC50Y9606I00294568YBDCCA0Y96YD450YFI09a200094568YBDCCA0Y96YD450YFI09a2006D4568YBDC",
  "CZA9YU3A0Z8GY96Z0F50YFIYD40DXa2006345685003600014E0100014456850YBD0460027456850CCYBDa9",
  "6aBI0760007456850CCYBDa96aBI076006B456850b63aQ9CCb4GYBDaSAaBIa960BY6006000000394550dDJ",
  "dFDcU8dH4dBCd99d7309200284550dDJdFDcU8dH4dBCd99082001000000394568f9DfBIeO4fD3f70f59f3G",
  "09200284568f9DfBIeO4fD3f70f5908200X902078YS2326323380430131524210251F43013152421025182",
  "353523443223352235D2245G2243522655430131524210251923360430131524210251F430131524210251",
  "E23463226352262G2262D2263522625430131524210251X1221022210O231612324XE222232221V2348123",
  "2812338T2244H2283322220XsczwuccWe+ngrcdWWcuxthWuuXZwYrgXuYfufmfmoWXmWWmdWWiWdcsWXWWWgW",
  "WZWWXWkWWuWkjiWYWWWqWWWhWddW/+qWeWeqW10mYYWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW",
  "WWWWWWWXWWWWWWWWWWWWWWWWWWeWWXWWWWWWWWWWWYeWWW00eXXWWWWemeWWWWWWWXWaaWWWWqYWWWWWWWWWWY",
  "aYWeaWWoWWWWmYYXWmWWaeaWmeWXaWWWXWaaYWWmmmYWWWWWXgXbYXaG0YWWWWWWWWYeWWWWWWWeWWWWWWWWfW",
  "WWWWWWWWuWuWWWnWWWXYWaepYWWWWWWWeWXYWWWYaWencaWWWWWWWWWWXWpYmkkWWWWWWW00d///////llzz//",
  "//k/l//////zz/tt///+tx//+/+/////vtx/lp/+f///+/xxz+///plt+/d/yp///z/ttx/++k/x//p//zhzrx",
  "yWVmmYYWWWWnWmWWWWWWYYWeeWWWXeaWWXWXWWWWWceaWmiWXsWWWXWaaYXWWWimeXWuWZiWWWYWeeaWXXnWaW",
  "WiWWYqYgaZ/0006270"]
@[expose] def ext_full_add_bin_m6 : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hint_full_add_bin : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_add_bin : List (SigEntry × Nat) :=
  [(("full_add_bin_m6", [i64, i32, i32], [i64]), 296)]

@[expose] def hint_full_add_unit : x64Isa.Hints := _decH #[
  "T4B04042716032K0L39071B191A1919191903035B160B06212B0606B604500140010024558022004000000",
  "294558X3IX5GA4X79X1DVATF09200284558X3IX5GA4X79X1DVA08200B020584430131504210251T2353123",
  "231233312343U228552222B2284322230ecuxthWuuXZwYrgeycfm30YWeeWWWWWWWWW80XWaaWWWWoXeYW40e",
  "WWWWWWWWfWWWWWWWW00l//////zz/tt///+xylx/NYYWeeWWWXaZmaW80060"]
@[expose] def ext_full_add_unit : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168)]

@[expose] def hints : List x64Isa.Hints := [hint_full_add_clause, hint_full_add_bin_m6,
    hint_full_add_bin, hint_full_add_unit]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_backtrack", [i64, i64], []), 168)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Clause
