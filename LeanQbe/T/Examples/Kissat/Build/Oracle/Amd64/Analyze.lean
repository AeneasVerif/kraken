module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Analyze

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rsi, Reg64.rdx, Reg64.rbp, Reg64.rcx, Reg64.rax, Reg64.r14, Reg64.rdi, Reg64.rbx,
  Reg64.r12, Reg64.r13, Reg64.r15]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.r8), (.flag CondCode.nz), (.flag CondCode.z), (.gpr Reg64.rax), (.gpr Reg64.rcx),
  (.gpr Reg64.r13), (.flag CondCode.nc), (.gpr Reg64.rdx), (.gpr Reg64.r15), (.gpr Reg64.rsi),
  (.flag CondCode.le), (.gpr Reg64.r9), (.gpr Reg64.rbx), (.gpr Reg64.rbp), (.flag CondCode.c),
  (.gpr Reg64.r14), (.gpr Reg64.r12), (.flag CondCode.l), (.gpr Reg64.rdi), (.slot 3 .w64),
  (.slot 6 .w64), (.slot 9 .w64), (.slot 11 .w64), (.slot 10 .w64), (.slot 2 .w64),
  (.slot 4 .w64), (.slot 5 .w64), (.slot 8 .w64), (.slot 7 .w64), (.slot 1 .w64),
  (.slot 0 .w64)]

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

@[expose] def hint_full_ana_failed_lit_m6_hdr : x64Isa.Hints := _decH #[
  "dK202102131304050406171819032A31211B1C13141D322D0D032E3F0F030E0D0D01233302030306312207",
  "0E0G4G140E0007091103030E2634040E131E232402020304030604063122078122034G3372092704040621",
  "2202030E2F370723021103071E3F0E0F070E0303233301020303063122070E0G4G140E0302070706312209",
  "0E0G4G520G2007091103030E2634040E131E16281007091134040E131E7134042H02030316190609210F0C",
  "0D0G05000B0B5109010912210909A903470E12221302211401042117190204090204070909090007040706",
  "0400060904020904072E000B03010904037007091103030E2634040E131EX4001300106B4IKJX9KG560XDL",
  "X5BM8XBMONX7C2G4B0203D4IKJX9KG560XDLX5BM8XBMONX7CY2DXTF2G4DaW0203E4IKJX9KG560XDLX5BM8X",
  "BMONX7CY2DXTFY541GEaW01044Z10Z39Z274I13401014Z10Z39Z274I0400025Z10Z39Z274IZC3050006E4I",
  "KJX9KG560XDDXDLX5BM8XBMONX7CZV4a241GE010454IKJX9KG5602OP5020014I01000054IKJX9KG5601850",
  "100B4IKJX9KG560X5BX7CXDLM8XBMON5GFQ3RB0501F4IKJX9KG560b5QX5BX7Cb3GXDLM8XBMONb4Fb7R2SDF",
  "0220F4IKJX9KG560b5QX5BX7Cb3GXDLM8XBMONb4Fb7R13F0104F4IKJX9KG560b5QbKSX5BX7Cb3GXDLM8bLD",
  "XBMON3ORPFaW0303EbTO4IKJX9KG560bKSbURXDLX5BM8XBMONX7C3G47E0300E4IbTObKSbURKJX9KG560X5B",
  "X7CXDLM8XBMON2G7E0204KbTObVP4IKJX9KG560b5QbKSbURXDLX5BM8XBMONX7CbLDcL3cLTcFF2G4KoWW020",
  "0LbTObVP4IKJX9KG560b5QbKSbURXDLX5BM8XBMONX7CbLDcL3cLTcFFcN41GLoWW010G4eH0eJ9eI74I13401",
  "014eH0eJ9eI74I0400025eH0eJ9eI74IeS305000344IKJX9KfA80400007fC0fE9fD7fA84IKJX9K13701018",
  "fC0fE9fD7fA84IKJX9KfH308000214I01000044IKJX9KfA8174010254IKJX9KfA8g37050004D4IKJX9KfA8",
  "g37g64gQGgR5gD3gS0gPDgOCgNF0DX0002C4IKJX9KfA8g37g64gQGgR5gD3gS0gPDgOC0CX000214I0100011",
  "4I01000324Ii730200024jV0k19k074I13401014jV0k19k074I0400025jV0k19k074IkA305000QR43A0331",
  "O63923B3364XL2209ZN813035311Z/////V381H23706632514034462236183253841103414224AD223B823",
  "1442211S2209X922499234144140354XI22463230602260O230692260022602224632203b12306322600Ya",
  "ZWoWYXkkWWWcWWWWYpWaupYWWxZjwucaWZwWWufWcid+WnWueauXYXmfWXWWWWZiWcdWWWWxWXnuWdWWkeeucW",
  "WXmiWqWxWuyxWuyWWjmXYXmfWXWWjmWuyWyWWyuvrgqvvoqXeD0eXWYWmWWWWWWWWWWWWWWWWWWWaWWWWWWWma",
  "eWWWWWYWWWWYWeWWWaaWmXWeWWWWWWWWmmWWaWWWaaWXWWWWWWWWnWWWWWWWWWWWWWWWWWWWaWmXWeWWmWWYYW",
  "WWWWWWWWWWWWWWWW00aWmXWeaWWWWWWWWWWWWaWnYaaYWWWWWWWeYaWWXXYXeWeWXWaWmWYYWeWmaYWWYWWWee",
  "eemYWWYYYYamWnWmoWWeqYaWmWWWXXWWXXXabWWYWeWmaYWeWXXXXYWaeXWYWWXYYWXWYG0XWWWWWWWWWWWWWW",
  "mWWWWWWWWWXWWWWWWWWfWWWWWWaWWWWWeWWeWWWmWWWWWWWWaWWXWWWWXWWWeWZoicWWiYWWWWaWWWXWWaXWWa",
  "WWWWWWWmWWWWWWmWWaWkXciWWWWWWWeWWW00l/p+/z/lt////+WlWpzolt+zxttv//////llxt//zzxzl/l/y/",
  "t+//xv/l+/tx//x///lllklv//xxxxo/+j+kx//ktxt+////zz//zzydn//v/l+/tx/d/zzzzx/tWy/x//zxx/",
  "z/wViXWYWmeWWWWX/m/iYjmeXYaeecWWWWWWmmaeWWYYaYmWmWZWeXWWacWmXWeaWWaWWWmmmnmcWWaaaajWXo",
  "XnaWWneaeXWWWWYYWWYYZukWWcWmXWeaWuWYYYYaWe/ZWaWWYaaWYWb000C672895A"]
@[expose] def ext_full_ana_failed_lit_m6_hdr : List (SigEntry × Nat) :=
  [(("full_bump_analyzed_mode_fid", [i64, .bool], []), 184),
   (("full_backtrack_ac_fid", [i64, i64], []), 184),
   (("full_ema_update", [i64, i64], []), 88)]

@[expose] def hint_full_restore_bump_ana_mode_fid : x64Isa.Hints := _decH #[
  "XC411B1C0E0C101D151F0143030E2227140E2G06014C0C030E31220E24170E210007091103030E2634040E",
  "131EB000000017IDG0ABMFK54I5T17701008IDG0AB4IECMFK55T274802019IDG0AB4IECMFK55TP41790103",
  "24I5T14201018IDG0ABMFK54I5TXAG247802019IDG0ABMFK54I5TXAGXE7149010500000014Y60Y89Y774I1",
  "3401014Y60Y89Y774I0400025Y60Y89Y774IYH305000332310YO2306022600YaZWoWYWaWiWuyXmXWZXmiYr",
  "YJ0eXWYWmWXWmWoYXWWeaWaaWWWW00aWmXWeaWmeWfXWmXaYWYYWeWW40XWWWWWWWaWWaWmWWXWWaWWW00/p+/",
  "z/lt+/d/jz+/ztv/xx/l/lNiXWYWmeXWuWoYXWYecWaaWmWm8002572895"]
@[expose] def ext_full_restore_bump_ana_mode_fid : List (SigEntry × Nat) :=
  [(("full_bump_analyzed_mode_fid", [i64, .bool], []), 184)]

@[expose] def hint_full_analyze_reasons_fid : x64Isa.Hints := _decH #[
  "ZQ311D190E091G15131814170143030E2227140E2906014303030E31220E2F140E22211301032113030221",
  "033I39010E121E07030E033E04062303030E2311110303030E31220E044103041639060904062300260333",
  "03030E31220E0I440E0B1E211303130E1423030E130E21130E04032103030E2634040E131ER000000018H5",
  "FG9DL8JU4CNJPT17801009H5FG9D4CD9L8JUNJPT27490201AH5FG9D4CD9L8JUNJPTS417A01038FG9DH54CN",
  "JJUL8PT1F80101AH5FG9DL8J7JU4CXD9NJPT2F4A0201BH5FG9DL8J7JU4CXD9NJPTXH41FB01064FG9DH54C0",
  "400009NJ9DJU4CH5FGL8PTY6F0900009FG9DH54CNJJUL8PTY6F0900029NJ9DJU4CH5FGL8PTY6F0900009NJ",
  "9DJU4CH5FGL8PTY6F090006CNJ9DJUZ974CZC3ZCOH5FGL8PTY6F1BC01006FG9DH54CY6FZ97060002D4CH5F",
  "G9DL8NJJUY6FZ97ZCOZFBZH4PT13D0101CNJ9DJUZ974CZCOH5FGL8PTY6FZFB0C0000D4CH5FG9DL8NJJUZ97",
  "ZCOZFBPTY6FZS30D000AE4CH5FG9DL8b10NJJUZ97ZCOZFBaP9Y6FPT14EYW0101F4CH5FG9DL8b10NJJUZ97Z",
  "COZFBaP9Y6FPTb240FYW00064FG9DH54C0400014FG9DH54C0400005FG9DH54CY6F13501015FG9DH54CY6F0",
  "500024FG9DH54C0400014FG9DH54C13401014FG9DH54C0400025FG9DH54Cd3305000702076M6311333304Z",
  "K2326F23249220072263XH22011gC51YaZXaWfWmiWmiWaeceWjmXnuZmmuWkaWxWZZmWmiXmXmWWWdkiaZWaZ",
  "YWcWikWuWmXmucXgrYJ0eXWaXXWWXWmaWWWWmWeWXaaYWYWYYWmeWYeeaYaXWaeWWWWWWWWeXWeWeWfXWmWaYW",
  "YYWWWWW00aWmYWmmWWmeYWYWWemaWWoYXWXWXXWeaWXaaYXYWmYaWWoYmWXWaWmaeaWammeWoXWXXWaWWW40XW",
  "WWWaWWWWaWWWWWWWmWWeXuYWucWWXWWWmWWaWmWWWWWZcWWWWWWWWYWWYWeWWWmWYWWWW00lp+/x++/p+/lx/x",
  "//k/p/+xxz/z/yz/dt/zttxzx+/xtt+xw/+z/t+/tlp/s+/l+xy/zz/t//lNiXWaXXWiXWmaWaWWnWiWXaaYWY",
  "WZYWueWYeeaYaXWaeeXabWXYWeXWemiWfXWmXaZWYYWeWWm8004672895A"]
@[expose] def ext_full_analyze_reasons_fid : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_div", [i64, i64], [i64]), 24)]

@[expose] def hint_full_analyze_core_m6 : x64Isa.Hints := _decH #[
  "ZF2F1G131505C11D1202021212020212121302211401042117190204090204070909090I07040706040I06",
  "0904020904072E0I000301090403000657070727010I0903040E2222210210190I1103030E2637070E141E",
  "1231130E1109030407070203040311120203040E040633130E22G00130010054C8GAUD56F1D5010834C6F8",
  "G03000444C6F8GXC304000214C1D1010044CYT06F8G39344030224CZGD0200011ZJD0100022ZJD4C020001",
  "5ZR0ZUIZT9ZJD4C14501015ZR0ZUIZT9ZJD4C0500026ZR0ZUIZT9ZJD4Ca740600026SD4C8GAUD56F060001",
  "6SD4CD58GAU6F0600016SD4CD58GAU6F0600016SD4C8GAUD56F06000402076L2304ZS2024ZF22301a451um",
  "WWekWWYYWWYYXieYaZWoWYgWcaXWWuuWWWXmWWWWquXcammWeWX//oL0YWYWWWnXWWWWWmaXWeXWYWmWWammaa",
  "WWWWWWWWWWWWWWeWWYaWWWWWWW00XWXWWWemqaWWWeYWmaWmXWeaWYeeYYWWWmWWWWWWWWXWaenXYqoqYWWW00",
  "caWWWWaWWWWWWWXWWWWWWWWWWaieWWWWWWWaWWWWWWWWWWWWWWW00lz/z///c+dt+/tlx+/p+/z/lt/xllxvZ/",
  "+//mZua/ipz/tkzzucudx///VYWYWWWvXueXWemaXWiXWYWmeWammacyWXWWlydxWpiYWenYYdvduaWWW00015",
  "72895"]
@[expose] def ext_full_analyze_core_m6 : List (SigEntry × Nat) :=
  [(("full_one_lit_confl", [i64], [i64]), 376),
   (("full_deduce_1uip_m6_hdr", [i64], [i64]), 504),
   (("full_min_shrink_m6", [i64], []), 424),
   (("full_analyze_reasons_fid", [i64], []), 120),
   (("full_ema_update", [i64, i64], []), 88),
   (("full_learn_clause_m6", [i64, i64], [i64]), 936),
   (("full_bump_analyzed_mode_fid", [i64, .bool], []), 184),
   (("m6_hdr_init", [i64], []), 0),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 88),
   (("full_restore_bump_ana_mode_fid", [i64, .bool], []), 248),
   (("full_ana_failed_lit_m6_hdr", [i64], [i64]), 344)]

@[expose] def hint_full_analyze_m6_hdr : x64Isa.Hints := _decH #[
  "232221001300101A23060XJ000Y4000/xNa80010"]
@[expose] def ext_full_analyze_m6_hdr : List (SigEntry × Nat) :=
  [(("full_analyze_core_m6", [i64], [i64]), 1000),
   (("m6_hdr_dr_update", [i64], []), 72)]

@[expose] def hints : List x64Isa.Hints := [hint_full_ana_failed_lit_m6_hdr,
    hint_full_restore_bump_ana_mode_fid, hint_full_analyze_reasons_fid,
    hint_full_analyze_core_m6, hint_full_analyze_m6_hdr]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_bump_analyzed_mode_fid", [i64, .bool], []), 184),
   (("full_backtrack_ac_fid", [i64, i64], []), 184),
   (("full_ema_update", [i64, i64], []), 88),
   (("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_div", [i64, i64], [i64]), 24),
   (("full_one_lit_confl", [i64], [i64]), 376),
   (("full_deduce_1uip_m6_hdr", [i64], [i64]), 504),
   (("full_min_shrink_m6", [i64], []), 424),
   (("full_learn_clause_m6", [i64, i64], [i64]), 936),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 88),
   (("m6_hdr_dr_update", [i64], []), 72)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Analyze
