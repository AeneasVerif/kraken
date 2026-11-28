module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Lucky

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r9, Reg64.rsi, Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.r13, Reg64.r14, Reg64.r15,
  Reg64.rdi, Reg64.rdx, Reg64.rax, Reg64.rcx, Reg64.r8]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rbp), (.gpr Reg64.r8), (.gpr Reg64.rdx), (.gpr Reg64.rcx), (.gpr Reg64.rbx),
  (.gpr Reg64.r14), (.flag CondCode.nz), (.flag CondCode.nc), (.gpr Reg64.r12),
  (.gpr Reg64.rax), (.flag CondCode.z), (.gpr Reg64.rsi), (.gpr Reg64.rdi), (.flag CondCode.c),
  (.gpr Reg64.r9), (.gpr Reg64.r13), (.gpr Reg64.r15), (.slot 1 .w64), (.slot 0 .w64),
  (.slot 4 .w64), (.slot 3 .w64), (.slot 8 .w64), (.slot 2 .w64), (.slot 5 .w64),
  (.slot 6 .w64), (.slot 7 .w64), (.slot 9 .w64), (.flag CondCode.g), (.flag CondCode.ge)]

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

@[expose] def hint_full_lucky_ord_fid : x64Isa.Hints := _decH #[
  "b3201112131415062708090A0808090B070916076949491C2909071D392B0D190B0E0D2C0C0F0E0A090D5A",
  "090D0F0F07090G0G070907AB09071D3B0D0606074E0E0D29091E0E0D29091E0E0D29091E0E0D290B09071D",
  "4E0E0D290B0D073C0C0D294C0C0D294C0C0D294C0C0D291B09071D3C0C0D2C1B0D2D0607AB09071D3B0D06",
  "4B0B0D3A0D291C0D161A0D29175A0D2C091B0D0607390929092909290309071D39030DXD0019001006G581",
  "A2E460C31860100260A2020004781C3U8G5E460A21C701007G581U8A2E460C31C701007G581U8A2E460C31",
  "C701007G581U8A2E460C31B701054U860C3A2040000981C3U8Y6HG5E460Y5IA22B990201981C3U8Y6HG5E4",
  "60Y5IA22B990201AY8B81Y6HG5E460C3U8Y5IA219A0105DC381YBCU8YUGY6HG5E460Y5IYQFA2YPF0D0000D",
  "YPF81C3YBCU8YUGY6HG5E460Y5IYQFA21BD0100DYPF81C3YBCU8YUGY6HG5E460Y5IYQFA21BD0100DYPF81C",
  "3YBCU8YUGY6HG5E460Y5IYQFA21BD0105AC381A2YUGY6HG5E460U8Y5I0A0000CC381YBCU8YUGY6HG5E460Y",
  "5IYQFA21BC0100CC381YBCU8YUGY6HG5E460Y5IYQFA21BC0100CC381YBCU8YUGY6HG5E460Y5IYQFA21BC01",
  "03DC381YBCU8YUGY6HG5E460Y5IYQFA2ZPB0D0001DC381YBCU8YUGY6HG5E460Y5IYQFA2ZPB0D0001DC381Y",
  "BCU8YUGY6HG5E460Y5IYQFA2ZPB0D0001DC381YBCU8YUGY6HG5E460Y5IYQFA2ZPB0D0003DC381YBCU8YUGY",
  "6HG5E460Y5IYQFA2b0B0D0002AC381A2YUGY6HG5E460U8Y5I1BA0100AC381A2YUGY6HG5E460U8Y5I1BA010",
  "0AC381A2YUGY6HG5E460U8Y5I1BA0102BC381A2YUGY6HG5E460U8Y5IbDB19B0101BC381A2YUGY6HG5E460U",
  "8Y5IbDB19B0101BC381A2YUGY6HG5E460U8Y5IbDB19B0101BC381A2YUGY6HG5E460U8Y5IbDB19B0103BC38",
  "1A2YUGY6HG5E460U8Y5IcQB1CB01034A2C360U80400004U860C3A21B401004U860C3A21B401004U860C3A2",
  "1B401053A260C319301004A2C360U82C9402015A2C360U8e0C19501043A260C329B302013A260C31930103",
  "4A260C3eTB1940103260A21320100260A21320100260A21320101YQ43103010iWWuuuuWWZWkWiXWWiWyZWW",
  "uWYrgsWWWZWuWWudZWyiZnmiWWcXuWWuacXXmeiZmWWcWWrgrmWWWWdmWWWWxWWjdpv+WWWWZXgL0eWnWWWWWa",
  "eWfWeXaemWoXWWeXYWWWWXYaWeXYWYWWeWXWWaWYeWmXYWYWWmWaWXWWWYWemWWWWeWWemWWWWeWaeWWWWWXWW",
  "eeeW00aWemWWWWoaWamaWoaeWfWmYaWnWWWWanYWaWnWXWWaWWmWYWeaWeWnWXWWeWYWWmXYnWaeWWWXWmeaeX",
  "aWmaWYaWWWWWanWaaaW00aWeeeeeWWXWYWaWWWaWaXWWeWmWWYWWWXWeWmeZXWiaXmmaWWYWuWmeWYWWmWaWmW",
  "WYWaWWWmWaWWWmWeWWfWYaXWmgWWeWWWW00Zp/kl///+hp/s/t+xtd/j+/xp+y////ozv/t+y/z//t/+//x/lp",
  "/l+y/z//l/x/+/yuy/td///z+lZplzp+/m/xp/////o+fppt/ViWnmWWWXqiWfWeXaeuWoXWaiXZWWWWjYcWeX",
  "ZWYWWeWXWWaWmiWmXZWYWWmWaWXWZdZWeuWWWYXmyimYiXWlWaiWWWWWjXsiieW00026234567"]
@[expose] def ext_full_lucky_ord_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_lucky_scan : x64Isa.Hints := _decH #[
  "Z7452913121B1GD6190923030D46082A090A09080908030C1D391C03031719070901260E0B020E0E0E0101",
  "560906091A2609092A99095A0A0B070A1A3A061A0A0B090A09090C1D33130C09091711070103260E0B0202",
  "020E08560106011A2601012A9C095A0A000DC001900100A44HJFK5LBMDH85JG6I9F10A0101B44HJFK5LBMD",
  "H85JG6I9FX200B0005C44XO8HJFK5LBMDH85JG6I9FX200C0003K44XO8HJFK5LBMDH85JG6I9FX20YINYJOY4",
  "3YKEYH2Y2CYGBYFP0K0002J44XO8HJFK5LBMDH85JG6I9FX20YINYJOY43YKEYH2Y2CYGB0J0001F44XO8HJFK",
  "5LBMDH85JG6I9FX20YINYJOY430F0004B44HJFK5LBMDH85JG6I9FX2019B0108B44HJFK5LBMDH85JG6I9FX2",
  "00B0003K44HJFK5LBMDH85JG6I9FX20aM3b7Ob8PaP9b9Eb6NaNCb5Bb4Q0K0002J44HJFK5LBMDH85JG6I9FX",
  "20aM3b7Ob8PaP9b9Eb6NaNCb5B0J0001F44HJFK5LBMDH85JG6I9FX20aM3b7Ob8PaP90F000R020281430938",
  "10205AN834133931B32A32290B22A152212922B8922C3122A4K23700235002360S22C7M2296322B5XR2293",
  "22214K2359023690239092379H22997229522295B2297322960jnpkocXnWW+mWiYeYkeWWWWWWmWWcuvtfZW",
  "umWleWZWoXdaWWidmiX//wr90YWWWWWWWWWWWWaXYWWWWWWWWWWWWWWWWaWWWWWWWWYWnWWWWWWWWWWXWmaWWW",
  "WWW00XWWWbWWWWWWmWYWnWWWmemWWmaWXfeXbYmWWWWWeWXWemWWaYaWWeWemeYWYWWWW00mWWWWWWWWYeWYWW",
  "WWWWWWWWWWWWWeWWWWWWWWXaWWmWWWWWWWWmbWWWWW00y///n/////+/xx+z//+/k//+lt/yilzru//////lzz",
  "/k///txt//d/k/lx/x////VZWWWkWWWWWXWaaXYWWXWnWWXmeWZpmYgdWWWWWWmYYWnWWWeaeWWuWnWmaWaWWW",
  "W000A6234567"]
@[expose] def ext_full_lucky_scan : List (SigEntry × Nat) :=
  [(("full_lucky_ord_fid", [i64], [i64]), 72),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_analyze_core_m6", [i64], [i64]), 1000),
   (("m6_hdr_dr_update", [i64], []), 72),
   (("full_backtrack", [i64, i64], []), 168)]

@[expose] def hint_full_lucky_polar_m7 : x64Isa.Hints := _decH #[
  "ZP290E1413151210120B3D0303090D6B0B090D16091D36090D0309091903070000481A1A07080307393909",
  "0D2R0S190B010901230D2G0B0G030103276D4609082A090B0B0B3F0F35050B070B07050D43160B0F0F0D0B",
  "2G011601030B2D18083B0B380803070307080D42160B01010D0B23011A01030B2D290909K00190010076M4",
  "JFP947EHNBK2GI70200A6M4JFP947EHNBKKOJ2D53GIFA0301DKOLGMI6M4JFP947EHNBKJ2D5NF0D0002DLGM",
  "I6M4JFP947EHNBKKOJ2D5NF19D0103DD5J2LGMINF947E6MKO4JFPBKHN19D0100ELGMI6M4JFP947EHNBKKOJ",
  "2D5NFXA90E0002C6M4JFP947EHNBKXM9KOJ2D5NF2GIC0205E6M4JFP947EHNBKXMHKOJ2D5NFMILG2B1E0200",
  "GLGMI6M4JFP947EHNBKXMHKOJ2D5NFXQ0XV83B13GXWW0300HLGMI6M4JFP947EHNBKXMHKOJ2D5NFXQ0XV8YA",
  "32B1HXWW020596M4C4JFP947EH0HNBK3329903002ZE3ZF2020001CZE3ZF26MZG94C4JFP947EH0HNBK0C000",
  "2A6M4C4JFP947EH0HNBKZG9232A0202DZF26MZG9947EH0HN4C4JF1FPBKZO81FD0102DZF26MZG9947EH0HN4",
  "C4JFPBKZO8aE523BD0202DZF26MZG9947EH0HN4C4JFPBKZO8aE523BD0205Cb8F4C4JFP6M94BKZG97EH0HNb",
  "P822BC0202Cb8F4C4JFP6M94BKZG97EH0HNbP822BC020B02348C2353023791A36133B32A1C030C741A130A",
  "XB231AXP22A02230B54284235C2213G22C71XR51pWWsWWWyyWWpWWsWWWyyWudmWmWWWXWudWWYbyWWWdWYX/",
  "WWWgr90YWWWWWWemWWYWWWWWWemWWWWWWqWWXWWeYWYYemWeWWmeWWWWXeWW00XWWYXWYaeWWXWWYXWYaeWWXW",
  "eWYXWWmWbXWXXaeWaWWeaamWeWaWW00YWYWigWWWWWYWYWigWWWmWWWWWWWWZmuWWvWWmXWWavWWWWW00//zzt",
  "uz/xpl//zztuz/xpl//z/l/xz/+l/nz/yztl/p+lltsX/d/t//VYYedYWaimWWYYedYWaimWWYWmWaYWXmWkYW",
  "ZYemWiXmmef+WuWeWW00086234567"]
@[expose] def ext_full_lucky_polar_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_lucky_late_m7 : x64Isa.Hints := _decH #[
  "XT3626390D1A0A461A2A2A191F181312D656032A090A0903090903021D3B120303171B070B0C26010E050G",
  "01010C0C560B060B1A260B0B2A92035A0A001DB00190010114401000114401000414419101011441910102",
  "644X9JX7KX1MX3FX581060101744X9JX7KX1MX3FX58XO0070004744X9JX7KX1MX3FX58XO0070003G44X9JX",
  "7KX1MX3FX58XO0Y79Z1GZ2IYJ3Z31Z05YH2YVEYUH0G0002F44X9JX7KX1MX3FX58XO0Y79Z1GZ2IYJ3Z31Z05",
  "YH2YVE0F0001B44X9JX7KX1MX3FX58XO0Y79Z1GZ2IYJ30B000902028YF634933B32AK22929228312214L23",
  "1C0230CS2281M22100XWmWWWWxZczaiZYWXzWWiYeaymWXm+X//wrWWWWYemWkXJ0YWWWWWWWWWWWWeYaWWWWW",
  "WWWWWaYWWWWWWWWefWWaYWa00XWWWgWWWWWXWWaXYWWWmemWXWXYXWYWWWWWaaamWYnWY40XWWWWWWWWWamWYW",
  "WWWWWWWYWWWWWWWWWWWWWWW00ly///Z/////z/ttzx//+/k//y/zxz/x////ltts//uz/xNZWWWyWWWWWYWeeY",
  "aWWXWnWWZWYaYWaWWWWmeefWWdYWa80056234567"]
@[expose] def ext_full_lucky_late_m7 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_lucky_polar_m7", [i64], [i64]), 120),
   (("full_lucky_scan", [i64, .bool, .bool], [i64]), 1144)]

@[expose] def hints : List x64Isa.Hints := [hint_full_lucky_ord_fid, hint_full_lucky_scan,
    hint_full_lucky_polar_m7, hint_full_lucky_late_m7]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_analyze_core_m6", [i64], [i64]), 1000),
   (("m6_hdr_dr_update", [i64], []), 72),
   (("full_backtrack", [i64, i64], []), 168)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Lucky
