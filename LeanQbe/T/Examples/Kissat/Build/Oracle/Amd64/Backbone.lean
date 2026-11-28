module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Backbone

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rbx, Reg64.rbp, Reg64.rsi, Reg64.r15, Reg64.rdx, Reg64.r9, Reg64.rcx, Reg64.rax,
  Reg64.r12, Reg64.r13, Reg64.r14, Reg64.rdi, Reg64.r8]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rsi), (.gpr Reg64.rdx), (.gpr Reg64.rbx), (.gpr Reg64.r8), (.flag CondCode.nz),
  (.gpr Reg64.rbp), (.flag CondCode.z), (.gpr Reg64.rdi), (.gpr Reg64.r9), (.gpr Reg64.rcx),
  (.gpr Reg64.rax), (.flag CondCode.c), (.flag CondCode.nc), (.gpr Reg64.r14), (.gpr Reg64.r13),
  (.gpr Reg64.r12), (.flag CondCode.l), (.slot 6 .w64), (.slot 0 .w64), (.gpr Reg64.r15),
  (.slot 4 .w64), (.slot 5 .w64), (.slot 3 .w64), (.slot 7 .w64), (.slot 2 .w64),
  (.slot 1 .w64), (.flag CondCode.g), (.slot 10 .w64), (.slot 8 .w64), (.slot 12 .w64),
  (.slot 11 .w64), (.slot 9 .w64)]

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

@[expose] def hint_full_backbone_sched_m6 : x64Isa.Hints := _decH #[
  "X120111213047405261407280944072505092A0B240464072616280A3627070A190B804C381A2602A74020",
  "04C381A260397A403015C381A260GA297502026C381A260GAM52976020301A001014C381A2602A9402015C",
  "381A260XL91A501026C381A260XL9XR71A601000Xnmunm+WWWicZXZXyYL0eWaWYaYWXYWWWWWeaWW00aWYWX",
  "YXWanWWeWYaYWe00mWeWWYWWWaWXWWWaW00Zp/x/zxz/sy//l/xtx/lViWaWYaYWfZWWmWaeaWm0000201"]
@[expose] def ext_full_backbone_sched_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_keep_m6 : x64Isa.Hints := _decH #[
  "Y73A110457030344081407140700290B260604040C33080827141300070733080827141300070733080827",
  "141300070733080827141300070709070C1B370303201417080000090BC0000000037A91522083020037A9",
  "15230893030147A9152D92084020537A9152193010037A9152193010037A9152193010247A9152XB904000",
  "147A9152XB904000147A9152XB904000147A9152XB904000347A9152ZG9040001020021Q51escWWWnikWni",
  "kWnikWniiWWWWoZuu50aWYWWemWaWWWaWWWaWWWaWWYWYWWeWW00YWXWWaeWYWWWYWWWYWWWYWWfgnWWaWWG0Z",
  "YWaWWccWWccWWccWWcaWWWYWWie00lv/z//td/x///x///x///x//bWyvtt/+VcWYWWeuWaWWWaWWWaWWWaWWw",
  "/ZceeWX000010"]
@[expose] def ext_full_backbone_keep_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_unwind_m6 : x64Isa.Hints := _decH #[
  "I48191A0B132A0A1A0A1A0B232A0A1A0A1A0B2000000015614750A9881A501000XXYiYYaueL0mWWWWWWa00",
  "eWWWmWWY00naWXYeW00/l//+///xVmWWXWWWa00000"]
@[expose] def ext_full_backbone_unwind_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_prop_m6 : x64Isa.Hints := _decH #[
  "XN4D0D131A191118151E227B2A000A093F0F3202020A0A0B39160A09090B2G06100B00001000304B0A0B1A",
  "0A0A0A090E0E1A0A0A0A090E0E6001A00100AJHHI476JFKQLDMB39DL52E0A0201347VEXDF1A30100DX60JH",
  "HI476JFKQLDMB39DL5VEXDF1AD0100HX6NJHH1HI47VEXDFXJ26JX8OXLPFKQLDMB39DL51AH0102IXTAX6NJH",
  "H1HI47VEXDFXJ26JX8OXLPFKQLDMB39DL50I000902034NA3503653043463377227062246A6317326372X34",
  "2552431424125432240422420xbnWaZWYuWkkZXljgr90aYWWWWXXWeWWWWWWaWWWW00YXWWWWWmqaaWmWWWYW",
  "WWW00XZYcWWWXWemWWWWeXcaXWWWWW00ll+/vz////++dtt+////x////VmXWcYWWWWXXueeXWWWWaWWWW0008",
  "60189A3"]
@[expose] def ext_full_backbone_prop_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_analyze_m6 : x64Isa.Hints := _decH #[
  "X65A171819130505360F0F36063A0B102A0A0A2621061601010A0A240B1B2B3A0A0A131B01010150011001",
  "036H342F9D8J5PF11601007H342F9J5PFB7D81A701007H342F9J5PFB7D81A701074XU142F9D81340101020",
  "0B0YeueWWXmaiiiXgZmygL0eWWWeXWWWWWWWWWWWW00aWWmaWoWfWmWaWqXWW00aeWWWWeWaWaWWWmaW00d/p/",
  "+/t+x/j+//t+tz//ViWXWeXaWoXWWeXeYWW00003018"]
@[expose] def ext_full_backbone_analyze_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_round_m6 : x64Isa.Hints := _decH #[
  "Z6481A0A1D19171315151F64440F0A0B2E0J0E2Q0G09090B0A0A1A0A293A29171A03090B1727071707190B",
  "06090B27172G060F1B07170723391B210B0B210A0A34211B0A0A4409091B4B610A090B1A01090B10290919",
  "09190B144901092Q2A00004409092B1909E08888P42505IN5LMDD4K19380400F505IL7LMN5FH42888P6RJS",
  "HNDDPTBU3K19F0307KX1KXCJ505ILMN5FH42888P6RJSHNDDX21XBEPTBUY6VXIL0KXWW0000NX1KXCJ505ILM",
  "N5FH42888P6RJSHNDDX21XBEPTBUY6VXILX6FY83Y7A19NXWW0103KX21XCJ888P42505IN5LMFH6RJSHNDDPT",
  "BUYO9XIAXILY6V1KK0102HYTKX21XCJ505ILMN5FH42888P6RJSHNDDPTBU0H0006GX1KXCJ505ILMN5FH4288",
  "8P6RJSHNDDPTBU11G01038aK342888PaHKLMN5DD1780100A888P42505IN5aK3aHKLMDD2A9A02027b0742aH",
  "KaK3LMN5DD070000Bb07aK342888Pb21b1AaHKLMN5DD19B0102342aHKaK31A301018L8LMN5DD42aHKaK3b0",
  "721A802019bO1L8LMN5DD42aHKaK3b071A9010U0430200B12315D23319C3C838C37B3663B73A4041703470",
  "4190349L2356D22C612267222782232452251123974622025124206220251242H2275342BB2C44228C1234",
  "BE22B972276122C7222B8223241624225122006242220251D22201424225104242251A22660mWnyZccWmaf",
  "mWWZuWe+WZZmiWZWWcpYXWicWWafmWYmjcaWWuuWm/rgr50eWWWWWWYWWWWaWWYWWYWeWWnWYaWWWaaWWmYWWW",
  "WWWWWWWWWYYWWWWW00aWWWeWaXWWWeYWWnWWXWaWWemXWWWWYYmWfXWWWeWWWWWYbWXXXWWWW00cXXYWWYamWW",
  "XeWWZWXWuaWXWWYWnWWYYWWYamWWWaXYWWaeWWWWWW00Z/tx//l/tz///lv/+zz/z/t//k/z////xw//jz///l",
  "/////vn/zzz////VeaWWmWeYWWWmcWXYYWYWeWWnWYWWWWabWWoYWWWmWWWWWckWYYYWWWW000D60189A3"]
@[expose] def ext_full_backbone_round_m6 : List (SigEntry × Nat) :=
  [(("full_backbone_prop_m6", [i64, i64, .bool], [.bool]), 120),
   (("full_backbone_analyze_m6", [i64, i32, i32, i64], [i32]), 24)]

@[expose] def hint_full_backbone_m6 : x64Isa.Hints := _decH #[
  "X8443A26060616064E2417190909070A0A07241A090944341416141F1A0F04003C30350B161606190B9001",
  "J00100242550200065MD42COPELM17501016MD42COPELMX290600012CO422DJ202005CO42PELMXDK30JI50",
  "3058CO42XTDPELMXDKXLIY0A1J801018CO42XTDPELMXDKXLIY0P1J80100AXKJCO42XTDPELMXDKXLIY0PY1F",
  "15A010J0401200BJ232752337020A7X4634617030732272522725227252272220A772317X0227222272222",
  "7262306122722227212272122720uiZWXWaYXWXyXcWXcqWWcy30YWWWWeYWWemWmeaYWWWWWWWWWWWW80XWWY",
  "oaWWeWeWeaYXYWWeWWeWgbeW40aWWWWWWWWWWWWmWWWWWWW00d//y//uxp//l/l/ltxzx//l//l/Zrl/NZWWda",
  "iWWmWmWmeaYaWWmWWmWygmW800560189A3"]
@[expose] def ext_full_backbone_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_prioritize_binaries_m6", [i64], [.bool]), 56),
   (("full_backbone_sched_m6", [i64], [i64]), 24),
   (("full_backbone_keep_m6", [i64, i64], []), 8),
   (("full_backbone_round_m6", [i64, i64, .bool], [i64]), 280),
   (("full_add_unit", [i64, i32], [.bool]), 232)]

@[expose] def hints : List x64Isa.Hints := [hint_full_backbone_sched_m6,
    hint_full_backbone_keep_m6, hint_full_backbone_unwind_m6, hint_full_backbone_prop_m6,
    hint_full_backbone_analyze_m6, hint_full_backbone_round_m6, hint_full_backbone_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_prioritize_binaries_m6", [i64], [.bool]), 56),
   (("full_add_unit", [i64, i32], [.bool]), 232)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Backbone
