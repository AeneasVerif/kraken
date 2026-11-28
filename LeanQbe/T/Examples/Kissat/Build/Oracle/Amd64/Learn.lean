module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Learn

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r13, Reg64.rdi, Reg64.rcx, Reg64.r14, Reg64.rax, Reg64.rdx, Reg64.r8, Reg64.rsi,
  Reg64.r9, Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.r15]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rax), (.flag CondCode.z), (.flag CondCode.nc), (.gpr Reg64.rcx),
  (.flag CondCode.c), (.gpr Reg64.rbp), (.gpr Reg64.rbx), (.gpr Reg64.rdx), (.gpr Reg64.r12),
  (.flag CondCode.nz), (.gpr Reg64.rsi), (.gpr Reg64.r9), (.gpr Reg64.r15), (.gpr Reg64.r14),
  (.gpr Reg64.r8), (.gpr Reg64.rdi), (.gpr Reg64.r13), (.slot 3 .w64), (.slot 10 .w64),
  (.slot 11 .w64), (.slot 9 .w64), (.slot 1 .w64), (.slot 2 .w64), (.slot 0 .w64),
  (.slot 4 .w64), (.slot 7 .w64), (.slot 5 .w64), (.slot 8 .w64), (.slot 6 .w64),
  (.flag CondCode.g)]

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

@[expose] def hint_full_det_new_level : x64Isa.Hints := _decH #[
  "73001000203240010010001000u1000X4000XyyNZZ80000"]
@[expose] def ext_full_det_new_level : List (SigEntry × Nat) := []

@[expose] def hint_full_one_lit_confl : x64Isa.Hints := _decH #[
  "cJ25102123060724380606095A3B0A0A2A0A0104040B0C040D010D00010D010D4E044124733C0E0E2E0D04",
  "3B3B0B0B2B040E070004190E3A020F0F370F000F04190F000F0417000F0F020F0B09140B07040B0B070427",
  "0B2B0B37070B090B02570F0702314107070207010F02570B34021A010A0200240A1A0000123702170F291C",
  "0615181D1E0F0F591709072129070721A300682D0000260000250206050A012401040C0806100100020324",
  "0A1303091008082019070903160000223702170A291B051F181D1E0A0A591709072129070721A300U00100",
  "010254GP6N865EH4FIJK54400565P64GN8EH5FD07E58501665P64GN8EHVE4FD076840484GP6N865EHY0IY1",
  "JY2K08400154GEHY2KY0IY1J05000084GP6N865EHY0IY1JY2K1F84100D4GYODN865P6Y0IY1JYICEHYE3YEL",
  "YDFY2K17Da4100D4GP6YDFYICYE3YELN865EHYODY0IY1JY2K3E70DY83029YOD4GP6N865EHY0IY1JY2K0980",
  "02H4GYODP6N865Y2KY0IY1JYICEHZEEZEMZIAZINYE3YELZP70HYie8001H4GYODP6N865Y2KY0IY1JYICEHZE",
  "EZEMZIAZINYE3YELZP70HYie8002HYOD4GP6N865Y2KY0IY1JYICEFEHZEEZEMZIAZINYE3YEL0Hue800014G0",
  "10001HYOD4GP6N865Y2KY0IY1JYICEHZEEZEMZIAZINYE3YELa5O0Hie8002KYOD4GP6N865Y2KY0IY1JYICEH",
  "ZEEZEMZIAZINYE3YELa60a5OaBPaAF0Kie8000LYOD4GP6N865Y2KY0IY1JYICEHZEEZEMZIAZINYE3YELa60a",
  "57a5OaBPaAF0Lie8006PYOD4GP6N865Y2KY0IY1JYICEHZEEZEMZIAZINYE3YELb3BaOQa60b1RaP7aPSa5OaB",
  "PaAF0Pmie800944GEHY2KY0I1A401020000003C4GY2BY2KdD8dFDcP0dHEdB5EHcNAd96d8C0C0002A4GY2Kd",
  "D8dFDcP0dHEdB5EHcNAd960A000154GY2KdD8dFDcP005000274GfB5fA6eUDeR8f36f8507Z000244GfJCfL6",
  "fK81A4010234GfJCfL613301010000003B4GfJCh88hADgJ0hCEh6FgG3gH6h45h3B0B0002A4GfJCh88hADgJ",
  "0hCEh6FgG3gH6h450A000154GfJCh88hADgJ005000X002001P2332X163A33B4395I2312X3232632307K234",
  "508262270221254M626227022114378345F626227022162368423550238532257542542863225312285E22",
  "56922140221312285A225754254216322531221596262270221L223AA223A02289Y22223J22890XsckzaiZ",
  "ZWalegqpakiWhYWWuXWWiWuuxWXsckzaiZZWalegqpakeWiWmXWeWWzmWWWdnuWWkuWkimWWWWWWeWYWkWdWWZ",
  "ZmZZp+XmWWWWXnuWyuvL0XWWWWWWWWWWWWWWeXXWWWWWWWWWWWWmWXWWWaeaWmaYWWWYWWWXWWYaWWWWemWWWa",
  "eWWWWWWWaWmWWWWWWWWWW00XWWaWmmWWWaXWmWWWeWXaWmnWWWWWWWWWWXWWaWmmWWWaXWmWWoaeWWWWWYaYWe",
  "YXWWWXaWWWaXXWnWXWaeWWmYaWWWmWWWYaeWWXeWWeXWY00YWWWWWWWWWXaWWWmWWWXmWWWWWWWWiiWWWYWWWW",
  "WWWWWXaWWWmWWWWWWWWWWWinWWWXmemWcencaWWWWWWmWmWadWZmWXnuXnuWWWWWWWWuyYiWW00//////z/tt+",
  "+////tz+/w//lyytW+zZ/////////z/tt++////tz+/+khtl/////vtx/lxy///yp///tzz+z/y/td/+dhol/+",
  "////xtchWXl//ly/xVYWeeXXWWWWeYXWbWWmZZe/XYyWWWWWWWWWYWeeXXWWWWeYXWXnqemWWWWWceaWmaZWWW",
  "ZiWWWeYYXYWZWeuWXuqjmWXWWWWaevq/+mWWmZWa000C69AB03C"]
@[expose] def ext_full_one_lit_confl : List (SigEntry × Nat) :=
  [(("full_backtrack_ac_fid", [i64, i64], []), 184),
   (("full_wstack_defrag_m6", [i64], []), 136),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_unwatch_large", [i64, i32, i32], []), 24)]

@[expose] def hint_full_eager_subsume : x64Isa.Hints := _decH #[
  "ZI301716131C1F1E1B09023A0A4A0A4A0A4A0A1E0A02143F0F1E049D090D0E1208080A35111905040E0209",
  "3A3A0A290F0406012E0411091E3E0E0A0A042T0E0E392106040F0F0F050F090F3E0419023E0E4E0E4E0E4E",
  "0E1F0E02143E0E1F044F09271004140002A007021430040420372F0900R00000000BLB4GB6BQD37097JHHL",
  "FC5S0B0000BLB70974GB6BQD3JHHLFC5S1EB0100BLB70974GB6BQD3JHHLFC5S1EB0100BLB70974GB6BQD3J",
  "HHLFC5S1EB01055LB7097D35S1650100ALB4GBQD37097JHHLFC5S2EFA0200BLB4GBQD3JHHLFC70975SY2A1",
  "FB0106HY3MLB4GBQD37097Y2NJHY6DHLFCYD8YN5YEOYI55S16HXmm0100HY3MLB4GBQD37097Y2NJHY6DHLFC",
  "YD8YN5YEOYI55S36FEHXmm0301IY3MLB4GBQD37097Y2NJHY6DHLFCYD8YN5YEOYI55SYUE26FIXmm0205ELB4",
  "GBQD3JHHLFC70975SY2NYN5YD8YEO0EeW0000HY3MLB4GBQD3JHHLFC70975SY2NY6DYD8YN5YEOYI516HZaW0",
  "101IY3MLB4GBQD3JHHLFC70975SY2NY6DYD8YN5YEOYI5ZJ60IZaW0005BLB4GBQD3JHHLFC70975SY2N0B000",
  "23D35SaN60300006aN6LB7097D35S1F601006aN6LB7097D35S1F601006aN6LB7097D35S1F601052D35S020",
  "0012D35S17201002D35S270202003D35Sc0017301022D35S10201002D35S10201002D35S10201062D35S10",
  "2010B0200152359A6336311367Y22306223212229572347Y6227142213L2270aF22760XscWZWWgrguWWZXm",
  "WpWWfwkpquWWiWWWWikXmZmWWWWiyWWXYyXWj+WpWWfwkpquWrgL0mWWnWaeWWWWYaWeYeWaeWWWWWWaeWYWXW",
  "XWaaWWaeWWWWXYaeWaYWWeWaeWWWWWWaWW00eWWemYaWWWWnYWaWaWYaWWWWWWoaWXWWmmmYYWWoaaamWanYaW",
  "YXWWaWYaWWWWWWoWW00oWWXWYWWWeeWXWmWfWYavcfoeWWWWYWWWXWXXuWWWWYkWeWWimWaWWfWYavcfoeWWW0",
  "0/X//klxp///+jv/t/p/xp/////+hp/z/+k+/xx/+xppo//sjxt/vz//p/xp/////+h//V+WWnmaiWWWXocWeW",
  "iWaiWWWWWXqiWYWXnXWaaWXaiijWWfoaeWcYWWiWaiWWWWWXqWW000769AB03C"]
@[expose] def ext_full_eager_subsume : List (SigEntry × Nat) := []

@[expose] def hint_full_learn_clause_m6 : x64Isa.Hints := _decH #[
  "aK361F1C0D1G010235050027120A23030B344E041000002G0G1002030G0100020324002003000024101300",
  "042910030000241109190D291A002D3104010131091919191A150119092410430100030309170000201907",
  "09031G000022370207291F0E16151C1F0B0B591709072129070721A30050010001240A1D29000022330203",
  "291A0F1E1615170B0B5913090321290303B30061M0010001016CD485NBC9F760610007769F48EGCD5NBC1E",
  "7G101A769FP748EGHEK5CD5NBC10Ac4100A769F48EGCD5NBCHEK5Q00AeG0036CD485NBCXOG761061102748",
  "BCY1LXOG76CD5N07X0000748BCY1LXOG76CD5N07X0002748BCY1LXOG76CD5N07X0006848Z6NBCZ9DY1LXOG",
  "76CD2A58a0200748ZBACDZ9DXOG76BC074002948Z6NBCZ9DY1LXOG76CDZC509a0001948Z6NBCZ9DY1LXOG7",
  "6CDZC5109a0108648ZBACDZ9DXOG76064002548ZBACDZ9DXOG1354105C48ZBACDbL5bNCb20bPFbJ6aV3b0G",
  "bHEbGN0C4002B48ZBACDbL5bNCb20bPFbJ6aV3b0GbHE0B4001648ZBACDbL5bNCb20064001348CDBC1A3210",
  "3148010003948CDe36e55dG0e77e1EdVFdUA092002848CDe36e55dG0e77e1EdVF08200B020B192307Y2231",
  "4XA2271D22400230402074M2271I2074Y92301U22801XU5l///////////VmucuxthWuuXZwYraukicWiXWWj",
  "nptfZWuuXZwYraukiWhYWWleuaXWmYeWWWgaWumXmmiWqueZWWpYWvnuuZZWaL0YWeeWWWWWWWWWWmeWYYWWYW",
  "WWWWoWWWWWaWXWWWWWWWWWWeWaWXWWWW00XWWWWWWWXWaaWWWXXWmeWXaWWWWWWWeWXWaaWWWXXWmWWWeaWXXf",
  "WXWaomgfWWXXbYWWmaXWWWamWWaWYWWmWYm00eWWWWWWWWfWWWWWWWWWWWWWmWWWWWWWWWfWWWWWWWXmWWXWWW",
  "WWWWWWWWWWWaWWaWWYWYWWWaXeWemgeXfWW00/z//////zz/tt///zz+/l+it///////lzz/tt///zz+/w//lt",
  "/yzj/z/su/hj//zznv/+/py//pop//p/x/+//w/VYWWWWWWYYWeeWWWYYXWmXpeWWWWWWWmYYWeeWWWYYXWbWW",
  "meWZYoWYWfdWqoWWYYkcWXWiZWWijiWWiWaWXWWbW000269AB03C"]
@[expose] def ext_full_learn_clause_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack_ac_fid", [i64, i64], []), 184),
   (("full_wstack_defrag_m6", [i64], []), 136),
   (("full_reduce_m6", [i64, .bool], [i64]), 856),
   (("full_add_clause", [i64, i32, i32, .bool], [i64]), 312),
   (("full_reduce_purge_c0", [i64], [i64]), 728),
   (("full_eager_subsume", [i64, i64], []), 104)]

@[expose] def hints : List x64Isa.Hints := [hint_full_det_new_level, hint_full_one_lit_confl,
    hint_full_eager_subsume, hint_full_learn_clause_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack_ac_fid", [i64, i64], []), 184),
   (("full_wstack_defrag_m6", [i64], []), 136),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_unwatch_large", [i64, i32, i32], []), 24),
   (("full_reduce_m6", [i64, .bool], [i64]), 856),
   (("full_add_clause", [i64, i32, i32, .bool], [i64]), 312),
   (("full_reduce_purge_c0", [i64], [i64]), 728)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Learn
