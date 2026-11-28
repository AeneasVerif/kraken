module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Backtrack

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rdx, Reg64.r9, Reg64.rcx, Reg64.rbx, Reg64.rsi, Reg64.rax, Reg64.r12, Reg64.rbp,
  Reg64.r8, Reg64.r13, Reg64.r14, Reg64.r15, Reg64.rdi]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rax), (.flag CondCode.nc), (.gpr Reg64.r8), (.gpr Reg64.rsi), (.flag CondCode.nz),
  (.gpr Reg64.r9), (.gpr Reg64.rdx), (.flag CondCode.z), (.gpr Reg64.rcx), (.gpr Reg64.rdi),
  (.slot 2 .w64), (.slot 3 .w64), (.slot 1 .w64), (.slot 5 .w64), (.slot 0 .w64),
  (.slot 4 .w64), (.gpr Reg64.rbx), (.flag CondCode.c), (.gpr Reg64.rbp), (.gpr Reg64.r13),
  (.gpr Reg64.r12), (.gpr Reg64.r15), (.gpr Reg64.r14), (.slot 9 .w64), (.slot 10 .w64),
  (.slot 7 .w64), (.slot 6 .w64), (.slot 8 .w64)]

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

@[expose] def hint_full_assign_lvl : x64Isa.Hints := _decH #[
  "R40002132011203241516161616150606541204022724020227A800400000003B4953VAX1B90X35TC6D78R",
  "EPF0Bi2002A4953VAX1B90X35TC6D78RE0Ai200154953VAX1B9005200C52350I2300123101232012341123",
  "30S2204322003420522122221C2203322220ZiizweuccWe+mrgpakC0mYYWWWWWWW00YWWeXXWWWWaXWG0aWW",
  "WWWWWWWYeWWWmW00d/////x/llzz////tz+VaWmmYYWWWWeYX00060"]
@[expose] def ext_full_assign_lvl : List (SigEntry × Nat) := []

@[expose] def hint_full_assign : x64Isa.Hints := _decH #[
  "S5200002138011803241516161616150606541804082724080827A800400000003B4953X1AX3BB0X55VC6D",
  "92TERF0Ba2002A4953X1AX3BB0X55VC6D92TE0Aa200154953X1AX3BB005200C82350I23001231012320123",
  "4112330S2204322203420522122221C2203322220xZdkocXnmYdqbgqvZp30aWmmWWWWWWW00mWYWeeWWWXWe",
  "a00XWWWWWWWWWWoWWWaWW00X/////+/xx/ll///z/ltVXWaaWmmWWWYWme00060"]
@[expose] def ext_full_assign : List (SigEntry × Nat) := []

@[expose] def hint_full_save_target_best : x64Isa.Hints := _decH #[
  "XG34271816131510020G0G2H040132044204420442041002011H3204100H2H040136044604460446041006",
  "011H3604100HJ000000025G3C8I5NG490500016E6C8I5NG49G310601006E6C8I5NG49G310601006E6C8I5N",
  "G49G310601027E6C8I5NG49G3T00700017E6C8I5NG49G3T00700017E6C8I5NG49G3T00700017E6C8I5NG49",
  "G3T00700037E6C8I5NG49G3XQ007000200000013G3C8I510301003G3C8I510301003G3C8I510301024G3C8",
  "I5Y700400014G3C8I5Y700400014G3C8I5Y700400014G3C8I5Y700400034G3C8I5Z400400000XXmWYZoZoZ",
  "oZWWiWmuWXXvXvXvXmWcYrfJ0XWeYaWmWmWmWmWnWmaXYWeWeWeWeWemWWW00maXYWeWeWeWeYemeYWnWaWaWa",
  "WaXaeWWY40mXWXWXWXWXWWWWWeWmWmWmWmWmWWmWW00Z+ltzv/l/l/l/lvk/dx+y/t/t/t/tytl//xNXmeYcWm",
  "WmWmWmcnWuaXZWeWeWeWeZemWWa800013"]
@[expose] def ext_full_save_target_best : List (SigEntry × Nat) := []

@[expose] def hint_full_backtrack_raw_m5 : x64Isa.Hints := _decH #[
  "ZP4124271816121310050G0G2H040135044504450445041005011H3504100H2H0401360446044604460410",
  "06011H3604100H1613101812151G101I3000180H089H480J0J0H200001300I000H081808743418081H0000",
  "0601050224080106080826010K0L051808110H3426041G0G0G260611310244163M1H3H2HR0000000134953",
  "5D0300026K2G8495DM3RG0600017I6G8M3495DRGK210701007I6G8M3495DRGK210701007I6G8M3495DRGK2",
  "10701028I6G8M3495DRGK2X100800018I6G8M3495DRGK2X100800018I6G8M3495DRGK2X100800018I6G8M3",
  "495DRGK2X100800038I6G8M3495DRGK2XU00800035K2G8495DM310501005K2G8495DM310501005K2G8495D",
  "M310501026K2G8495DM3YB00600016K2G8495DM3YB00600016K2G8495DM3YB00600016K2G8495DM3YB0060",
  "0036K2G8495DM3Z8006000235D49aA81I30100DZPNZNA5DZJ3ZJFa1EaAO49ZTPZLQZH6ZHBZRR2IMD0201EZ",
  "PNZNA5DZJ3ZJFa1EaAO49ZTPZLQZH6ZHBZRRaMM1IE0100HaLIZPNZNA5DZJ3ZJFa1EaAO49aMMaQJZRRZTPZL",
  "QZH6ZHBaP80HYWW0003HaLIZPNZNA5DZJ3ZJFa1EaAO49ZTPZLQZH6ZHBaMMb70aQJZRR0H000AHaLIZPNZNA5",
  "DZJFa1EaAO49ZTPZLQZHBZRRaMMcHLb70aQJcGK18H0100JaLIZPNZNA5DZJFa1EaAO49ZTPZLQZHBZRRaMMcH",
  "Lb70aQJcGKcI5cVC18J010535D49dTI03000Q32354bH233012344A23655226522322CA3A23073733813984",
  "2252E225222229H222632287A222862228XE2310F2241J4244203042442030424420304244203042442030",
  "42442030424420304244203I2245222450XmiYWWuWxZoiWiyamXmWuWWofnwwaWbmiXm/+azgrgmWmuWXXvXv",
  "XvXmWcWeiWWmymymymuWZXgqvJ0XWeWWWaWWWWWWWWWWWWWWYWWaWWWmWaXWWWWWWWWWWmaXYWeWeWeWeWemeY",
  "WnWaWaWaWaWaeWWWW00YWmaWWWYWaaWXXXeWmWfWmXWmYWWWeWYWmXWWWWWWWWeYWnWaWaWaWaXaeaXWemYWYW",
  "YWYWoaWWXY40iWfmmcmaaWWWuWWWWWWWWXYWWnWWmWWWiWWWWWWeWmWmWmWmWmWWWWaWeWeWeWeWeWWeWWW00/",
  "x+/p///x/tt/zzyl+//j+/z+/x///l/x+/z/+//////dx+y/t/t/t/tytlpz/klx/x/x/x+ht//zxNaXWiWWWa",
  "WeeWYYZmXWWoXWYXWaWWWmWaXWYWXWWWWWWuaXZWeWeWeWeZemiYWnmaWaWaWaXqeWWYa800B63769AB"]
@[expose] def ext_full_backtrack_raw_m5 : List (SigEntry × Nat) := []

@[expose] def hint_full_backtrack : x64Isa.Hints := _decH #[
  "XI4124271816121310050G0G2H040135044504450445041005011H3504100H2H0401360446044604460410",
  "06011H3604100H1GJ00000001249530200026K2G8495CM3RG0600017I6G8M3495CRGK210701007I6G8M349",
  "5CRGK210701007I6G8M3495CRGK210701028I6G8M3495CRGK2X100800018I6G8M3495CRGK2X100800018I6",
  "G8M3495CRGK2X100800018I6G8M3495CRGK2X100800038I6G8M3495CRGK2XU00800035K2G8495CM3105010",
  "05K2G8495CM310501005K2G8495CM310501026K2G8495CM3YB00600016K2G8495CM3YB00600016K2G8495C",
  "M3YB00600016K2G8495CM3YB00600036K2G8495CM3Z8006000332314bI230C022C00mWmuWXXvXvXvXmWcWe",
  "iWWmymymymuWZXgqvJ0maXYWeWeWeWeWemeYWnWaWaWaWaWaeWWWW00eYWnWaWaWaWaXaeaXWemYWYWYWYWoaW",
  "WXY40eWmWmWmWmWmWWWWaWeWeWeWeWeWWeWWW00Z//dx+y/t/t/t/tytlpz/klx/x/x/x+ht//zxNuaXZWeWeW",
  "eWeZemiYWnmaWaWaWaXqeWWYa800213"]
@[expose] def ext_full_backtrack : List (SigEntry × Nat) :=
  [(("full_backtrack_raw_m5", [i64, i64], []), 136)]

@[expose] def hint_full_backtrack_ac_fid : x64Isa.Hints := _decH #[
  "Z539012724092H18161213100509092H040135044504450445041005011H3504100H2H0401360446044604",
  "46041006011H3604100H1718161213100500002H040135044504450445041005011H3504100H2H04013604",
  "4604460446041006011H3604100H0H10X50000000124G5I0200036O2K84G5IQ3V90600017M6K8Q34G5IV9O",
  "210701007M6K8Q34G5IV9O210701007M6K8Q34G5IV9O210701028M6K8Q34G5IV9O2X500800018M6K8Q34G5",
  "IV9O2X500800018M6K8Q34G5IV9O2X500800018M6K8Q34G5IV9O2X500800038M6K8Q34G5IV9O2Y20080003",
  "5O2K84G5IQ310501005O2K84G5IQ310501005O2K84G5IQ310501026O2K84G5IQ3YF00600016O2K84G5IQ3Y",
  "F00600016O2K84G5IQ3YF00600016O2K84G5IQ3YF00600036O2K84G5IQ3ZC006000234G5IF90300017ZR2Z",
  "N84G5IF9ZT3a200700018ZP6ZN8ZT34G5IF9a2CZR210801008ZP6ZN8ZT34G5IF9a2CZR210801008ZP6ZN8Z",
  "T34G5IF9a2CZR210801029ZP6ZN8ZT34G5IF9a2CZR2a800900019ZP6ZN8ZT34G5IF9a2CZR2a800900019ZP",
  "6ZN8ZT34G5IF9a2CZR2a800900019ZP6ZN8ZT34G5IF9a2CZR2a800900039ZP6ZN8ZT34G5IF9a2CZR2b5009",
  "00036ZR2ZN84G5IF9ZT310601006ZR2ZN84G5IF9ZT310601006ZR2ZN84G5IF9ZT310601027ZR2ZN84G5IF9",
  "ZT3bI00700017ZR2ZN84G5IF9ZT3bI00700017ZR2ZN84G5IF9ZT3bI00700017ZR2ZN84G5IF9ZT3bI007000",
  "37ZR2ZN84G5IF9ZT3cF007000A0407403CbO230CK2315022C0322C0222C0022C0aB22C0A2305022500eWWa",
  "cWWekekekeiWXmYZWWadadadacWWugraWYZWWadadadacWWuXXmWYZoZoZoZWWibgpXnH0aaXWemYWYWYWYWWW",
  "YWmaeXWXWXWXWWWWWWWYWmaeXWXWXWXWXYXWeYaWmWmWmWmWnWWWWaa00YYWmaeXWXWXWXWfYXWeYaWmWmWmWm",
  "anWWWeXWeYaWmWmWmWmanWmaXYWeWeWeWeYemWWaYY40YWaWaWaWaWaWWWWXWYWYWYWYWYWWYWWWWWXWYWYWYW",
  "YWYWWWWWmXWXWXWXWXWWXWWWWW00X//xv+/tdz/z/z/z/bxy/lxp+/+/+/+/oz///ly/lxp+/+/+/+/oz+ltzv",
  "/l/l/l/lvk///pxxNacXWeuYWYWYWYWwaZWmaiXWXWXWXWjYWWWmZWmaiXWXWXWXWjYXmeYcWmWmWmWmcnWWWi",
  "aa8002237"]
@[expose] def ext_full_backtrack_ac_fid : List (SigEntry × Nat) :=
  [(("full_backtrack_raw_m5", [i64, i64], []), 136)]

@[expose] def hints : List x64Isa.Hints := [hint_full_assign_lvl, hint_full_assign,
    hint_full_save_target_best, hint_full_backtrack_raw_m5, hint_full_backtrack,
    hint_full_backtrack_ac_fid]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Backtrack
