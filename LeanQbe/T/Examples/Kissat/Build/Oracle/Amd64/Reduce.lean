module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Reduce

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r12, Reg64.rcx, Reg64.rbx, Reg64.rbp, Reg64.r13, Reg64.rsi, Reg64.r8, Reg64.r14,
  Reg64.rdi, Reg64.rax, Reg64.r15]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rsi), (.gpr Reg64.rax), (.gpr Reg64.rdx), (.gpr Reg64.rcx), (.flag CondCode.nz),
  (.flag CondCode.c), (.gpr Reg64.r8), (.flag CondCode.nc), (.gpr Reg64.rbp), (.gpr Reg64.r9),
  (.gpr Reg64.rdi), (.gpr Reg64.r12), (.gpr Reg64.rbx), (.gpr Reg64.r13), (.gpr Reg64.r14),
  (.flag CondCode.z), (.slot 0 .w64), (.gpr Reg64.r15), (.slot 4 .w64), (.slot 2 .w64),
  (.slot 3 .w64), (.slot 1 .w64)]

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

@[expose] def hint_full_red_less : x64Isa.Hints := _decH #[
  "E302101022303040000320221050510015001000Xpmc6000XW00yyZ30d/ycVZuWZv00000"]
@[expose] def ext_full_red_less : List (SigEntry × Nat) := []

@[expose] def hint_full_red_sift : x64Isa.Hints := _decH #[
  "XA410607320521280129090823030401013808230502050231260129090623030403033909290505110607",
  "40000000034A507B316C3030144A507BDC12401027XF24A507BXI1XL6DC157XG101020010XpmccjmZdWiix",
  "W00YWWWWWWWWWWWWWe00aWWWXWWWWWWYWWWa40yyZZamXvuccfW00Zpyd/yc//vl/uj//pJiZuWZvWWcmWdoWW",
  "iC0003230"]
@[expose] def ext_full_red_sift : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_reds : x64Isa.Hints := _decH #[
  "fD251B13050601270804180200073105222C0226060C29090402023C0C2605010501322002260600290904",
  "06063909290505120007040D041122053105222C0226060C29090402023C0C260501050132200226060029",
  "0904060639092905051200070D0412010E0E0601010730002C0C302C0C0C00000C100C2000280830280808",
  "0000081C0C20002808302808080000081C0C20002808302808080000081C0900071530002C0C302C0C0C00",
  "000C100905D309071533055303230303450905080005244900030507390928080820790928080820790928",
  "0808207909280808204309071530002808082943052C051F06074303234303234303234303230103071543",
  "032301050743434343010307154301053808210101010132020209041022022A0A0A0A0A3606060A07243C",
  "05X80000000338BA35D03000035DA38B18301014K85DA38B0400004K85DA38B320A403015K85DA38BQA115",
  "01028K85DXS1A38BXV2Y20QA158Z010428BA31D2010138BA3Z1D0300003A38BZ1D320A3030148BZ1DA3Z9A",
  "114010278BZ1DaB1A3aE2aH0Z9A157XG1046bJEbKGbM15DbG28B0600007bJEbKG5DbG2A38BbM119701007b",
  "JEbKG5DbG2A38BbM119701007bJEbKG5DbG2A38BbM1197010445D8BbKGbJE1A401006bM15DbG2bKGbJE8B3",
  "A6C603009fIAfJ65DbM1fKCbG2bKGbJE8B0900009bM1fIAfJ65DfKCbG2bKGbJE8B13901009bM1fIAfJ65Df",
  "KCbG2bKGbJE8B13901009bM1fIAfJ65DfKCbG2bKGbJE8B139010395DbM1fJ6fIAbKGbJEfKCbG28B2989020",
  "09fIAfJ65DbM1fKCbG2bKGbJE8B3098903017bM15DbG28BbKGbJEfKC2A6702019fJ6fIA5DbKGbJEfKCbM1b",
  "G28B09000095DbM1fJ6fIAbKGbJEfKCbG28B230902019fJ6fIA5DbKGbJEfKCbM1bG28B13901009fJ6fIA5D",
  "bKGbJEfKCbM1bG28B13901009fJ6fIA5DbKGbJEfKCbM1bG28B139010535D8BkD603000045DkD68BkBA1140",
  "10045DkD68BkBA114010045DkD68BkBA114010435D8BkD6113010035D8BkD6113010035D8BkD611301043A",
  "38B5D1C301005A38B5Dn4Cn78115G1006A38B5Dn4Cn78nM9116G10302045cQ2306gD22600ZWiXuciWdWvmX",
  "uWXy+ldWWiyWWvyvyvyvuWWXsuvmWcxZdjsckxiizsuvmWZWWXyiuXmWbgriWaWxpcWWeXtcieXtcieXtcieXt",
  "ciWXWWWWvuZZcuXpmccjmWcWWWWXpmccjmZdWiixWWWZWK0XWYWWWWWWWWWXWXYWWWWWWeWWnWWWWWWWWWWmmW",
  "WWYaWWWWWWWWWWWWWWWWaWaeWWWWmYaWWWWaWWWWWemWWWWWWWWWWWWWWWWWWWWWWaWXWWWWWWWWWWWWWaWWWa",
  "WYWWWWWWWWWWWWWeWWWW00mXXWWWWaWWWWmWnWWWWWYaWWemWWWWWWWWmeeWWWXYWWWWWWWWWWWWWWWXYWYaWW",
  "WWeXYWWWWYWWWWWaeWWWWWWWWWWWWWWWWWWWWeWYYWWWWmWWWWWXWWWYYWYYaWWWXWWWWWWYWWWaaXaY10XWae",
  "wYaXZeemWWWmaYXWWWcWWeiaiaiaiWWWWYeimXWfXpWoZcXaciYeimWXWWWaceWmXWWWaWWxfnWWaXspYWXspY",
  "WXspYWXspYWYeWWWWkkXnoeWyyZZamWYWWWWWyyZZamXvuccfWWWWW00+lzy////t///+l+y/////xp//kl///",
  "////+tdd///zv///////////////zv/xoX///dzv////v/////td////////////////////l/vv+Z/+Zl/yt/",
  "yc//vx/xxpyd/yc//vl/uj//ppzpuLXmYZWWWWeWWWXmXZWWWWWaiWWnmWWWWWWWXeuuWWWYcWWWWWWWWWWWWW",
  "WWYcWaj+WWWuYcWWWWcWWWWWeuWWWWWWWWWWWWWWWWWWWWmWccXyWXymWZeWZvWWcaWaaiZuWZvWWcmWdoWWii",
  "YidA001523047"]
@[expose] def ext_full_sort_reds : List (SigEntry × Nat) := []

@[expose] def hint_full_reduce_m6 : x64Isa.Hints := _decH #[
  "dU330318030505110514020A0A0201040F023A060A0209010203040F021834241F041F2F24110513070303",
  "0534002F1A19181D11161B130325310101053411050102074315181E1H111314430D06020B010569090105",
  "1401153401050202020202241F0104060909061F03030704070715201A05140A070A0A1501320303020A06",
  "0903020A060903020A060903020A060903020703030205060A0606060909050F140A060903020A220A0A03",
  "03020302230502070101020A0A03010A24152303221F02020233030201052F242F2F1016180B111A091303",
  "253101010534110501020743152F0F0F1F041F14080F081B242B1423120207030207241312030314X60018",
  "0010034C5IA8123010144CA85IB3114010044CA8B35I114010234CA85I31233030324C5I182010124C5I02",
  "000314C181010134C5IXLJ1K3010644CY6K5IXLJ040001AYLDYRBYJ8YH9YP6YFA4CY6K5IXLJ13A0101BYLD",
  "YRBYJ8YH9YP6YFA4CY6K5IXLJZ230B000564CZR8ZTEY6K5IXLJ1B6010094CZR8ZVHa1GY6K5IXLJZTEa3L20",
  "A90201Da604CZR8ZVHa1GY6K5IXLJaBDZTEa3LaA3a7A12DYW0103FaC6aD2ZR8a7AaA3a604CZVHa1GY6K5Ia",
  "BDZTEa3LXLJ11FG100Fa604CZR8ZVHa1GY6K5IXLJaBDZTEa3LaA3a7AaU1aD20FYW0002A4CZR8Y6K5IZVHZT",
  "Ea3La1GXLJbB210A0102Ea604CZR8ZVHa1GY6K5IXLJbB2aBDZTEbG1a3LaA30EeW0002C4CZR8Y6K5IZVHZTE",
  "a3La1GXLJbB2a60aBD0C0000Ea604CZR8ZVHa1GY6K5IXLJbB2aBDZTEbG1a3LbP30E00064XLJ4CY6K5I0400",
  "0184CZR8ZTEY6K5Ic6BXLJcH11A8010184CZR8ZTEY6K5Ic6BXLJcH122A80200B4CZR8ZTEY6K5Ic6BXLJcH1",
  "dD2dC3dGA0B000374CZR8ZTEY6K5Ic6BXLJ1A7010284CZR8ZTEY6K5Ic6BeOAXLJ118010294CZR8ZTEY6K5I",
  "c6BeOAXLJeR109000224CY6K182010034CY6KXLJ0300023XLJ4CY6K0300049g3Bg89g28g06g7AfU0XLJ4CY",
  "6K1390101Bg3Bg89g28g06g7AfU0XLDXLJ4CY6KgF30B000544CY6KXL8XLJ0400073hM84ChNB0300013hM84",
  "ChTB0300012hM84C11201023hM84CiA1133010B0202872345XV232364190339G4190339041913390419033",
  "9041903390419033904190339YH43113093d151Y159X051oWoWWrWrWuWWWWWXWalWXZmcZaqrcXpZWWdWbpW",
  "aWWWWWWWYWWWWWWWWWWWWZYWWWYWWaeWWkWaZ+WcYrgXZuWeyXmvgrgiiWWepZWWWZZeWWWWWWWWH0eWYWYWWq",
  "WWWWWmWeeeaWWWWWWWWeXWWWmWeWWWWWWWWWmWWWWWWWWWYaWeXWeeWenWWXWmWWWWWWWWaWYYYXWWWWWWWWWW",
  "WWeaWWeeWYWWWWnWW00aWaaaWXWXWWYWbbeWeWaaaYWaWWWeYaaWmWWeWaeWWoWWWWagWaWWWWWWWXYWaanaaW",
  "aemWWmefWWmWaWWYWXXXWmXWWWWmWWnYaaYXeaaWXWWYWemq00XYWWWYWWWWWWWWWWpWWnWWYmWWeXWWWsWmWW",
  "WWWYWWXWWWWWcWWWXWYWWfoWYWWWWWemWWWmWWWWWWWaWWWWWWWWWWWWWaWWW00lt/ttt/z/z+dx/nml/d/ptt",
  "x/t///lxtt+l//l/tl/yh///ttZ/sl////+vzx/tsztt/tk/y+/liZ+l/t//v/yzz+/z///++/+yhttxyltt/r",
  "/thzk+tVeWeeeWYWYXuaWklmWuWieeaWeWWWmaeeXmWWmWemWZqWWWeeyWfmWWWWXcYaWefYeeWenWZXWmpyXm",
  "WeWWcWZYYXWYWWWXXWXZqeeaZmeeWgWeqYnXe0005623047A"]
@[expose] def ext_full_reduce_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 88),
   (("full_sort_reds", [i64, i64], []), 56),
   (("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_div", [i64, i64], [i64]), 24),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("full_arena_sweep_m6", [i64], [i64]), 504),
   (("full_compact", [i64], [i64]), 760),
   (("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_full_reduce_purge_c0 : x64Isa.Hints := _decH #[
  "Y434241F042F1016181B111A1913032531010105341105010207431518330520060A060105690901051401",
  "153401050A010101011A07141F00030330000301072F0F0F1F04D00110010014C01000114C01000314C010",
  "0017OBU9M8K6SAI04C13701018OBU9M8K6SAI04CX5308000514C01000024CXU8122010154CXU8Y12Y60Y23",
  "11581036Y8AY234CXU8Y12Y60116X010064CXU8Y12Y60Y23YP106800244CXU8Y12Z6104000414C01000102",
  "0281a451mWkWemWWXuWmluXmjWnyWakWuirgrcWWZ30XYaWWaYWWWWWaWYWXXXWmWWWWWWWWe80YoqXWWWnYWW",
  "YXXaWYWYWXWWmmmeWmWWWeXea40XcWWXWaWeWXceWmWWWaeWWWeWWWWWWWW00X/uudz//+zv/pxzzmlv/x/y/+",
  "k+/l+////lyltNdduYWWXYcWiaYYlmcWaWZWXnXWmXWWWWmZme80003230"]
@[expose] def ext_full_reduce_purge_c0 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_arena_sweep_m6", [i64], [i64]), 504)]

@[expose] def hints : List x64Isa.Hints := [hint_full_red_less, hint_full_red_sift,
    hint_full_sort_reds, hint_full_reduce_m6, hint_full_reduce_purge_c0]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 88),
   (("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_div", [i64, i64], [i64]), 24),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("full_arena_sweep_m6", [i64], [i64]), 504),
   (("full_compact", [i64], [i64]), 760),
   (("m6_hdr_init", [i64], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Reduce
