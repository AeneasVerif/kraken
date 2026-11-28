module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Watch

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rbx, Reg64.r15, Reg64.r9, Reg64.rbp, Reg64.r8, Reg64.rdx, Reg64.r12, Reg64.r13,
  Reg64.r14, Reg64.rdi, Reg64.rsi, Reg64.rcx, Reg64.rax]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.r9), (.gpr Reg64.rax), (.flag CondCode.nc), (.gpr Reg64.rdx), (.gpr Reg64.rbx),
  (.flag CondCode.c), (.gpr Reg64.rdi), (.gpr Reg64.rsi), (.gpr Reg64.rcx), (.gpr Reg64.r8),
  (.gpr Reg64.r14), (.flag CondCode.nz), (.gpr Reg64.r12), (.gpr Reg64.r13), (.gpr Reg64.rbp),
  (.gpr Reg64.r15), (.flag CondCode.z), (.slot 2 .w64), (.slot 1 .w64), (.slot 0 .w64),
  (.slot 4 .w64), (.slot 3 .w64), (.flag CondCode.g)]

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

@[expose] def hint_full_wsort_sift : x64Isa.Hints := _decH #[
  "L40010253033403052000300503044101422000010230000000034657783019303014465778D9234402000",
  "ZdpWyudc00YWW00aWeWWWXWW40XXvWkeZo00dp/l/p/y//JiWmWiWZWWC00010"]
@[expose] def ext_full_wsort_sift : List (SigEntry × Nat) := []

@[expose] def hint_full_wstack_radix_sort_m6 : x64Isa.Hints := _decH #[
  "ZR6A110BA10402153105023404340404047404340404047404340404047404340404044104021534043404",
  "040441054C0C0D010405023C0C310101012D0D00005C0C310101012D0D00005C0C310101012D0D00005C0C",
  "310101012D0D0000240102153C0C310101012D0D000024050244444444010402154401050305K000000007",
  "8EAA784657699F137010188E78B34657AA699F08000088EAA78B34657699F118010088EAA78B34657699F1",
  "18010088EAA78B34657699F118010388EAA7869B346579F08000088E78B34657AA699F118010088E78B346",
  "57AA699F118010088E78B34657AA699F118010588EAA6978B346579F08000088EAA7869B346579F2418020",
  "189FB38E5769AA784608000088EAA6978B346579F148010088EAA6978B346579F148010088EAA6978B3465",
  "79F148010588EAA784657699FB308000089FB38E5769AA7846118010089FB38E5769AA7846118010089FB3",
  "8E5769AA78461180101060120340450yWW+ldpmWZWukiWXmiddiZXvxWukkucZpWWWiW+ZpWWlXvxukk+Zptm",
  "yuWXmWbgri00mmWnWWWWWWfWWWWWnWWWWWWWWWWWWWWWWWWWoWWeWWWaeWWWWWWWWWWWWWWamYaWWWWG0eeWem",
  "WWWWXWmWWWWemWWWWWWWWWWWWWWWWWYXWWaWWWYaWWWWWWWWWWWWWWmeXYWWWW80eYXWmWWXafdaWeoappanay",
  "vafdcfYfvWWWaWYfvWYXayufdcYfvmokeWWmXWWWa00ddd/kl////z+l////kl/////////////////xy//p//",
  "/xp/////////////+/dzv////FuuWnmWWWWYXmWWWWnmWWWWWWWWWWWWWWWWWaZWWiWWWaiWWWWWWWWWWWWWXW",
  "uYcWWWWG0006036781"]
@[expose] def ext_full_wstack_radix_sort_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_wstack_defrag_m6 : x64Isa.Hints := _decH #[
  "ZP351404161A170B98084G0502030500290C41053G02080113030211030108020E0B1E0008025101340105",
  "290930050104480842290008020B0E0B1128055101340105290930050104480842290008020E0B03030808",
  "030308080B4E0E330339090B080803030B0B010240202020010002150140010501040D05K0000000144FEA",
  "C6G73C03403005C6G74FEAA45C1093505016C6G74FEAA4K14C093604035C6EAG74FXHC0500045G7C6EA4FX",
  "HC0500005XHCC6G7EA4F1E501016Y5EXHCC6G7EA4F0600006Y5EXHCC6G7EA4F3083603017Y5EXHCC6G7EA4",
  "FYB3214702045G7XHCC6EA4F1E501016G7XHCC6EA4FZLE0600006G7XHCC6EA4FZLE3083603017G7XHCC6EA",
  "4FZLEZT32147020414F14101005C6EAG74FXHC24D502018C6EAG74FXHCbGDbF4bU9080001BC6EAG74FXHCb",
  "GDbF4bU9bKEc18c3311B0100BC6EAG74FXHCbGDbF4bU9bKEc18c3311B0100BC6EAG74FXHCbGDbF4bU9bKEc",
  "18c3311B010502019c9431930A042912A04431930A042912A00oYWWWyWWcivuWWWZppWWWWWWclcXvmkiWuW",
  "WWclcXvmkiWWWeeWWWiW+kaYqJ0aWmWaeWWWWWWXWWWWWWXWWWWWWWaWWWWWmWWWWWWaWWWWWWWmaWWWWWWWW0",
  "0YWeWYaWWWWmgWmWWYWWWmeWmWWWYWWeWeeeWmWWWYWWeYeYWfYWWXWWWeW40YWWWWWWqXnfWYneWWYZoWymda",
  "WeWWWYZoWymdaWWaXWWWWaWcaWWW00d//v/d/xp///+lZ+///x//+ld+//d/v//l/lld+//d/v//dxZx/jv/zb",
  "///l/NcWuWaiWWWXmyXWWWaWWXmuXWWuWcWWmWmmuXWWuWcWWuayaWocWYwWWWmW80026036781"]
@[expose] def ext_full_wstack_defrag_m6 : List (SigEntry × Nat) :=
  [(("full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], []), 56)]

@[expose] def hint_full_watch_push_slow_m6 : x64Isa.Hints := _decH #[
  "ZJ5C1101020B0B2G2G1121020117070211011707022A1D1F300037070E0G0G1101052B110F052G380E0116",
  "0G06022G37070E06223G0G4G0G37071102010109090105091101052B01010707210F010609054F00000808",
  "0B024323232301030215460105012G3E050102A108021531050101210119O00110010157H8E6I449C05700",
  "257H8E6I449C165710257H8E6I449C165710067H8E6I449CO6067003D44XPEXAA9CXO77HXCD8E6IXJ0XEFX",
  "N7X860DYj0002944XPE8EXAA9C7HXCD6IXEF09b4003644XPEY418EXAA9C068001C7HXCD8E6I44XPEXEFXAA",
  "9CXJ0XO7XN70CYWD001D7HXCDYF18E6I44XPEXEFXAA9CXJ0XO7XN70DaWP002644XPEYF1XAA9CXO7060003A",
  "44XPEXAA9CXO77HXCDYF18E6I0Av0002544XPEXAA9CXO705000287HXCD8E6IXPE44XAA9C38798D301A7HXC",
  "D8E6IXPE44XAA9CZR9XEF287AD202C44aH9aJFaG7XAA9CaL0XPE7HXCD8E6I0CZe0000D7HXCD8E6IaG7aJFa",
  "N8aL0aH9XPE44XAA9C11DD100D7HXCD8E6IaG7aJFaN8aL0aH9XPE44XAA9C11DD100D7HXCD8E6IaG7aJFaN8",
  "aL0aH9XPE44XAA9C11DD105844aH9aJFaG7XAA9CaL0XPE080001744aH9aJFaG7bREXAA9C070000844aH9aJ",
  "FaG7bREXAA9CaL01180100844aH9aJFaG7bREXAA9CaL01180100844aH9aJFaG7bREXAA9CaL0118010C0603",
  "406A0094432B315YP2251622B2M2251622B2U2251622B2T230442240Y32251622B20pWWuWYrgsWWycWZmWX",
  "nnnuWXWWWZWmWXWyWdmkcWZmuWmWZmuecXWXvwqWoWeeauuW20eXYWWWWWmXWaWYaWWWWWaWWWWeeWWeWXWWXW",
  "mWWaYaYWWaWWmmfWWWWeWWWWWYWa00aWnWWWWaeWmYWXYWWWWWoWYWWaaWWaWWmeameWWYXYWWWYYWeeamWWWa",
  "WYXWXXWoG0iWWeWmWWYYWiYWWWXWWWWWWqWmWWYWmWaiWXmYWWnmemWWXmfWWaWWumWWWWWWWWWW80X///p+y/",
  "///pl+/v/zv////+h/ud/tpp/t/+/ls/d//xyx///xv/lds////t/xz/zz+gViXZWWWWimXWcWYcWWWWXqWduW",
  "eiiWeWXWmfWuWWaZaWWWacWmufWWWWeWaYWYYXr00036036781"]
@[expose] def ext_full_watch_push_slow_m6 : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 136)]

@[expose] def hint_full_watch_push_m6 : x64Isa.Hints := _decH #[
  "XF571101020B0B0911100B1500080510000805381020003800000B00022G380908023G0G4G0G311102010G",
  "01022G3109A001100101789787J6346579707XF00254657637J8905U001989I1G97J634657KH9709YP000A",
  "89I1G9787J634657KH970AbP005646G9I189X3I97068001D46G9XF0X3I9789XDK7JX5L6357KHI10DXt0002",
  "B46G9X3I9789XDK7JX58X5LXF0630BXZG002646G9X3I9789XDK06XG004746G9XF0X3I9789XDK07Z000H523",
  "0BD2322R23324231B023522234B022B2522B36225022251B22B3K22C0222B1B22B2522C3622B0222B10kZW",
  "WXXuWlWyWWycWZphWYWWYmW20mWWWWWWXWWXWmWWWWWWeWWa00eaeaWXWmfWmWWmfWWWXWaaeWoG0cXYWWWuWZ",
  "WaeWiYafnWWWWWWWW80///lplt/z+/j+l/+/a///z/ttl+gVmimeWYXWoXmWXWxWWWYWeemXr00060"]
@[expose] def ext_full_watch_push_m6 : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hint_full_wstack_defrag : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_wstack_defrag : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 136)]

@[expose] def hint_full_watch_push : x64Isa.Hints := _decH #[
  "XF571101020B0B0911100B1500080510000805381020003800000B00022G380908023G0G4G0G311102010G",
  "01022G3109A001100101789787J6346579707XF00254657637J8905U001989I1G97J634657KH9709YP000A",
  "89I1G9787J634657KH970AbP005646G9I189X3I97068001D46G9XF0X3I9789XDK7JX5L6357KHI10DXt0002",
  "B46G9X3I9789XDK7JX58X5LXF0630BXZG002646G9X3I9789XDK06XG004746G9XF0X3I9789XDK07Z000H523",
  "0BD2322R23324231B023522234B022B2522B36225022251B22B3K22C0222B1B22B2522C3622B0222B10kZW",
  "WXXuWlWyWWycWZphWYWWYmW20mWWWWWWXWWXWmWWWWWWeWWa00eaeaWXWmfWmWWmfWWWXWaaeWoG0cXYWWWuWZ",
  "WaeWiYafnWWWWWWWW80///lplt/z+/j+l/+/a///z/ttl+gVmimeWYXWoXmWXWxWWWYWeemXr00060"]
@[expose] def ext_full_watch_push : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hint_full_watch_pop_c0 : x64Isa.Hints := _decH #[
  "S371808021318380830000E0G050125040808050102A1090215310504500000004546QED377X1405000074",
  "6QED377X14P0X381170100746QED377X14P0X381170100746QED377X14P0X381170102020C5C230B0XuWuW",
  "YrgsWWcWddg20eXYWWWWWmWWWWW00aWnWWWWaeegWWWG0eWmWWYYYWWZYW80d//p+y////pldZ//+ViXZWWWWi",
  "muyWWX0001203"]
@[expose] def ext_full_watch_pop_c0 : List (SigEntry × Nat) := []

@[expose] def hint_full_unwatch_large : x64Isa.Hints := _decH #[
  "XB361101021B1E1130003C0C05070002490G0809090802091B05430903200279131809022302490825436C",
  "0C7000000038H1T744FE76RCU063188a01036H1T744FE76RC23960202644FE76RCH1T7208602006H1T744F",
  "E76RC303860302644FE76RCH1T723860201644FE76RCH1T70600010400909A0kZtZuXyWXbyWZuYWWkWXvwo",
  "20YWXXWWWWWYeaWWWWWWW00XWWmmWWeWXaYXWaeWWaG0fpXeWqWWWqWXeWWmcWWumW80/////z/+kl//d/ztvz",
  "/tl//sVYWXnmWWuWYecYWemWWf00003036"]
@[expose] def ext_full_unwatch_large : List (SigEntry × Nat) := []

@[expose] def hint_full_has_bin : x64Isa.Hints := _decH #[
  "T4808030201020G080G18199702070307310136060605381B01080G011530011001043X13K9XD611301013",
  "X13K9XD61130101040C505A0XiWyyZ/wmW10aWWWWWWWWWWW00YYYWeWWWWWaqG0aYigXvuWW00/xvx/l/+l//",
  "mWVacaWmWXmWWl/00000"]
@[expose] def ext_full_has_bin : List (SigEntry × Nat) := []

@[expose] def hint_full_delete_bin_side : x64Isa.Hints := _decH #[
  "X6371101021E183101330C0G090530031B050101000G1515030263333333010302156301053C0C80000000",
  "2644DE77PCF8R91160100744DE77PCF8R966117Y0101744DE77PCF8R966117Y0103644DE77PCF8R9060000",
  "644DE77PCF8R91160100644DE77PCF8R91160100644DE77PCF8R91160101040090951X352kZmZyWWyyy/WW",
  "WWYiWddg20YWWnWWWWWWemWWWWWWW00XWWemWWWWYaemaWfWWWG0fmXiWeiiihXWWXWaWZYW80l//y//kl////",
  "vtkit/j//+VZWWnmWWWWcenpeWoWWX00003036"]
@[expose] def ext_full_delete_bin_side : List (SigEntry × Nat) := []

@[expose] def hint_full_delete_binary : x64Isa.Hints := _decH #[
  "YU3411010217183101330C0G000539031B050101090G1515030269393939010902156901053C0C3E110102",
  "13183101370C0G000539071B050101090G1515070269393939010902156901053C0C41080823031B070308",
  "0823031B0703110B01H000000003466E540360028466ED774PCF8R054118a21008466ED774PCF8R054118a",
  "21018466ED774PCF8R054118a21038466E54D774PCF8R00860008466ED774PCF8R054118a21008466ED774",
  "PCF8R054118a21008466ED774PCF8R054118a21053466E540360028466E54YU3YOEZACZ08ZC01186100846",
  "6E54YU3YOEZACZ08ZC011861018466E54YU3YOEZACZ08ZC011861038466E54YU3YOEZACZ08ZC0086000846",
  "6E54YU3YOEZACZ08ZC011861008466E54YU3YOEZACZ08ZC011861008466E54YU3YOEZACZ08ZC0118610104",
  "03500A2X352ZG52XXcWpYZmyW/WWdddduWWWWpWXvwmmkZmZyWWyyy/WWWWYiWddg20eWWWWWWWWmWaeWWWWWY",
  "aWWWWWWWWWWWYWWnWWWWWWemWWWWWWW00aWWWWWWWWeWYaWWWWWnYaXWYeWWaWWWXWWemWWWWYaemaWfWWWG0Z",
  "WXmWYiWhWYZZZYueWWeXWWumYWWfmXiWeiiihXWWXWaWZYW80ltx/z/////d/xp////+jxpb/xl//t///y//kl",
  "////vtkit/j//+VeaWYWWWWWuWaiWWWWXoaiwWamWWeWWWZWWnmWWWWcenpeWoWWX00003036"]
@[expose] def ext_full_delete_binary : List (SigEntry × Nat) := []

@[expose] def hint_full_prioritize_binaries_m6 : x64Isa.Hints := _decH #[
  "X92A0A1D14181F0B570730000205000553091B05290156273527030B0247474747010702154701051E0590",
  "011001005FF9D7AB4D82CE502016FF9D7AB4D8IE11601027HCFF9D7AIED8B4276702008B4D8V0HCFF9D7AI",
  "E3176803018B4D8V0HCFF9D7AIE3176803039HCFF9D7AIEXT6XV3D8B411901009HCFF9D7AIEXT6XV3D8B41",
  "1901009HCFF9D7AIEXT6XV3D8B411901000ZmWZvy+kWWWuzpWpWWddWr90aYWYaWWWWWXWmWWWeWWYWWWW00Y",
  "XWXYWWWWWameWWWbWYfWWYW00XXWmeWWaWeinWXWWZYWW00Xvy/zv/////o/l///r/xb//x/VcZWYcWWWWWjWm",
  "WWWgWawWWaW00006036781"]
@[expose] def ext_full_prioritize_binaries_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_bin_watches_fid : x64Isa.Hints := _decH #["000000000000100000"]
@[expose] def ext_full_sort_bin_watches_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_has_ternary : x64Isa.Hints := _decH #[
  "Y5580D2B170711430A052B490500032F052B470509032G07000B0007101E093101030315331B022601066C",
  "1B05060C0C055106012M0G09020G000307000103000G0000252G0G70011001017I1466A7F5D98G72037S20",
  "267F6A5D98I14629367203AXVEXT7XTHY73Y7IXRJ7F6A5D9811Ak0105BYKLXVEXT7XTHY73Y7IXRJ7F6A5D9",
  "8290By0200CYKLXVEXT7XTHY73Y7IXRJ7F6A5D98Z2C3946Cy0302DZA6YKLXVEXT7XTHY73Y7IXRJ7F6A5D98",
  "Z2C290DXu02030601B08507AY7631532230AQ233C0XnmWb/ZXkWdbWWZvmWlcXzaP0aaWWWWmWWWWWWWWmWWW",
  "WWWaWWWmWW00oYWaWagWXXeWWgWeWWWeWYYWWeeWX00emeWvXWYXZmWWXuWWdWWyW00/+xx/twph/zzl//h/l/",
  "/nklxxv/ll/zVXaaWebiqWYYmWWqWmWWknmaacWmmWY00046036781"]
@[expose] def ext_full_has_ternary : List (SigEntry × Nat) := []

@[expose] def hints : List x64Isa.Hints := [hint_full_wsort_sift,
    hint_full_wstack_radix_sort_m6, hint_full_wstack_defrag_m6, hint_full_watch_push_slow_m6,
    hint_full_watch_push_m6, hint_full_wstack_defrag, hint_full_watch_push,
    hint_full_watch_pop_c0, hint_full_unwatch_large, hint_full_has_bin,
    hint_full_delete_bin_side, hint_full_delete_binary, hint_full_prioritize_binaries_m6,
    hint_full_sort_bin_watches_fid, hint_full_has_ternary]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Watch
