module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Minimize

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rax, Reg64.rdi, Reg64.rsi, Reg64.r8, Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.r13,
  Reg64.r14, Reg64.r15, Reg64.rcx, Reg64.r9, Reg64.rdx]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rsi), (.flag CondCode.nc), (.gpr Reg64.rax), (.gpr Reg64.rcx), (.gpr Reg64.rdx),
  (.flag CondCode.nz), (.flag CondCode.z), (.flag CondCode.c), (.gpr Reg64.r8),
  (.gpr Reg64.rdi), (.gpr Reg64.rbp), (.gpr Reg64.r14), (.gpr Reg64.r9), (.gpr Reg64.r12),
  (.gpr Reg64.rbx), (.gpr Reg64.r15), (.gpr Reg64.r13), (.slot 0 .w64), (.slot 3 .w64),
  (.slot 2 .w64), (.slot 1 .w64), (.slot 9 .w64), (.slot 6 .w64), (.slot 5 .w64),
  (.slot 4 .w64), (.slot 10 .w64), (.slot 8 .w64), (.slot 7 .w64), (.slot 17 .w64),
  (.slot 11 .w64), (.slot 18 .w64), (.slot 14 .w64), (.slot 15 .w64), (.slot 16 .w64),
  (.slot 13 .w64)]

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

@[expose] def hint_full_min_mark : x64Isa.Hints := _decH #[
  "F500112130304150613072843030404200000002390C2G40300000XsoaYb30XWW00mqW80YWWWW00Z///++t",
  "/FXXeWG0000"]
@[expose] def ext_full_min_mark : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_tmp : x64Isa.Hints := _decH #[
  "c6291A0707131B071412120228521202220708070C00072C0D0C0E020601020100000501A208011732070A",
  "0A0208013C0C0C2C0C7C0C0C2C0C7C0C0C2C0C7C0C0C2C0C480C01173C0C0C2C0C4807054D0C0D080A0700",
  "013E0E0828082A0A0C0C5E0E0828082A0A0C0C5E0E0828082A0A0C0C5E0E0828082A0A0C0C200801173E0E",
  "0828082A0A0C0C20071700170E070E00070037072909085F0F0C2C01280C090A0D0G076C090807176C0908",
  "0707090149494949020901174902073A0A022C110E240408374007V000000036696HH48AEBC328C602006H",
  "48A696HEBC338C0603026H4EBC3696HXII0600029XHE696HEBH4XO0C38AXFD0900009696HH48AXFDXHEXO0",
  "EBC312901009696HH48AXFDXHEXO0EBC312901009696HH48AXFDXHEXO0EBC312901058696HXHEXO0C3YH2E",
  "BH40800008XHE696HYH2EBH4XO0C318801008XHE696HYH2EBH4XO0C318801008XHE696HYH2EBH4XO0C3188",
  "01046696HC3YH2EBH40600008696HXHEXO0C3YH2EBH42A8802026696HC3YH2EBH410601006696HC3YH2EBH",
  "410601006696HC3YH2EBH410601046H4EBC3696HXII12601018H4EBC3696HeHJeFKXII1280101AH4EBC3eP",
  "0eMEeI26HeHJeFKXII3ADGA0300DeQAeSGeRDeP0eMEH4C3eI26HeHJeFKXIIEB0D0002AeRDeI2eP06HeHJeF",
  "KXIIH4C3EB18A0100BeRDeP0eMEH4C3eI26HeHJeFKXIIEB298B02029eI2eP06HeHJeFKXIIC3H4EB0900009",
  "eI2eP06HeHJeFKXIIH4C3EB298902028eP06HeHJeFKXIIC3H4EB12801008eP06HeHJeFKXIIC3H4EB128010",
  "08eP06HeHJeFKXIIC3H4EB12801054C3EB696H10401007C3EBhQC696HhI0hLA127Y41007EBC3696HhI0hLA",
  "hR207X000A0200112301XI2330eP2310223223222122232Y62210X42210922102hM51051ZcdZWiiWdWWdpv",
  "yyWWXyWW+WWiu/ZWWWWWZWvnmWcXpZsXpZsXpZsXpZWWWuWdpZWWlcdlcdlcdlccWWZWWgrguWWWWWWusigne5",
  "0XWWmWaWWWWWeWWWWWWYWWXWWWWWWWWfWXXXWWWWYaWWWWWWWWWWWWWWWWWaWWYWWWaeWWWWWWWWWWWWWXWaeW",
  "WWWaaeWaWWWWWWW00mWeWYWWYWYaWWWWWenWWemWaWWWWWamWmmmWWWXYWWWWWWWWWWWWWWWWYYWWnWWWYaWWW",
  "WWWWWWWWWaWmYaWWWWoYbWYWWWWWaYG0XYXfWbaWWWYWmeaWaWWqWWgWWagffWWWWWXaiqmXYevfoevfoevfoe",
  "vfXWeeWWvfWYXopXopXopXooYuXWYWWWeWnWaWWgWbWWW00X+l/l/x//v/xp/////cyl/kd/tWZ///suY++l//",
  "/zv////////////////vv/+y///xp////////////p+lxp///+hxqlvZ////neVXmWmWaWWcWaiWWWWWvZmWnu",
  "We/yWWWfdzXXmWWWYcWWWWWWWWWWWWWWWWccWXZWWWaiWWWWWWWWWWWWiXmaiWWWXqahmcyWWWWkt000464567",
  "89"]
@[expose] def ext_full_sort_tmp : List (SigEntry × Nat) := []

@[expose] def hint_full_min_lit_dfs_m8 : x64Isa.Hints := _decH #[
  "bI5G00000112061936181C1E1C1D12020727371213141B0B0B453D343E0304012006150F00073F070F0007",
  "062706110F1000150600070940000000150404050802070E000E0303200000012906061404151526090707",
  "360801090167110314041506040709440404040606110F1000150600070940000000150404050802070E00",
  "00000129060614041515260907073609016711031404150604070944040404374543130104100015060007",
  "09400000000E01H001200103B4ATCVL9G7MHKNNPORIEPA00B000524ATC1220100E4ATCVLXGQ9G7MHKNNPOX",
  "EJRIXKBXCREP3284E0300E4ATCVLXGQ9G7MHKNNPOXEJRIXKBXCREP3284E0307OXQ24ATCXR8XTDVLXGQ9G7M",
  "HKNNPOXEJR9RIXKBXCREPY14YGHY63Y5EY74YLF0OgeWW0003IXTD4ATCVLXGQ9G7MHKNNPOXEJRIXKBXCREPX",
  "Q2XR8Y5E0IaWW0002KXTD4ATCVLXGQ9G7MHKNNPOXEJRIXKBXCREPXQ2XR8Y5EY74Z1F0KaWW0009IXQ2XTD4A",
  "VLXGQ9G7MHKNNPOTCXEJRIXKBa30XCREPXR80I00095XQ24ATCa40b93050004IXTD4ATCVLXGQ9G7MHKNNPOX",
  "EJRIXKBXCREPXQ2XR8Y5E0IaWW0002KXTD4ATCVLXGQ9G7MHKNNPOXEJRIXKBXCREPXQ2XR8Y5EY74bVF0KaWW",
  "0009IXQ24ATCXR8XTDVLXGQ9G7MHKNNPOXEJRIXKBXCREPcR00I00085XQ24ATCcS0dV305000334ATCeL21E3",
  "010144ATCeL2eQE04000264ATCeL2eQEf03f2406000J020514236A323A0623117234B3228406396334353X",
  "4638C32A370H22218230232213YE22A4522C5922C1D2249ZS22A4522C5922C1D22492aN5l///////////Vb",
  "05l///////////VZiWXabukWWWWxWWfYWzuXuWZaoXmWWXWWxWWfYWWWWjmWanWdkWXuWZaoXmiWWWmWjmWanW",
  "iWZmaiZtW+YgmyiWbgqzY10mWWWWmWWWWeWWWWWaWWaWWWYemWWWWWeWWWWWaWWWWWWWWYWWXWWWWYemWWWWWW",
  "aWWWWWYWWWXWWWWWWWWWWWWXXYmWWWW00eWWWagWmWmaWWWWXYmaYWYYXaafWqaWaWWWWXYmaqWWWWWneYWmWo",
  "YXaafWqaWWYWWWWWneYgWqeafXWWXWWWXWmmWWXWeG0aWWWWuWWWWWXWWWWWimWeWWWWWWWWaWWXWWWWWWWWWm",
  "WWWWZaWWeWWWWWWdaWYWWWmWWWWWZXmWaXoWWuWWaWWWWWWW00X/d///th+/+/t////zw/tx/vxyttj+nt/sp/",
  "//zw/st////+zlx+/+fxyttj+nt//xf///+zlxh+plpjz//z///z+k///z/kVuWWWeqXWXWeWWWWYbWeaWcaZe",
  "eoXkeWfiWWWYbWfeWWWWXYmaXWXsaZeeoXkeWWasWWWXYmaqXimioYWWYWWWYXnWWWYWn000B6456789"]
@[expose] def ext_full_min_lit_dfs_m8 : List (SigEntry × Nat) := []

@[expose] def hint_full_shrink_lower_m8 : x64Isa.Hints := _decH #[
  "X0420412021515310213031506130720430303032102130315061307204303030360012001013496894032",
  "0020000002294L20200020000002294XD20200050203CB631C301323162102322C1242102C1M22320cwemf",
  "ZWWcwemfZWo90aWWWWWWWaWWeW00YYmaWWWWYYmaXa00eWWWWWWWeWWWWWW00X////xw/t////xw/tztVabWeW",
  "WWWabWeYe00030"]
@[expose] def ext_full_shrink_lower_m8 : List (SigEntry × Nat) :=
  [(("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]), 136)]

@[expose] def hint_full_shrink_blk_bool_m8 : x64Isa.Hints := _decH #[
  "bL621C141E1F131A1D1G0E074A0A0A1D0D0D0D240007BA013409091909150608013606080404200614000A",
  "073407040A074A00000047043A14050804070835081404160807060704042D0E0414041515210A14041506",
  "04070044040404110A140415060407004404040438080E050536070401A008011730072G35320214040404",
  "110410001506000708400000000E0705013404100000003404100000003404100000003404100000000204",
  "01173404100000000207R001200100FRE88CCK35SA26B4QOPET7UMVQX0GX1IF14FXW0100FRE886BK3CCA24",
  "Q5SQX0MVGX1IFOPET7U240FmW02026CCK35SA26B4Q3D4G60300DCCK35SA26B4QOPET7UMVQX0GX1IF5ED0G8",
  "De05007XLDCCK35SA26B4Q1G70100FXLDCCK35SA26B4QXKEQX0MVGX1IFOPET7U2G8FmW0210IXLDCCK35SA2",
  "6B4QXKEOPET7UMVQX0GX1XM0XNGXPAIF18IXW0108KXKEXLDYAG5SA26BYEM4QQX0M9MVGX1CCIFYMRK3OPET7",
  "UYJ024NKuWW4204JYAG5SA26BYEM4QQX0MVGX1CCIFZ6X2Z9LYMRZ5NK3OPET7U4ED48JeWW1400IZBDYAGCCK",
  "35SA26B4QYEMOPET7UMVQX0GX1IFZC4ZAE0IYW2002MZAEZBDYAG5S6BYEM4QZ6X2K3CCOPET7UZ9LYMRZ5NZD",
  "8A2QX0MVGX1IF1AMaW4101KYAG5SA26BYEM4QQX0MVGX1CCIFZ6X2Z9LYMRZ5NK3OPET7UZD83ED4KeWW1308P",
  "ZAEZBDYAG5SA26BYEM4QQX0MVGX1CCIFZ6X2Z9LYMRZ5NK3OPET7UZD8ZO9ZOOZLO0PXWWW4004OZAEZBDYAG5",
  "SAK6BYEM4QQX0MVGX1CHIFZ6X2Z9LYMRZ5NKJOPET7UZDIZOOaQA0OXWWW4004PZAEZBDYAG5SA26BYEM4QQX0",
  "MVGX1CCIFZ6X2Z9LYMRZ5NK3OPET7UZD8ZO9ZOObEA0PXWWW40033c8DCCK303000274QCCK3c8DA25ScAG070",
  "0008c8DA25ScAG6B4QCCK310801008c8DA25ScAG6B4QCCK310801008c8DA25ScAG6B4QCCK310801055494Q",
  "CCK3c8D1E501016494QCCK3c8DdAE0600028494QCCK3c8DdAEdE2dM40800033c8DCCK312301003c8DCCK31",
  "2301003c8DCCK3123010X30208CA23IA623G41C3F73A63E53BC3H2381S2218X4222G123632237C7221E822",
  "580235C34111351443923D592229F222B4234C663CC2142CIC22C4322C89831030B32A333020C0082012B0",
  "2A223314218204J22A442204482012B02A2233082012B02A2233082012B02A2233222C8B22C80222862214",
  "22218T222HXA222H0YiWWYkXdWpmfmWWWWxWWfYXcZpWiWXgrhWWWWWWWxWWfYWWxWWfYXamiWWYekWWdWWWcW",
  "kWnmWWWanmduXmeuYrgL0mWWnWWWWWWWWWWeaWWWWaWWWWWWaWnWWWWWeWWWWWWWWWWWWWWWWWmWWWamWWWWWW",
  "XWWWWWWWWWWWWWWWXWWWWWWW00eWWemWWWWWWWWXaYWWWXYmaWWaWYWemWWWYbWWWWWWXYmaWWWXYmaYeWWYga",
  "WmaaWWmWWnWmaWqWfeWXWWmWWWmWW00XaWeXcWpWfmamWWWWXWWWWWYWXWaWeWWXXWWWmWWXWWWWWWXWWWWWWW",
  "aWWWWYWWZmZWWicWWuWWWWemWWWmaeWWW00dd//kl////////ytv///zw/t//t/v/kl///vrn/////zw/t///z",
  "w/txl//xZt+/tt/+//+j+lt+t/bl/z/+l//+///VuWWnmWWWWWWWWZecWWWYbWeWWeWcWnmWWWcgkWWWWWYbWe",
  "WWWYbWeamWWayeXWeeWXWWXoXmeXeWwmWYWXmWWXWWW000J6456789"]
@[expose] def ext_full_shrink_blk_bool_m8 : List (SigEntry × Nat) :=
  [(("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]), 136)]

@[expose] def hint_full_min_shrink_m6 : x64Isa.Hints := _decH #[
  "ZG2F1B2637071E12137202120103100015060007094000000004075202022318080D272202023612020708",
  "0D020117301A07040202020703074743052912071415001502020721330307121705011273020117230701",
  "03014420020307172303032408172303033608030744200203072BV0000000034G6F8B03000124G8B02000",
  "26MKKHIE8B4G6F06000064GIE8BMKKH6F146010074GIE8BMKKH6FR407000294GIE8BMKKH6FR4X12X330900",
  "035IE6F4G8BKH0500006MKKHIE8B4G6F1A60100AM0MKK4KHY13IE8B4G6FXPA28DAG200AY7DMKKHIE8B4G6F",
  "XPAY13Y680Ae00027Y7DMKKHIE8B4G6F0700027IE4GY7DMKKH8B6F1A701018IE4GY7DMKKH8B6FYSA080005",
  "54G6FIE8BKH19501005IE6F4G8BKH292502006IE6F4G8BKHZG219601025IEKH4GZR98B0500018ZS46FZV0Z",
  "R94GIE8BKH12801018ZS46FZV0ZR94GIE8BKH0800029ZS46FZV0ZR94GIE8BKHa820900027ZR94G6FZS4IE8",
  "BKH13701007ZR94G6FZS4IE8BKH13701007ZR94G6FZS4IE8BKH137010534GZR98B0300015KHIE4GZR98B05",
  "00005IEKH4GZR98B223502025KHIE4GZR98B12501018K0KHbT4IEZR9bK24G8B18841007bK2bV8KHIE4GZR9",
  "8B0700026bV8KHIE4GZR98B2236020502071U431A300XM22A0122C1c822C00ZmziWcuWdZWiiWWjmWWYWWrg",
  "qWWemiamXYWZXmZiWWWWuWWYdZWbnsWWXsWWoYjrgmZnL0mWeWXXWWWaXWemWWWWnWaWmaaWaWeXWXYWeaWXWW",
  "mWeWWWeWWWWeWWWWWWWa00eWWmeWaWWmmWXYWmaeWWWYemYWeYYaYWaWmWnWaWWmmWeWaWWWaWWWYbWeWWWYmY",
  "00mWYeWXfWbaWWamWWWWaWWWWWWWaWWWWWXWmWaWmWWeWeWWnWWemWWWYWWWWaWWWWW00////Z/+/l/t/++d/z",
  "x+ltd///vklx/lxxtv/t+/+b/p/++k/l/t///p///xr/l///u/xVyWXWmWeWXXuWYaXmeuWWWcnmaWmaaecWeX",
  "WXwWiWXXnWmWeWWWiWWWagWmWWWdWa00026456789"]
@[expose] def ext_full_min_shrink_m6 : List (SigEntry × Nat) :=
  [(("full_sort_tmp", [i64], []), 88),
   (("full_shrink_blk_bool_m8", [i64, i64, i64, i32, i64], [.bool]), 344),
   (("full_min_lit_dfs_m8", [i64, i32, .bool, .bool], [.bool]), 136)]

@[expose] def hints : List x64Isa.Hints := [hint_full_min_mark, hint_full_sort_tmp,
    hint_full_min_lit_dfs_m8, hint_full_shrink_lower_m8, hint_full_shrink_blk_bool_m8,
    hint_full_min_shrink_m6]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Minimize
