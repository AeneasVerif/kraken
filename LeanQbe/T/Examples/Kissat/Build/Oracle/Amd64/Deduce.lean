module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Deduce

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r8, Reg64.rax, Reg64.r9, Reg64.rcx, Reg64.rdx, Reg64.rdi, Reg64.rbx, Reg64.rbp,
  Reg64.r12, Reg64.r13, Reg64.r14, Reg64.r15, Reg64.rsi]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.r9), (.gpr Reg64.rcx), (.gpr Reg64.rax), (.gpr Reg64.r8), (.flag CondCode.nc),
  (.flag CondCode.z), (.flag CondCode.c), (.flag CondCode.nz), (.gpr Reg64.rdx),
  (.gpr Reg64.rdi), (.gpr Reg64.rsi), (.slot 2 .w64), (.gpr Reg64.rbp), (.gpr Reg64.r12),
  (.gpr Reg64.r15), (.gpr Reg64.r14), (.gpr Reg64.r13), (.gpr Reg64.rbx), (.slot 1 .w64),
  (.slot 0 .w64), (.slot 4 .w64), (.slot 3 .w64), (.slot 5 .w64), (.slot 13 .w64),
  (.slot 11 .w64), (.slot 8 .w64), (.slot 9 .w64), (.slot 7 .w64), (.slot 6 .w64),
  (.slot 12 .w64), (.slot 10 .w64)]

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

@[expose] def hint_full_analyze_lit : x64Isa.Hints := _decH #[
  "I401112132302022421050637251816751214300120010300000025495ACBH3P105I004A230002321X1222",
  "0H22320ZnsgdcuqcZmiuwL0YWmmWWWW00mmWXWeebXWW00YWWWeWWWWaWW00l//++//z/llnz//VXXWWYWmmkY",
  "WW00030"]
@[expose] def ext_full_analyze_lit : List (SigEntry × Nat) := []

@[expose] def hint_full_analyze_rsn_m6_hdr : x64Isa.Hints := _decH #[
  "a03517120A01260C0C033D060D0106170E0E041F111A1G32320202062H0214281508200413061704330373",
  "0373037303420304163303420607060H020H45272702040E05010E21060131060102060H0HC2330G0A0E0F",
  "1H0202142A050627010625010600166502144106210601060A13111C1D2H02022421050637251816751214",
  "H0012001054ND496IIC0450014IC49ND6I2HE4C201849ICJBVEX41X6AND6I108c4100A49ICJBVEX41X6AND",
  "6IX2FX8G203Ac4200B49ICJBVEX41X6AND6IX2FX8GXB310Bc41057Y70IC49ND6IJBVE07XO0009Y7049ICJB",
  "VEX41X6AND6I129i81009Y7049ICJBVEX41X6AND6I129i81009Y7049ICJBVEX41X6AND6I129i81075ND496",
  "IICa3H0550016ND496IICa3Ha4E0650016ND496IICa3HaE20650035ND49686IIC115D107AND49686IICbE1",
  "bJ3bMEbPHc0A0AoD00601200105549d6AdCCdHHdP105G00412314J2320aQ2305022500dZiqkjneidWvnrgW",
  "WWiWxacjnWXmXminWy//mWWkWiWuccWWWlcWW+k+k+k+iWWWiYupWkgrWYWkXn40eaWeWWWWaXWYWWWWWWWWWe",
  "YWYWWWmmWoaWWemWWWWWWWWYaWWeYWeWWWeeWWWW00XXWWYWmmgYWWWWaYWaWemWYWoXabXWWWWWWaXWXWWWee",
  "WfYWWaeWWWWWWWWfYYWaXWaWWWaanWYW90aWWWmWWWWeWWWWWWWWXWWWmWWWWWaWWkWWWWWcWcWWWWWWWXoWaZ",
  "cZcZcZaWWWaWeXWdWWWWiceW00X///zz//x++/Zx////pv/p/k//x+hytnz//////tz/z+r/ll/bv//td/////",
  "///bvv/tz/t///tsj/v/DYYWWaXXWyaWWWWicWiWnWWaXqZekYWWWWWWeYWYXgWmmWwcWWeuWWWWWWWWwccWeY",
  "WeWWWefoWcWI00366789AB"]
@[expose] def ext_full_analyze_rsn_m6_hdr : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_full_clear_ana : x64Isa.Hints := _decH #[
  "D23181A27020206243101061216400000001463AA8849040001463AA88491240101563AA8849K20500000a",
  "ecXaWcL0mYWWXWm00eXWYWme00YWWWW00ldz/x+/lVuYWaXWm00000"]
@[expose] def ext_full_clear_ana : List (SigEntry × Nat) := []

@[expose] def hint_full_otfs_large : x64Isa.Hints := _decH #[
  "bE4F1D0E323105074C010104320202370304203000003703041206160H0H04303A00002006030802062211",
  "020627020102061A021101041119071609030619090306391329093000090709045A010004354501120402",
  "0501045109244238020222070A3609000133062A4713020247041030000040003000004000300000400030",
  "00004200041610300000420602040A010A250A0C0C37020931091211150A38083202040208044305020303",
  "020439Q00120010066J4GAD5E8FBE1I6911286J4GQCAD5EMI8FBE138XL10096J4GQCAD5EMI8FBES12329XL",
  "202A6J4GQCAD5EMI8FBES1XB213AXL10494GXVHAD6J8FBEQC5EMI189k810094GQCADXVH5EMI6J8FBE32389",
  "ZI302A4GXVHAD6J8FBEQC5EMIYJ80Ak8001A4GXVHAD6J8FBEQC5EMIYJ80Ak80029XVHAD6J4G8FBEQC5EMI0",
  "9k400014G010001BXVHAD6J4G8FBEQC5EMIYJ8Z2A0Bk4002EXVHAD6J4G8FBEQC5EMIZ32Z2AYJ8ZBKZ910Ek",
  "4000EXVHAD6J4G8FBEQC5EMIZ32Z2AYJ8ZBKZ910Ek4006IXVHAD6J4G8FBEQC5EMIa69ZQLZ32a4MZS3Z2AYJ",
  "8ZBKZ910Iak40078MI5E4G8FBEXVHQC6J2198c32009XVHAD6J4G8FBEQCMI5E431909k4401AXVHAD6J4G8FB",
  "EQCMI5EbE33190Ak43028MI5E4G8FBEXVHcB9QC1A8a3101BcCA8FBEQCXVHcA1cJ3cB9MI5E4G12Bu9100BcC",
  "A8FBEQCXVHcA1cJ3cB9MI5E4G12Bu9100BcCA8FBEQCXVHcA1cJ3cB9MI5E4G12Bu91067MI5E4G8FBEXVHcB9",
  "0730015MI5E4G8FBE05300114G01000254GfO1fK9g885E125K10J040BC095D23042231112313YM23240224",
  "2L2345V2335422230235232254B2243O2243B2224B2243A221102240XC2240a622410pnuWZmWddXgXuXuXW",
  "WW+dWWdnu+dZuylZmW+atWWZmikWXWWzmWWmZuyWXxWXvrmWeWWYmmmWcXeWikWWWWkdWdZmdWZt50XWWWYWWa",
  "WWWmWaWeeWWYaWWWWWWWWWWWaWWWXWWYWWWWWWWWWWWWWWWWWWWWWWWWWWWeWaWmmXWWWWWmXWWWWWaWWWW00m",
  "eXXWWYWWWeWYWaaWWXYWWWWWWWWWWWoWXWWmWXWWYWWWWYaYWaXWmWWamWWWaWmmeaWYWeeWmWWYaeemWXWWYW",
  "XeW00uaXmWZYmWWyW+WYWWZZmXWu+ZZuilXnuWZWZWWXucdWWWWinWWWWuaeWvYaumWWWWWWYWXWWaWWcdWmWW",
  "ZZmXnmpWXo00l//+llzz//x///l/x/pp//zv//////////+h/z/+kZr//x////vtx/tz+l//ol///t++/lt/v/",
  "ld+f//xtdc//zl/x/yl/VXmmYYWWaWWWmWaWiiWWYcWWWWWWWWWWXqWYWXnygWWaWWWWceaWeYXmWWjmWWWeXX",
  "WmeWcWmuXsWWaeuvWWYmWaWZmW000666789AB"]
@[expose] def ext_full_otfs_large : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 136),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_unwatch_large", [i64, i32, i32], []), 24)]

@[expose] def hint_full_otfs_bin : x64Isa.Hints := _decH #[
  "aO4G180D33000007293A07090937051206250511130F5E4204080008320239090906311702010502162211",
  "02062702010206110108081202041219071609030619090306130929091000090709072102000435021207",
  "0205020722093202041213071601090611010906190C210110000107030721023004350212070205030722",
  "01AC2A3A09110642020C06170C1637020601020201011202P0012001004BD4H5D8G2CA4420084HA86CH0F3",
  "BD5D8G2128YK20194HA86CH0F3BD5D8GK2119YK10684HXJEXDF8GBD5DX6AX5C128X0100B4HXJEXDF8GBD5D",
  "X6AX5CXR0XC3Y7912BX0101B4HXJEXDF8GBD5DX6AX5CXR0XC3Y7912BX010364HXJEXDF8GBD5D06X000184H",
  "BD5D8GXJEX6AXDFX5C08400184HBD5D8GXJEX6AXDFX5C08400284HXJEXDF8GBD5DZ78X6A08X000014H0100",
  "01A4HXJEXDF8GBD5DZ78X6AX5CZ510AX0002C4HBD5D8GXJEZ78X6AXDFZ51X5CZFBZD20C4000C4HBD5D8GXJ",
  "EZ78X6AXDFZ51X5CZFBZD20C4006G4HBD5D8GXJEZ78X6Aa59ZS3XDFa3KZ51ZTLX5CZFBZD20GXW400664HXJ",
  "EXDF8GBD5D06X000014H01000184HXJEXDF8GBD5DX6AZ7808X0002A4HXJEXDF8GBD5DZ78X6Ab83b620AX00",
  "00A4HXJEXDF8GBD5DZ78X6Ab83b620AX0006E4HXJEXDF8GBD5DbU1bL9bSBZ78bMCX6Ab83b620Ef000654HX",
  "JEXDF8GBD12501037dD9dF14HXJEXDF8GBD127010074HXJEXDF8GBDdS2dF107000I0607408C065ZE230C02",
  "2C0N23250431430C242412C0F431430C242412C052335323423225252253D2223G2222522135431430C242",
  "412C0XE23221iA51krhtmWWdWYXyeyufdaXucWWYWyXuZWXcWWeWWYmoWXmWWmdWWiWauWXWWWgYWmWcXeWWbm",
  "ZpmllomWWdWkWd50meeWWWWWWWWWWWWWWWWWWWWWWWWWWWWeWWWWWWWWWWWWWWWWWWWXWWaWmmWmWWWWWWWWWW",
  "aamYWWW00eaamXWWWWWWWWWemeXWmWWamWWaWmmeaWWWYaYWeaWWoWWWmYYXWmWYWeeWeeeXWWWWWWbYYeXWYW",
  "00qWmXWWaaWieWWWWWYaWWWaeWXYaYWWWWWWYWWWnWWWXYWaemeWWWWWWeWXWWaWWWWmfneYXWWWWXmdWn00l/",
  "////+lltsXz/////////c/lz+l//ol//t++/lt///vtx/lp/+f//+/xxz+//v/ld/ldlz//v///rvxlz/x/VXm",
  "mef+YWWWWWWWWWvWmYXmWWjmWWeXXWmeWWWceaWmiWXsWWXWaaYXWWcWmuWmumYWWcWWWgcamYWaW000566789",
  "AB"]
@[expose] def ext_full_otfs_bin : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 136),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_unwatch_large", [i64, i32, i32], []), 24)]

@[expose] def hint_full_otfs_subsume : x64Isa.Hints := _decH #[
  "X15705122817001000310100171107010A2117011207024107010A21170908060108500000003000000144",
  "9C25A830440031490100014C2F85A830460000hWXZmYXiWamymsG0XXWWeWWmaWXWWWWW00mmWaWWeYWWnWWX",
  "W50XmWWWWWcWWYiWY00Z/+c//t//lx/+z//z/LXvWWeWWmaWXYWWYWA0000"]
@[expose] def ext_full_otfs_subsume : List (SigEntry × Nat) := []

@[expose] def hint_full_deduce_1uip_m6_hdr : x64Isa.Hints := _decH #[
  "lS85120124020517110208060C0C0A3D060D0806170E0E041F11181G323202020622021423150329041A06",
  "17043A0A7A0A7A0A7A0A420A04163A0A420607060G020G45272702040E05010E21060131060102060G0G72",
  "3A03080F0G190202142805062701062501060316650214410621060106021819131C2A0101242905060725",
  "0816650114811918131C2A02022428050607250916650214811918131C2A02022428050627250916650214",
  "720105181A1913101C2D12D50A2E0F0204273501051G0805170A0G01160C0C023D060D010617010A040101",
  "030229390909062909142815082004120617043909790979097909420904163909420607060A010A351717",
  "01040005090029060939060901060A0A19330A090208100202142905062701062501060A16650A14410621",
  "06010603000A0D0C190101142A0506072500166501146C0A070A2406150F0D051G05160705022117081808",
  "3A0A081711070121170112070248070828170A010608010209080A07020206243101061216120G47110701",
  "110701051607052117081808320208171207021207020209080A0702020624310106121609080A17020206",
  "2431010612160E2709080A1702020624310106121609080A17020206243101061216150209180A07020206",
  "24310106121609180A1702020624310106121619181A1715020202062431010612161502Y900120010014H",
  "131010734HX2DTC0320013TC4HX2D2GE3420174HTCUJXAEXF1XH8X2D197Y410094HTCUJXAEXF1XH8XDFXJG",
  "X2D29A9e4200A4HTCUJXAEXF1XH8XDFXJGX2DXMA19Ae41056YI9TC4HX2DUJXAE06O0008YI94HTCUJXAEXF1",
  "XH8X2D128a81008YI94HTCUJXAEXF1XH8X2D128a81008YI94HTCUJXAEXF1XH8X2D128a810744HX2DTCaEG0",
  "4200154HX2DTCaEGaFE05200154HX2DTCaEGaP205200334HX2DTC113210784HX2DTCbK1bPAbSFbV9c6808a",
  "I00B54HdC2dI3dNAdV905G00314H01000554HeR1f13f6AfE805G00854HgA1gG3gLAgT805G00324HhP30200",
  "0224Hi6N1E20100B4Hi6Ni2Oi0PiBQhURi8Ci8Si43i4MhQT3128B0302AiSA4Hi6Ni2Oi0PiBQhURi8Si4MhQ",
  "T218A0203D4HjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQT0DYW200014H010005G4HjTDj0FjOCjDGjEKiSB",
  "i6Ni2Oi0PiBQhURi8Si4MiVEhQT0GmWI001GjOC4HjTDj0FjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQT2A0",
  "GmWK201K4HjOCjPUk5Lk81k93jTDj0FjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQT10KeWg4100M4HjOCjPU",
  "k5Lk81k93jTDj0FjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQTk7IkAJ202MeWg4200N4HjOCjPUk5Lk81k93",
  "jTDj0FjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQTk7IkAJkC210NeWg4105Jl80jOC4HjTDj0FjDGjEKiSBi",
  "6Ni2Oi0PiBQhURi8Si4MiVEhQTjPUk5L0JbWX8000Ll804HjOCjPUk5Lk81k93jTDj0FjDGjEKiSBi6Ni2Oi0P",
  "iBQhURi8Si4MiVEhQT12LmWq8100Ll804HjOCjPUk5Lk81k93jTDj0FjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4Mi",
  "VEhQT12LmWq8100Ll804HjOCjPUk5Lk81k93jTDj0FjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQT12LmWq81",
  "07H4HjTDj0FjOCjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQTn4A0HmWI001I4HjTDj0FjOCjDGjEKiSBi6Ni",
  "2Oi0PiBQhURi8Si4MiVEhQTn4An500ImWI001I4HjTDj0FjOCjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQTn",
  "4AnC10ImWI003G4HjTDj0FjOCjDGjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQT11GmWI107L4HjTDj0FjOCjDGj",
  "EKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQTo11o63o9IoC0oJ90LXamWI00BH4HjDGjEKiSBi6Ni2Oi0PiBQhURi8",
  "Si4MiVEhQTpP3pSDpV9q6A0HYYW2003E4HjDGr0CjEKiSBi6Ni2Oi0PiBQhURi8Si4MiVEhQT1AEaW210614H0",
  "1000634HrK2rEG03000214H01000144HrK2rEGrN10480034t69t8At784H12401014t69t8At784H0400025t",
  "69t8At784HtG205000364HtR2rBDrAFhQTjEK06000314H0100084v99vBAvA84H12401014v99vBAvA84H040",
  "0025v99vBAvA84HvJ20500024vT9vVAvU84H12401014vT9vVAvU84H0400025vT9vVAvU84Hw820500034wM9",
  "wOAwN84H12401014wM9wOAwN84H0400025wM9wOAwN84Hx120500024xB9xDAxC84H12401014xB9xDAxC84H0",
  "400025xB9xDAxC84HxM20500034y39y6Ay584H12401014y39y6Ay584H0400025y39y6Ay584HyE20500024y",
  "O9yRAyQ84H12401014yO9yRAyQ84H0400025yO9yRAyQ84Hz4205000224HhP30200005zF9zJAzH84HhP3125",
  "01025zF9zJAzH84HhP30500026zF9zJAzH84HhP3zV206000L02065XD230ClV23C1UE3983673D23503B538C",
  "374C2257542282890232C6223B32344H23A1B233C2231322301C2241ZK430C312042C0221XF2311XM2211Z",
  "U221CaS223CcJ221D0aWnWufWYXgmaecXaWamaecXaWXWWemiYeWeWnWuamWmWWnWuamWmXYXmfWWWWXWamyms",
  "WeWaWpuWaecXaWWWWWbmYkWebmYekehWYWWWmaWWccvXpiecWZaeWWWZWcvXpieWiWiZaedWWWdWcWeaeWWXyu",
  "WZvxvxvxvmWWXmhYiXuWWeXuaYXWdZWul/rrgqWXnseixYXmucijgsXnseixYXmWvnrguZZimvsaZWXpZgqWWW",
  "uXseixYWZWZWvYXv/WWWyWuXmiiWWW+iWXyzyzyzyuWWWubncWyrgWaWyWfWipgL0XYWeXWeWmWWmYWaXWWWmY",
  "WaXWWWXWaWeYWWYWeWmaWWeYWeWmaWWaWmXWWWWWWWWWWWWWYWWWWWWmYWaWWWWWWWWWWWWWWWWWWWWWmWYama",
  "WWWWWWXWmmWWWWYXWYWWWWXWeWmWWWWWWaXWXWWWnWYemWXYWWWWWWWWWemWXWeXWWXXWWWWWWWmeWWWWWWWWe",
  "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWmeWmWWWWeYWaWWWWWWWWmaWaWWXXWWaeWWnWWWWWW",
  "WWWaeWWmaWmWWWmmWWWWXWWW00XWaWmaWYWWeXWYWmeWeXWYWmeWmmYWaXWmXWaWeYXWaXWaWeYXWYWeWmaYWW",
  "aWnWWXWqnWmYWWWeXWYWmeWWeeWeWXWeWemWWmbaeXXYeYWWWYaWWmefeeWWXWmXWYaWWmamfXeeWWWYWmWmWW",
  "emXaeWWnWWWWWWWWXaeeWmaWmWWmoaWeameeaeXWWWWWXWWWWnWWaYYYmmWWWWWWnWWaYYgYWWWWWWXYWWeaaq",
  "aWWWWeaWeWnWWaXaYegYWWWWWeYWYWWWmmWoaWWemWWWWWWWWoaaWeYWeWWWefYWaYemaW00eWWWWWWWWYWWWW",
  "WWWYWWWWWWWWaWWWWWWWeWWWWWWWWeWWWWWWWmWWWWWWWWYiWYWWWWWWiWWWYWWWWWWWWmWWWWWmWXcWXWWWWW",
  "WWWWWWeWWaWWWXWWWWWWWWeWWaWWWWWXWWZmWWZWZWWWWWWWceWmiuiuiuimWWWmXWaWyWWXmvWWWWWWWeWWWW",
  "WWWWWYWWXWWWWYWWWWWWYWWXWWWWeWWWWWWaWWYWWWWmWWWWWWWWYWWXWWWWWWeWWyWWWWiWiWWWWWWWZaWeci",
  "ciciceWWWeWmYWkWWWWuimWWWWW00Zly/t+/ttx//dz/x+/l/dz/x+/l++lx/tz+/y/t/lxz/ty/t/lxz/v/l+",
  "/tx//t+z//z+sz+/xt//dz/x+/l//Zl/l/z/l/k//+/rtlzzvlx///xt/+/lill//y+ly/xt/+/o/byll///x+",
  "/+/g/k/ytd/+y////////ytdd+/t+//++vt/ds/Zltlz/////z///+z//txxu+//////+z//txxZx//////zx/",
  "/ltsdt////dp/d+z//tytvlZx/////lx/xzh++/+hp//kl///////+hpp/lx/l///lix/pxklt/VmZWeXWeeaW",
  "WuYWaXWmWuYWaXWmXXmaWeYXWZWeWmaYWeZWeWmaYWcWmXWeaWWeXYWWYXfYXWaeWWuYWaXWmWWymWmWYWmWnW",
  "WXWgemYYcmaWWWaeWXWmpmmWWZXmZWaeWXWjWwZmmWWWaXWXWrWnWZeuWXZWWWWWWWWZeuuXWeXWWXXceWufWy",
  "memYWWWWWYWWWXYWWeaadXWWWWWWXYWWeaayaWWWWWWYaWWmefueWWWWuiWuXYWWeZecmyaWWWWWmaWaYqXXWX",
  "qiWWnmWWWWWWWXqiiWmaWmWWWmpaWianmeW000E66789AB"]
@[expose] def ext_full_deduce_1uip_m6_hdr : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("full_otfs_large", [i64, i32, i32], [.bool]), 328),
   (("full_otfs_bin", [i64, i32, i32], [.bool]), 312)]

@[expose] def hints : List x64Isa.Hints := [hint_full_analyze_lit, hint_full_analyze_rsn_m6_hdr,
    hint_full_clear_ana, hint_full_otfs_large, hint_full_otfs_bin, hint_full_otfs_subsume,
    hint_full_deduce_1uip_m6_hdr]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("full_wstack_defrag_m6", [i64], []), 136),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_unwatch_large", [i64, i32, i32], []), 24)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Deduce
