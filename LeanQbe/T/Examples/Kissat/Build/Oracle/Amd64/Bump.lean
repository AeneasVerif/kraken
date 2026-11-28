module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Bump

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r14, Reg64.rdi, Reg64.r13, Reg64.rax, Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.r15,
  Reg64.rsi, Reg64.rdx, Reg64.rcx]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rbp), (.gpr Reg64.r12), (.flag CondCode.nz), (.gpr Reg64.rdx), (.flag CondCode.c),
  (.gpr Reg64.rax), (.gpr Reg64.rcx), (.gpr Reg64.r15), (.gpr Reg64.rdi), (.flag CondCode.nc),
  (.gpr Reg64.rbx), (.gpr Reg64.r14), (.gpr Reg64.r13), (.gpr Reg64.rsi), (.gpr Reg64.r9),
  (.gpr Reg64.r8), (.flag CondCode.z), (.slot 3 .w64), (.slot 4 .w64), (.slot 2 .w64),
  (.slot 0 .w64), (.slot 1 .w64)]

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

@[expose] def hint_full_rescale_m6 : x64Isa.Hints := _decH #[
  "H2011024304050604270405121819481A0440000000034B8160153010034B81602563020254BL7OC81601A",
  "5010202001M20230iWWWeWu50mWWWWXWW00eWYWeWmWG0aWWWWWe00/d/x/j+h+VuWaWoXqX00006456207"]
@[expose] def ext_full_rescale_m6 : List (SigEntry × Nat) :=
  [(("f64u_div", [i64, i64], [i64]), 24),
   (("f64u_mul", [i64, i64], [i64]), 24)]

@[expose] def hint_full_rescale : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_rescale : List (SigEntry × Nat) := [(("full_rescale_m6", [i64], []), 88)]

@[expose] def hint_full_bump_var : x64Isa.Hints := _decH #[
  "T2C2910281D3203091E1005260629043211021F0F0F230319390842152940000000124AHB02000564AHBQ0",
  "6C5COE166G10084AHBQ06C5COER5X91168G10204028041C20030iWjnvcWayciqXnj60aWWYWWWWWWWWWWaWW",
  "00YWWXWYYWWnXeWXYWW80cWaueZeWaWaWWWW00dx//z/xx/+zyl/zx//FaWWYWaaWXYZmWYaWWG000545620"]
@[expose] def ext_full_bump_var : List (SigEntry × Nat) :=
  [(("f64u_add", [i64, i64], [i64]), 0),
   (("full_rescale_m6", [i64], []), 88)]

@[expose] def hint_full_bump_decay : x64Isa.Hints := _decH #[
  "225191000000022230102210010X00G000+VX00010"]
@[expose] def ext_full_bump_decay : List (SigEntry × Nat) :=
  [(("f64u_mul", [i64, i64], [i64]), 24),
   (("full_rescale_m6", [i64], []), 88)]

@[expose] def hint_full_queue_renumber : x64Isa.Hints := _decH #[
  "F261E1F1534040335050D032504250530000000048EAF6648335D40300448AF66D30400000YibWsWYL0XWW",
  "WfW00mWWam00aWWWWW00/+///o/VXWWWjW00000"]
@[expose] def ext_full_queue_renumber : List (SigEntry × Nat) := []

@[expose] def hint_full_queue_mtf : x64Isa.Hints := _decH #[
  "XL350A092G16131110322G2F0F041D0D042D0D3D0D3F1E0F092E1E092F1F0F0945090515060D0E15340403",
  "35050F03150425054G2505800000002848I18AK05AG375E608G004A48I18AK05AG375E6XHFXJE0AuG00184",
  "8I18AK05AG375E608G001448I18AK0040001448I18AK00400017YDDYEEYC648I18AK0335F70300748I18AK",
  "0YEEYC6YH3070001020480onvcYWsWYWmfcWmiYcWsfncWmuuzgp10aWWmWWfWWYWWWWWWWWWWWWeWYYWWW00Y",
  "WWeWWamWXWWmWXWWmWWWWaaXXWWa80eYWWWWWWWWYWWaWYWWWmYWWWWaWW00//x//l//o//z/+//z/+/////mt",
  "zz//pFaWWmWWjWWYWXWWYWXWWWWWleYYWWiG0003456"]
@[expose] def ext_full_queue_mtf : List (SigEntry × Nat) := []

@[expose] def hint_full_ana_sift_m6 : x64Isa.Hints := _decH #[
  "P580E09550504251604280804281406054E0E04281925080E096000000004406A5D8F38E3403017406A5DE",
  "3DEC88F15701015406A5D8FE3265502018406A5D8FE3N5O6DE18801018X66406A5D8FXAEE3X75188X01010",
  "40490510XmucWucWuc00YWWYWmYW00YWaXWWXWeXW40meYWeYWeY00Zv/tz/dz/dz/JcWeYWuYWuYWC000245"]
@[expose] def ext_full_ana_sift_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_ana_qs_m6 : x64Isa.Hints := _decH #[
  "dP241504161A131104290002100E08095303042D13042E0E042E14030D4808042E192D0E0809020C02132D",
  "045303042D13042E0E042E14030D4808042E192D0008090C02093E0E042030000E003E0E042030000E003E",
  "0E042030000E003E0E042030000E000D0E09143E0E042030000E000D0415D60E09143604560606440E0400",
  "0D04224E0D060409300E0E210D500E0E210D500E0E210D500E0E210D260D0914300D0D210E260428041966",
  "66666605060914660504093808042F3F0F080F3808042F3F0F080F3808042F3F0F080F3808042F3F0F080F",
  "0D0809143808042F3F0F080F0D04300E120F2608044D04096666666605060914660504XQ000000044DAB68",
  "55C04000045CB685DA10401015P05CB685DA0500005P05CB685DA3E8F503018P05CB685DAVFU8TE1D80101",
  "6P05CB685DAVF23D602019P05CB685DAVFX8DX93U81E901019P05CXN3B685DAXR8VFXOD1E9Y01043DAB685",
  "1C301014DAB685YCC0400004B685DAYCC308F403017B685DAYKFYJ8YI0YCC1D701015DAYCCB685YKF23D50",
  "2018DAYCCB685YKFYTDYU3YJ81E801018DAYCCZC3B685ZG8YKFZDD1E8X01045F3H15CDA480500007B685DA",
  "F3H1485C1D701007B685DAF3H1485C1D701007B685DAF3H1485C1D701019B685DAF3H1485Ca1Da4E109e01",
  "019B685DAF3H1485Ca1DaKE109e01019B685DAF3H1485Ca1Db4E109e01019B685DAF3H1485Ca1DbKE109e0",
  "1039B685DAF3H1485Cc6Dc9E109e010225CDA13201003cP55CDA33F8303006cQ3cRF5CcP5cS8DA0600006c",
  "P5cQ3cRF5CcS8DA16601006cP5cQ3cRF5CcS8DA16601006cP5cQ3cRF5CcS8DA166010365CcP5cRFcQ3cS8D",
  "A2E0602006cQ3cRF5CcP5cS8DA3DE0603014cP55CDAcS823F402016cRFcQ35CcS8cP5DA06000065CcP5cRF",
  "cQ3cS8DA26D602016cRFcQ35CcS8cP5DA16601006cRFcQ35CcS8cP5DA16601006cRFcQ35CcS8cP5DA16601",
  "0535CDAgM3153010035CDAgM3153010035CDAgM315301043F35CDA0300005B685DA5CF31D501005B685DA5",
  "CF31D501005B685DA5CF31D501017B685DA5Ci3DF3i681F7Y01017B685DA5Ci3DF3iM81F7Y01017B685DA5",
  "Ci3DF3j681F7Y01017B685DA5Ci3DF3jM81F7Y01037B685DA5Ck8DF3kB81F7Y010235CDAF30300003F35CD",
  "A1D301006F3kUE5CkQDkT0DA15601006F35CDAkQDkT0kV506000335CDAF3153010035CDAF3153010035CDA",
  "F31530101020280X+WWlv/dy/WWvmiWuWZcXmWWiudWvmkXpWyZcXmWduWX/dy/pyWWZZZWWiikuuznnxZZWWc",
  "WWZuuXmWbgrieWciZWWWvmkXpWyZcXuciZWWWXmucWucWucWiWWWZXmiXmiXmiWWcbg40XWWemWWWWWWWeWaWm",
  "WmWWmYaWWYWWWaWWWeWWWmWaWXYWWWWWWWXXWWWaeWWWWWWWWWWWWeWemWWWmYaWWWWXWWXWaeWWaWWWeWWWmW",
  "WXWWeWWWYWWYWmYWWWWeWWWaWWaXWaWWWWWW00mWaeWWWWWWYaWYWeWeWWeXYWWXWWWYWWWaWWWeXYWWnWWWWW",
  "WWemmWWYaWWWWWWWWWWWYaWaeWWWeXYWWWWWmWWmYaWWYWWWaWWWeWWWmYaYWaXWWXWeXWaWaaaWeYWWYWmYWe",
  "YemWH0gWaYmgXebWWemaWeWrYWmXYqeYbemagnWerYWmWXeWmgXebWqWWXXXWYaaceeimmvXXWWYWWWeeWmXWW",
  "WaWXgaXWYbemagnWerYWngaXWWWWmeYWeYWeYWaWWWXWmaWmaWmaWWWWW00X+l/td//////xp/x/l/d//lzv//",
  "z///x///t///lzv/+y///////kkl//xp///////////xp/taZ//dzv////+l/+/xp//x///t///l//+/xpv/tz",
  "/dz/dz/t/ttp/lx+lx+lx/dxkbg5XmWeuWWWWWWaiWaWmWuWWmYcWWYWWWaWWWeWWWmYcWXZWWWWWWWnnmWWai",
  "WWWWWWWWWWWaiWexyWWuYcWWWWXmWXWaiWWaWWWeWWWmWWXWaicWeYWuYWuYWeWeeiWmaXmaXmaWuanwrQ0004",
  "4562"]
@[expose] def ext_full_sort_ana_qs_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_bump_analyzed_mode_fid : x64Isa.Hints := _decH #[
  "bS421C171516131811101B221502052215050G2205383D02041G1403150405340609250505042512120505",
  "0504322G0406420506193D090D0609250F290535050504322G040846040E14221505150416250504150422",
  "150406051D2G5231010442190B280D2203090F0B0716061904321D02180808230319390E42132905040819",
  "09923505044206091G0308070D321G1F0F041F0F042F0F2F0F1B1F0B092F0F092B1F0F0926090616030B0E",
  "0634040836060F08060426063G15050104X30000000144AO0KHAC040001AEIO0GJ4AACM1C7IKQBKH0A0000",
  "A4AO0KHACEIGJM1C7IKQB0A0002A4AACM1O0C7EIGJQBIKKH0A0000AEIO0GJ4AACM1C7IKQBKH0A0006D4AAC",
  "M1O0C7EIGJQBXR3XV5XVLIKKH1ED01007M1O0AC4AQBKHXR3070002E4AACM1O0C7EIGJQBXR3XVLIKKHY2EY4",
  "615E0101D4AACM1O0C7EIGJQBXR3XVLIKKHY2E0D0000E4AACM1O0C7EIGJXR3XVLY2EQBIKKHYF50E000AF4A",
  "ACM1O0C7ZKFEIGJXR3XVLY2EZCDQBIKKH16FYW0101G4AACM1O0C7ZKFEIGJXR3XVLY2EZCDQBIKKHZL60GYW0",
  "00644AO0KHAC04000144AO0KHAC0400006M1O0AC4AQBKH15601016M1O0AC4AQBKH06000244AO0KHAC04000",
  "1000000114A01000054AKHO0ACbEL155010164AKHO0ACbELbO506000374AKHO0ACbELbOKcA5070005B4AKH",
  "O0ACbELbOKcAJcGBbS1bR1cFF16Bm0100D4AKHO0ACbELbOKcAJcGBbS1bR1cFFcH7cTD16Dm010764AKHO0AC",
  "bEDbEL06000154AKHO0ACbEL115010164AKHO0ACbELe81060004D4AKHO0ACbELe81eP7eC5eQDeB5eO8eJ6e",
  "N30Dm0004F4AKHO0ACbELe81eP7eC5eQDeB5eO8eJ6eN3fIBfKF0Fum0001D4AKHO0ACbELe81eP7eC5eQDeB5",
  "eO8eJ6eN30Dm000194AKHO0ACbELe81eP7eC5eQD09000194AKHO0ACbELe81eP7eC5eQD090001CgBBgCEgA3",
  "4AKHO0ACbELe81eP7eC5eQD386FC0300C4AKHO0ACbELe81eP7eC5eQDgCEgA3gE80C000C02041L833130932",
  "A343XE2311G23139228272214XH2280ZL2318K22A3A230332323ZG22A31e651YZmuWbmWWeWiXWuWuYmucWm",
  "nZmaXyZX/yWWWWWXmXsdauWpmoWYZYdmidvnWmiWmiWaeceWjmXnuZmmuWkaWxWZZmWmiXmXnWWWZtcYXmYXng",
  "rgJ0XWWeWYWWYeWWWWWWWWWWWWWeWaeWWaXWWWWeeYWmWWeWWWWWWWWWeWWmaWWWWWXWmaWWWWmWeWXaaYWYWY",
  "YWmeWYeeaYaXWaeWWWWWWWWaWmaaWWW00mWaWXWWXaWWmXWWYWYWWWWaaYaWfYWmYWWaaXWeWWaWeeWYabWYaW",
  "aeYWeYWWWmeYWYWWemaWWoYXWXWXXWeaWXaaYXYWmYaWWfXeWWmYWeYWWWW40meWWWWWWWaWWeWeWWeYWWWWmW",
  "WWXWWWWWWWWWuWpXWjWWmWWWWWWWaWWWaWWWWaWWWWWWWmWWeXuYWucWWXWWWmWWaWmWWWWWXpWWWWWWWWWW00",
  "X+l/t/z//yt/+/z//x/x////mtxt/bx+/x//tty/l//t/ll/xtn/xt/tlx/lx/p+/lx/x//k/p/+xxz/z/yz/d",
  "t/zttxzx+/xtt/jzl/k/x/lx////NXmWeWYWWZeWXWYWWaWaWWWWleaeWwaXWaWWeeZWmWWeWmmWaekWaeWema",
  "WmaWiXWmaWaWWnWiWXaaYWYWZYWueWYeeaYaXWaeeWoYmWnWaWmaWWWW80056456207"]
@[expose] def ext_full_bump_analyzed_mode_fid : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_div", [i64, i64], [i64]), 24),
   (("f64u_add", [i64, i64], [i64]), 0),
   (("full_rescale_m6", [i64], []), 88),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("full_sort_ana_qs_m6", [i64, i64], []), 40)]

@[expose] def hints : List x64Isa.Hints := [hint_full_rescale_m6, hint_full_rescale,
    hint_full_bump_var, hint_full_bump_decay, hint_full_queue_renumber, hint_full_queue_mtf,
    hint_full_ana_sift_m6, hint_full_sort_ana_qs_m6, hint_full_bump_analyzed_mode_fid]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_div", [i64, i64], [i64]), 24),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_add", [i64, i64], [i64]), 0),
   (("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 8)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Bump
