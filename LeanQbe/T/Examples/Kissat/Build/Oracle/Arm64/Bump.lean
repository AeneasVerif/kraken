module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Bump

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X11)), (XRegOrSp.reg (XReg.X1)),
  (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X10)), (XRegOrSp.reg (XReg.X7)),
  (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X28))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.gpr (XRegOrSp.reg (XReg.X26)))]

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

@[expose] def _rLoc (cs : List Char) : Option (Loc armIsa.Reg armIsa.VReg
    armIsa.Cond) × List Char :=
  let (i, cs1) := _rNat cs; (_locs[i]?, cs1)

@[expose] def _rMove (cs : List Char) : Option (Move armIsa.Reg armIsa.VReg
    armIsa.Cond) × List Char :=
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

@[expose] def _rEntry (cs : List Char) : Entry armIsa.Reg armIsa.VReg
    armIsa.Cond × List Char :=
  let (nl, c1) := _rNat cs
  let (lv, c2) := _rList (fun s => let (sa, s1) := _rSymArg s
    let (lo, s2) := _rLoc s1; (lo.map (sa, ·), s2)) nl c1
  let (np, c3) := _rNat c2
  let (pl, c4) := _rList _rLoc np c3
  let (lz, c5) := _rBools c4; let (pz, c6) := _rBools c5
  ({ live := lv.filterMap id, ploc := pl.filterMap id, liveZ := lz, plocZ := pz }, c6)

@[expose] def _rPre (cs : List Char) : PreStep armIsa.Reg armIsa.VReg
    armIsa.Cond × List Char :=
  let (pk, c1) := _rNat cs
  let (ms, c2) := _rList _rMove (pk / 2) c1
  ({ clearFlags := pk % 2 == 1, moves := ms.filterMap id }, c2)

@[expose] def _rVar (cs : List Char) : VariantHint × List Char :=
  let (t, c1) := _rNat cs
  match t with
  | 0 => (.default, c1) | 1 => (.adcx, c1) | 2 => (.adox, c1)
  | 3 => (.mulxFast, c1) | 4 => (.decInc, c1)
  | _ => let (o, c2) := _rNat c1; (.disp (Int64.ofBitVec (BitVec.ofNat 64 o)), c2)

@[expose] def _decH (chunks : Array String) : armIsa.Hints :=
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

@[expose] def hint_full_rescale_m6 : armIsa.Hints := _decH #[
  "H201102430405060728070512191A491B0740000000034C8160153010034C81602563020254CL8OD81601B",
  "5010202001M20210iWWWeWu50mWWWWXWW00eWYWeWmWG0aWWWWWe00/d/x/j+h+VuWaWoXqX00006345206"]
@[expose] def ext_full_rescale_m6 : List (SigEntry × Nat) :=
  [(("f64u_div", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0)]

@[expose] def hint_full_rescale : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_rescale : List (SigEntry × Nat) := [(("full_rescale_m6", [i64], []), 64)]

@[expose] def hint_full_bump_var : armIsa.Hints := _decH #[
  "X025160A16231E2602030A1F1G0H26061E0A0723021I021E0E33030J0A2J0K524A400000001249HL020005",
  "649HLQG655MOF166G110849HLQG655MOFX9IRH168G11502078B8301318337329060A129228112210O22730",
  "kWjuudWaiYiqWnj20aWWYWWWWWWWWWWaWW00YWWXWYYWWnXeWXYWW80cWaueZeWaWaWWWW00dx//z/xx/+zyl/",
  "zx//FaWWYWaaWXYZmWYaWWG0040"]
@[expose] def ext_full_bump_var : List (SigEntry × Nat) :=
  [(("f64u_add", [i64, i64], [i64]), 0),
   (("full_rescale_m6", [i64], []), 64)]

@[expose] def hint_full_bump_decay : armIsa.Hints := _decH #[
  "2291A100000003020811230802280010X00G000+VX00010"]
@[expose] def ext_full_bump_decay : List (SigEntry × Nat) :=
  [(("f64u_mul", [i64, i64], [i64]), 0),
   (("full_rescale_m6", [i64], []), 64)]

@[expose] def hint_full_queue_renumber : armIsa.Hints := _decH #[
  "F261J1F1537070335050E032507250530000000048JAF6649335E40300449AF66D30400000YibWsWYL0XWW",
  "WfW00mWWam00aWWWWW00/+///o/VXWWWjW00000"]
@[expose] def ext_full_queue_renumber : List (SigEntry × Nat) := []

@[expose] def hint_full_queue_mtf : armIsa.Hints := _decH #[
  "XT36050K130N131E1I1G0F0F0F021F0N2F0F071F0F072F0F3F0F3F1J0F0K2J1J0K2F1F0F0K460A0616030H",
  "0J1637070E36060F0E16072606160G060N2505800000002849II85KG55GE76E308K004A49II85KG55GE76E",
  "3XHFXJJ0AuK001849II85KG55GE76E308K001449II85KG044001449II85KG0400017YDHYEJYC349II85KG3",
  "E6F70300749II85KGYEJYC3YHE0700000omXcYWsWYWmfcWmiYcWsfncWmueXgn10aWWmWWfWWYWWWWWWWWWWW",
  "WeWYYWWW00YWWeWWamWXWWmWXWWmWWWWaaXXWWa80eYWWWWWWWWYWWaWYWWWmYWWWWaWW00//x//l//o//z/+/",
  "/z/+/////mtzz//nFaWWmWWjWWYWXWWYWXWWWWWleYYWWkG0000"]
@[expose] def ext_full_queue_mtf : List (SigEntry × Nat) := []

@[expose] def hint_full_ana_sift_m6 : armIsa.Hints := _decH #[
  "P5G0J0K5303072F13072G0G072G14030F4J0J072G1K2F0G0J0K60000000044966558E3GJH403017496655E",
  "HDJCG8E1F7010154966558EEH23F5020184966558EEHNFO3DJ1G801018X634966558EXAJEHX7F1G8X01010",
  "20BC0XmucWucWuc00YWWYWmYW00YWaXWWXWeXW40meYWeYWeY00Zv/tz/dz/dz/JcWeYWuYWuYWC0000"]
@[expose] def ext_full_ana_sift_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_ana_qs_m6 : armIsa.Hints := _decH #[
  "e22416071E1H131F041J0A0I021I0G0F0K5909072319072G0G072G1409034F0F072G1K230G0F0K02050219",
  "25045909072519072J0J072J1409054303072J1K250J030K0G020A3G0G072I3I0I0G0I3G0G072I3I0I0G0I",
  "3G0G072I3I0I0G0I3G0G072I3I0I0G0I0J0G0A173G0G072I3I0I0G0I0J071649097J090A143J045909092L",
  "0L070G040I0J07224G0J09040A3J0G0G2I0L5J0G0G2I0L5J0G0G2I0L5J0G0G2I0L290J0A173J0G0G2I0L29",
  "072E041A560666666609060A17560609070A3F0F072J3J0J0F0J3F0F072J3J0J0F0J3F0F072J3J0J0F0J3F",
  "0F072J3J0J0F0J090F0A173F0F072J3J0J0F0J09073G0I120J260F044E070A560666666609060A17560609",
  "07XQ000000044DHBE8655040000455BE86DH1I401015PI55BE86DH0500005PI55BE86DH3GFJ503018PI55B",
  "E86DHVJUFTG13801016PI55BE86DHVJ293602019PI55BE86DHVJX83X99UF1G901019PI55XN9BE86DHXRFVJ",
  "XO31G9Y01043DHBE861G301014DHBE86YCG0400004BE86DHYCG3J3F403017BE86DHYKFYJ3YIJYCG1570101",
  "5DHYCGBE86YKF295502018DHYCGBE86YKFYT5YU9YJ31J801018DHYCGZC9BE86ZG3YKFZD51J8X01045F3HF5",
  "5DH490500007BE86DHF3HF49551J701007BE86DHF3HF49551J701007BE86DHF3HF49551J701019BE86DHF3",
  "HF4955a1Ja4G1I9e01019BE86DHF3HF4955a1JaKG1I9e01019BE86DHF3HF4955a1Jb4G1I9e01019BE86DHF",
  "3HF4955a1JbKG1I9e01039BE86DHF3HF4955c6Jc9G1I9e0102255DH13201003cP655DH33FE303006cQ3cRF",
  "55cP6cSEDH0600006cP6cQ3cRF55cSEDH1J601006cP6cQ3cRF55cSEDH1J601006cP6cQ3cRF55cSEDH1J601",
  "03655cP6cRFcQ3cSEDH2GI602006cQ3cRF55cP6cSEDH3JGI603014cP655DHcSE23F402016cRFcQ355cSEcP",
  "6DH060000655cP6cRFcQ3cSEDH29J602016cRFcQ355cSEcP6DH19601006cRFcQ355cSEcP6DH19601006cRF",
  "cQ355cSEcP6DH1960105355DHgM31930100355DHgM31930100355DHgM319301043F355DH0300005BE86DH5",
  "5F319501005BE86DH55F319501005BE86DH55F319501017BE86DH55i39F3i6F1J7Y01017BE86DH55i39F3i",
  "MF1J7Y01017BE86DH55i39F3j6F1J7Y01017BE86DH55i39F3jMF1J7Y01037BE86DH55k89F3kBF1J7Y01023",
  "55DHF30300003F355DH1E301006F3kUI55kQEkTGDH19601006F355DHkQEkTGkV9060003355DHF319301003",
  "55DHF31930100355DHF319301000+WWlv/dylWWvmiWuWZcXmWWiudWvmkXpWyZcXmWZuWX/dy/nyWWZZZWWii",
  "kuuznnxZZWWcWWWuuXmWbgrWeWciZWWWvmkXpWyZcXuciZWWWXmucWucWucWiWWWZXmiXmiXmiWWYbg40XWWem",
  "WWWWWWWeWaWmWmWWmYaWWYWWWaWWWeWWWmWaWXYWWWWWWWXXWWWaeWWWWWWWWWWWWeWemWWWmYaWWWWXWWXWae",
  "WWaWWWeWWWmWWXWWeWWWYWWYWmYWWWWeWWWaWWaXWaWWWWWW00mWaeWWWWWWYaWYWeWeWWeXYWWXWWWYWWWaWW",
  "WeXYWWnWWWWWWWemmWWYaWWWWWWWWWWWYaWaeWWWeXYWWWWWmWWmYaWWYWWWaWWWeWWWmYaYWaXWWXWeXWaWaa",
  "aWeYWWYWmYWeYemWH0gWaYmgXebWWenaWeWrYWmXYqeYbemagnWerYWmWXeWmgXebWqWWXXfWYabcegimqvXfW",
  "WYWWWgeWmXWWWaWXgaXWYbemagnWerYWngaXWWWWmeYWeYWeYWaWWWXWmaWmaWmaWWWWW00X+l/td//////xp/",
  "x/l/d//lzv//z///x///t///lzv/+y///////kkl//xp///////////xp/taW//dzv////+l/+/xp//x///t//",
  "/l//+/xpv/tz/dz/dz/t/ttp/lx+lx+lx/dxkbg5XmWeuWWWWWWaiWaWmWuWWmYcWWYWWWaWWWeWWWmYcWXZWW",
  "WWWWWnnmWWaiWWWWWWWWWWWaiWex/WWuYcWWWWXmWXWaiWWaWWWeWWWmWWXWaicWeYWuYWuYWeWeeiWmaXmaXm",
  "aWuanwrQ0000"]
@[expose] def ext_full_sort_ana_qs_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_bump_analyzed_mode_fid : armIsa.Hints := _decH #[
  "d739021D181O1P1Q1R11101C090902090502050909020909090N190205393502041N140E1G040G37050A29",
  "090907291212090909072602160N07052909020905060K3F0A0F050K0505090J0J160A390909072302130N",
  "0706290905070H090409090209050509090415290907190409090205090406090508190N52310107291209",
  "0A0Q29051502050A0F0H0G1606030A0725021I021E0E33030J0A2J0K524A0C07091A0A923909072512060A",
  "050N030E050I0F0F0F020F0N1F0F071F0F072F0F2F0F1F1J0F0K2J0J0K2F1F0F0K260A0616030G0J063707",
  "0E36060F0E06072606060I060N19090H07X30000000144BO0KRAD040001AEOO0GP4BADM1C8IQQCKR0A0000",
  "A4BO0KRADEOGPM1C8IQQC0A0002A4BADM1O0C8EOGPQCIQKR0A0000AEOO0GP4BADM1C8IQQCKR0A0006C4BAD",
  "M1O0C8EOGPQCXREXVGIQKR1HC01007M1O0AD4BQCKRXRE070002E4BADM1O0C8EOGPQCXREXVGIQKRY2HY4519",
  "E0101D4BADM1O0C8EOGPQCXREXVGIQKRY2H0D0000E4BADM1O0C8EOGPXREXVGY2HQCIQKRYF90E000AF4BADM",
  "1O0C8ZLJEOGPXREXVGY2HZCFQCIQKR15FYW0101G4BADM1O0C8ZLJEOGPXREXVGY2HZCFQCIQKRZM50GYW0006",
  "44BO0KRAD04000144BO0KRAD0400006M1O0AD4BQCKR19601016M1O0AD4BQCKR06000244BO0KRAD04000100",
  "0000114B01000054BKRO0ADbE81C5010164BKRO0ADbE8bOC06000374BKRO0ADbE8bOCcA9070005B4BKRO0A",
  "DbE8bOCcA9cGHbS1bR1cFF16Bm0110D4BKRO0ADbE8bOCcA9cGHbS1bR1cFFcTIcHG16Dm011754BKRO0ADbE8",
  "05000154BKRO0ADbE81H5010164BKRO0ADbE8e8H060004D4BKRO0ADbE8e8HeP5eC9eQIeB9eOEeJ6eN30Dq0",
  "004F4BKRO0ADbE8e8HeP5eC9eQIeB9eOEeJ6eN3fIFfKJ0Fuq0001D4BKRO0ADbE8e8HeP5eC9eQIeB9eOEeJ6",
  "eN30Dq000194BKRO0ADbE8e8HeP5eC9eQI09a000194BKRO0ADbE8e8HeP5eC9eQI090001CgBGgCJgA34BKRO",
  "0ADbE8e8HeP5eC9eQI3E6FC0300C4BKRO0ADbE8e8HeP5eC9eQIgCJgA3gEE0C000302031Y42301020810YWW",
  "uWbmWWeWiXWuWuYmucWmmWWWXiZX/yWWWWWXuXtZWyWnmYWWZWbmidumWWWWmiWWWWWWXmWmuZmWWWkWWZWXXm",
  "WmiXmXnWWWZtYWWWWWXgrgH0XWWeWYWWYeWWWWWWWWWWWWWeWaeWWaXWWWWeeYWmWWeWWWWWWWWWeWWmaWWWWW",
  "XWmaWWWWmWeWXaaYWaWYYWmeWYeeaYaXWaeWWWWWWWWaWmaaWWW00mWaWXWWXaWWmXWWYWYWWWWaaYaWfYWmYW",
  "WaaXWeWWaWeeWYabWYaWaeYWeYWWWmeYWYWWemaWWoYXWYWXXWeaWXaaYXYWmYaWWfXeWWmYWeYWWWW40meWWW",
  "WWWWaWWeWeWWeYWWWWmWWWXWWWWWWWWWuWpXWjWWmWWWWWWWaWWWaWWWWaWWWWWWWmWWeXmcWucWWXWWWmWWaW",
  "mWWWWWXpWeWWWWWWWW00X+l/t/z//yt/+/z//x/x////mtxt/Xx+/x//tty/l//t/ll/xtn/xt/tlx/lx/p+/l",
  "x/x//k/p/+xxz/x/yz/Zt/zttxzx+/xtt/jzl/k/x/lx////NXmWeWYWWZeWXWYWWaWaWWWWleaeW+aXWaWWee",
  "ZWmWWeWmmWaekWaeWemaWmaWiXWmaWaWWnWiWXaaYWaWZYWyeWYeeaYaXWaeeWoYmWnWaWmaWWWW8001A34520",
  "6DEFG"]
@[expose] def ext_full_bump_analyzed_mode_fid : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_div", [i64, i64], [i64]), 0),
   (("f64u_add", [i64, i64], [i64]), 0),
   (("full_rescale_m6", [i64], []), 64),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("full_sort_ana_qs_m6", [i64, i64], []), 0)]

@[expose] def hints : List armIsa.Hints := [hint_full_rescale_m6, hint_full_rescale,
    hint_full_bump_var, hint_full_bump_decay, hint_full_queue_renumber, hint_full_queue_mtf,
    hint_full_ana_sift_m6, hint_full_sort_ana_qs_m6, hint_full_bump_analyzed_mode_fid]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_div", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_add", [i64, i64], [i64]), 0),
   (("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Bump
