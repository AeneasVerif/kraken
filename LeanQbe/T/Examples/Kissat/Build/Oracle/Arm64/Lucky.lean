module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Lucky

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X23)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X27)),
  (XRegOrSp.reg (XReg.X28)), (XRegOrSp.reg (XReg.X29)), (XRegOrSp.reg (XReg.X6)),
  (XRegOrSp.reg (XReg.X5))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X14))),
  (.gpr (XRegOrSp.reg (XReg.X15))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X28))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X29))), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X19))), (.slot 0 .w64),
  (.slot 1 .w64), (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.flag LeanQbe.T.Arm64.ArmCond.gt),
  (.flag LeanQbe.T.Arm64.ArmCond.ge)]

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

@[expose] def hint_full_lucky_ord_fid : armIsa.Hints := _decH #[
  "bE20111213141506170809070A0909070B0C07160C6B4B4B1B2D070C1E372D0E170F0G0E2H0H0I0B0A070E",
  "3B1A070E0I0I0C070J0J0C070C17077B070C1E3B0E06060C1B0B1D0D0E2K0K1D0D0E2K0K1D0D0E2K0D1B0B",
  "0E2D070B0C1E4B0B0E2D070E0C3B0B0E2B4B0B0E2B4B0B0E2B4B0B0E2B170B0C1E3B0B0E2B170E2E060C17",
  "0771070C1E310E0641010E240A0E271B0E16010A0E211C4B0A0E2B01170E060C3101210121012107010C1E",
  "31070EXD0010001006G581A2E460C31960100260A2020004781C3U9G5E460A21B701007G581U9A2E460C31",
  "B701007G581U9A2E460C31B701007G581U9A2E460C317701054U960C3A2040000981C3U9Y6GG5E460Y5FA2",
  "2D790201981C3U9Y6GG5E460Y5FA22D790201AY8D81Y6GG5E460C3U9Y5FA217A0105DC381YBHU9YUJY6GG5",
  "E460Y5FYQIA2YPI0DaW0000DYPI81C3YBHU9YUJY6GG5E460Y5FYQIA21BD1100DYPI81C3YBHU9YUJY6GG5E4",
  "60Y5FYQIA21BD1100DYPI81C3YBHU9YUJY6GG5E460Y5FYQIA21BD1105AC381A2YUJY6GG5E460U9Y5F0A000",
  "0CC381YBHU9YUJY6GG5E460Y5FYQIA217C0100CC381YBHU9YUJY6GG5E460Y5FYQIA217C0100CC381YBHU9Y",
  "UJY6GG5E460Y5FYQIA217C0103EC381YBHU9YUJY6GG5E460Y5FYQIA2ZP7ZRB0E0001EC381YBHU9YUJY6GG5",
  "E460Y5FYQIA2ZP7ZRB0E0001EC381YBHU9YUJY6GG5E460Y5FYQIA2ZP7ZRB0E0001DC381YBHU9YUJY6GG5E4",
  "60Y5FYQIA2ZP70D0003DC381YBHU9YUJY6GG5E460Y5FYQIA2b070D0002AC381A2YUJY6GG5E460U9Y5F17A0",
  "100AC381A2YUJY6GG5E460U9Y5F17A0100AC381A2YUJY6GG5E460U9Y5F17A0102BC381A2YUJY6GG5E460U9",
  "Y5FbD71BB0101BC381A2YUJY6GG5E460U9Y5FbD71BB0101BC381A2YUJY6GG5E460U9Y5FbD71BB0101BC381",
  "A2YUJY6GG5E460U9Y5FbD71BB0103BC381A2YUJY6GG5E460U9Y5FcQ71BB01034A2C360U90400004U960C3A",
  "211401004U960C3A211401004U960C3A211401053A260C317301004A2C360U92B7402015A2C360U9e0B175",
  "01043A260C3217302013A260C311301034A260C3eT71140103260A21720100260A21720100260A21720101",
  "020010iWWuuuuWWZWcWiWWWiWiZWWuWYrgmWWWZWuWWudZWyiZnmiWWcXuWWuacXXmeiYWWWcWWrgqWWWWWbmW",
  "WWWxWWjdpv+WWWWXXgL0eWnWWWWWaeWfWeXaemWoXWWeXYWWWWXYaWeXYWYWWeWXWWaWYeWmXYWYWWmWaWXWWW",
  "YWemWWWWeWWemWWWWeWaeWWWWWXWWeeeW00aWemWWWWoaWamaWoaeWfWmYaWnWWWWanYWaWnWXWWaWWmWYWeaW",
  "eWnWXWWeWYWWmXYnWaeWWWXWmeaeXaWmaWYaWWWWWanWaaaW00aWeeeeeWWXWYWaWWWaWaXWWeWmWWYWWWXWeW",
  "meZXWiaXmmaWWYWuWmeWYWWmWaWmWWYWaWWWmWaWWWmWeWWfWYaXWmgWWeWWWW00Zp/kl///+hp/s/t+xtd/j+",
  "/xp+y////ozv/t+y/z//t/+//x/lp/l+y/z//l/x/+/yuy/td///z+lZplzp+/m/xp/////o+fpnt/ViWnmWWW",
  "XqiWfWeXaeuWoXWaiXZWWWWjYcWeXZWYWWeWXWWaWmiWmXZWYWWmWaWXWZdZWeuWWWYXmyimYiXWlWaiWWWWWj",
  "XsikeW00000"]
@[expose] def ext_full_lucky_ord_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_lucky_scan : armIsa.Hints := _decH #[
  "a04L2M1N1O101P0QC6110121010E23160103030A030A03010R0R0103000E30130101000C00070C0B20060I",
  "040D090K00074716070607070A2607072A37070000200020001A0A020C0A000A3A061A0A02000A00000701",
  "0E3111070000030C030B0C032B060I040D090K0B4316030603030A2603032A37070707270020001A0A0S0E",
  "C001000100B4THUFO5VBMDN8LJP6X0KQ9X11SB0101C4THUFO5VBMDN8LJP6X0KQ9X1X2S0C0005D4TXORHUFO",
  "5VBMDN8LJP6X0KQ9X1X2S0D2003L4TXORHUFO5VBMDN8LJP6X0KQ9X1X2SYI9YJKY41YK0YHDY23YG4YFI0LfW",
  "W2002K4TXORHUFO5VBMDN8LJP6X0KQ9X1X2SYI9YJKY41YK0YHDY23YG40KfWW2001G4TXORHUFO5VBMDN8LJP",
  "6X0KQ9X1X2SYI9YJKY410GXWW2004C4THUFO5VBMDN8LJP6X0KQ9X1X2S10C0108C4THUFO5VBMDN8LJP6X0KQ",
  "9X1X2S0C0003L4THUFO5VBMDN8LJP6X0KQ9X1X2SaM1b79b8KaP0b9Bb6DaN7b54b4I0LfaW0002K4THUFO5VB",
  "MDN8LJP6X0KQ9X1X2SaM1b79b8KaP0b9Bb6DaN7b540KfaW0001G4THUFO5VBMDN8LJP6X0KQ9X1X2SaM1b79b",
  "8KaP00GXaW0007040200311231402051N2301V2241B2210aD22400XnmYocXmWWsuWcWWYkWWWWWWWWWWWuuX",
  "fZWuWWhiWXmWXdWWWWbmiX//or90YWWWWWWWWWWWWaXYWWWWWWWWWWWWWWWWaWWWWWWWWYWnWWWWWWWWWWXWma",
  "WWWWWW00XWWWbWWWWWWmWYWnWWWmemWWmaWXfeXbYmWWWWWeWXWemWWaYaWWeWemeYWYWWWW00mWWWWWWWWYeW",
  "YWYWWWWWWWWWWWWWeWWWWWWWWXaWWmWmWWWWWWmbWWWWW00y///n/////+/xx+z//+/k//+dt/yilzru//////",
  "lzz/k///txt//Z/k/lx/x////VZWWWkWWWWWXWaaXYWWXWnWWXueWZpmYgdWWWWWWmYYWnWWWeaeWWyWnWmaWa",
  "WWWW0002B367589A2BCD"]
@[expose] def ext_full_lucky_scan : List (SigEntry × Nat) :=
  [(("full_lucky_ord_fid", [i64], [i64]), 0),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_analyze_core_m6", [i64], [i64]), 848),
   (("m6_hdr_dr_update", [i64], []), 48),
   (("full_backtrack", [i64, i64], []), 96)]

@[expose] def hint_full_lucky_polar_m7 : armIsa.Hints := _decH #[
  "a8200H151T1K121R130X13X20707020X2213707020X216021E2706020E0702021G07080I0I013D1A1A0C0D",
  "07080I67070E110X30X41A0B040704220E2J0B0J0F040F2C6E2116020103030A020B0B0B03030303033B0B",
  "040804080B0E4D160304040E03140704160407032E130301010101013B0B030803080B0E43160104040E01",
  "140F041A040F012E220000K0010001007604SFU957HHRBT2JF70200A604SFU957HHRBTKX1J3DK3JF9Aa030",
  "1DKX1LJMF604SFU957HHRBTJ3DKN90D1002DLJMF604SFU957HHRBTKX1J3DKN912Dm0113DDKJ3LJMFN9957H",
  "60KX14SFUBTHR12De0100ELJMF604SFU957HHRBTKX1J3DKN9XA20Em0002C604SFU957HHRBTXMGKX1J3DKN9",
  "2JFCe0205E604SFU957HHRBTXMGKX1J3DKN9MFLJ2B4Ee0200GLJMF604SFU957HHRBTXMGKX1J3DKN9Y8IXVD",
  "3B42GXXW0300HLJMF604SFU957HHRBTXMGKX1J3DKN9Y8IXVDYB22B4HXXW02057604SFU957HHRBT37F27030",
  "02ZE7ZFF020001AZE7ZFF60ZG24SFU957HHRBT0A00028604SFU957HHRBTZG227F80202AZFF60ZG2957HHR4",
  "SFUBTZO117A0102BZFF60ZG2957HHR4SFUBTZO1aEB273B0202BZFF60ZG2957HHR4SFUBTZO1aEB273B0205A",
  "b874SFU6095BTZG27HHRbPB2F1A0202Ab874SFU6095BTZG27HHRbPB2F1A020402061F2304aJ22E0XM22F00",
  "nWWsWWWyWWWnWWsWWWyWWWbmWmWWWXWedWWYbuWWWZWYXxWWWgr90YWWWWWWemWWYWWWWWWemWWWWWWqWWXWWe",
  "YWYYemWeWWmeWWWWXeWW00XWWYXWYaeWWXWWYXWYaeWWXWeWYXWWmWbXWXXaeWaWWeaamWeWaWW00YWYWigWWW",
  "WWYWYWigWWWmWWWWWWWWZWuWWvWWmXWWavWWWWW00//zztuz/xpl//zztuz/xpl//z/l/xz/+lZnz/yztl/p+l",
  "ltsXxd/t//VYYedYWaimWWYYedYWaimWWYWmWaYWXmykYWZYemWiXmmef+auWeWW000143675"]
@[expose] def ext_full_lucky_polar_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_lucky_late_m7 : armIsa.Hints := _decH #[
  "YF2006100610120X21A0A461A2A2A1L1X11R1P1QC00630160002020A020A020002000207010E3117020201",
  "0C01030C0123060I0B040D09030K4116010601010A2601012A37070707270220001A0A0S000X2B00100010",
  "114T01000114T01000414T101010114T101010264TX9QX7PX1LX3X1X5R1S6010174TX9QX7PX1LX3X1X5RXO",
  "S07000474TX9QX7PX1LX3X1X5RXOS070003G4TX9QX7PX1LX3X1X5RXOSY70Z1DZ29YJ2Z33Z04YH7YVBYUI0G",
  "fa0002F4TX9QX7PX1LX3X1X5RXOSY70Z1DZ29YJ2Z33Z04YH7YVB0Ffa0001B4TX9QX7PX1LX3X1X5RXOSY70Z",
  "1DZ29YJ20BXa0001020310XWWWWWWZZWbaiZWWXjmWcWWayWWWWsW//wrWWWWYemWgWH0YWWWWWWWWWWWWeYaW",
  "WWWWWWWWWaYWWWWWWWWefWWaYWa00XWWWgWWWWWXWWaXYWWWmemWXWXYXWYWWWWWaaamWYnWY40XWWWWWWWWWa",
  "mWYWYWWWWWWYWWWWWWWWWWWWWWW00lyl//Z/////z/ttzx//+/k//ylzxz/x////ltts//uz/xNZmWWyWWWWWY",
  "WeeYaWWXWnWWZmYaYWaWWWWmeefWWdYWa80007367589A"]
@[expose] def ext_full_lucky_late_m7 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_lucky_polar_m7", [i64], [i64]), 48),
   (("full_lucky_scan", [i64, .bool, .bool], [i64]), 960)]

@[expose] def hints : List armIsa.Hints := [hint_full_lucky_ord_fid, hint_full_lucky_scan,
    hint_full_lucky_polar_m7, hint_full_lucky_late_m7]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_analyze_core_m6", [i64], [i64]), 848),
   (("m6_hdr_dr_update", [i64], []), 48),
   (("full_backtrack", [i64, i64], []), 96)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Lucky
