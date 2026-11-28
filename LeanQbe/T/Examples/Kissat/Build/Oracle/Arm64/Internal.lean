module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Internal

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)),
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X4)), (XRegOrSp.reg (XReg.X0)),
  (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X15))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.gpr (XRegOrSp.reg (XReg.X14))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X15))), (.slot 0 .w64),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.flag LeanQbe.T.Arm64.ArmCond.eq)]

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

@[expose] def hint_full_zero_tables1 : armIsa.Hints := _decH #[
  "Y120001112131415161708094A0A0A5A2ABA2ABA2ABA2B0A091C4A0A0A5A2B0C141B0812110108091B0B74",
  "0B091C340C111B0B740B091D340D141E0E7B0E091D3B0DH0000000014E01000094E70L7J6H5F4D3B2911B9",
  "010094E70L7J6H5F4D3B2911B9010094E70L7J6H5F4D3B2911B9010514E01000114E01000034EZJ1ZG2143",
  "010034EZJ1ZG2143010034EZJ1ZG2143010514E01000024EaB1142010024EaB1142010024EaB114201031b",
  "141B101001b141B101001b141B101000cWWrgqYWuWYrgmeZWWgrgWWgWqXftWrWWgjxrfftkrbczwqqxmgmXg",
  "r90YWemWWWWeXYWWWWXWaeWWWWaWaWmWWWWaeWWWWWWWWWWWWWWWWWWWeWW00XWaeWWWWaWnWWWWWmYaWWWWoW",
  "YWeWWWWYaWWWWWWWWWWWWWWWWWWXaWW00YWaWWWmWeWmWWYWXWYWWWeWWWWWWZaWWYWWvWWWZaWWWimWWXoWWW",
  "WW00y/td////p+y////+lxp///+h/x/d////xp//////////////////yt//VZWeuWWWWiXZWWWWXmaiWWWXqW",
  "aWuWWWWaiWWWWWWWWWWWWWWWWWWZeWW00000"]
@[expose] def ext_full_zero_tables1 : List (SigEntry × Nat) := []

@[expose] def hint_full_zero_tables2 : armIsa.Hints := _decH #[
  "Q2F1112131516171A101G1H1I1J1K1B141L1M0809X8E0N091CKE0C403X446FX2B030000IX446FX2BX0KUJS",
  "IQHOGI7X8MX6LM0KAG6E5C3A2811EI0100IX446FX2BX0KUJSIQHOGI7X8MX6LM0KAG6E5C3A2811EI0100IX4",
  "46FX2BX0KUJSIQHOGI7X8MX6LM0KAG6E5C3A2811EI01000XiXgrhgsrgWWrgrrhgrrgrjgwreWrgrgrgL0mWW",
  "WWWWWemWWWWWWWWWWWWWWWaWWWWWW00eWWWWWWWaeWWWWWWWWWWWWWWWoWWWWWW00aWWWWWWWWWWWWWWWWWWWW",
  "WW00d/d///////td//////////////+h//////VuWWWWWWWeuWWWWWWWWWWWWWWXqWWWWWW000040123"]
@[expose] def ext_full_zero_tables2 : List (SigEntry × Nat) := []

@[expose] def hint_full_fixed_bytes : armIsa.Hints := _decH #[
  "N14010102020B0303030D0B01010201030104010E010B01000000000YqWcA0l/+/VXW00000"]
@[expose] def ext_full_fixed_bytes : List (SigEntry × Nat) := []

@[expose] def hint_full_init_ptrs : armIsa.Hints := _decH #[
  "XI360303020205010101040D050B1B1B131313131312121212121212121212121212121211160111111111",
  "111111141B041B14000banaofaoaofaofaofaofaoeW000000aWWWWWmWWWWWWWWWWWWWWcA0/////////////",
  "/////////z/VYW00000"]
@[expose] def ext_full_init_ptrs : List (SigEntry × Nat) := []

@[expose] def hint_full_init_hdr : armIsa.Hints := _decH #[
  "364Y0B0B000XgrgrgrgrgrYrgrgrgrgrgrgrgrgrgrgrgrgr500000eWWWWWWWWWWWWWWWWWWWWWWWWW00d///",
  "/////////////////////////////////V00000"]
@[expose] def ext_full_init_hdr : List (SigEntry × Nat) := []

@[expose] def hint_full_calc_max_v : armIsa.Hints := _decH #[
  "XE4E0901030C0E0E03010E0E0101090E1E0305050606010707070D01050506050705030503050105030404",
  "0D0E0D0E1035B42641E3010102045000a40Y20XYqWcgWyn00Xf//+//x/vRsWWXWWaWc4YW0000"]
@[expose] def ext_full_calc_max_v : List (SigEntry × Nat) := []

@[expose] def hint_full_calc_ext_cap_m5 : armIsa.Hints := _decH #[
  "61B090B0B0D0B00000000000YRX40000"]
@[expose] def ext_full_calc_ext_cap_m5 : List (SigEntry × Nat) := []

@[expose] def hint_full_calc_scr_cap_m5 : armIsa.Hints := _decH #[
  "81D090B0E0E090E0E1001E001000000010G0Zw1bU0000"]
@[expose] def ext_full_calc_scr_cap_m5 : List (SigEntry × Nat) := []

@[expose] def hint_full_init_arenas : armIsa.Hints := _decH #[
  "YG5G0G1H01020203030903020205050101090A000606020207010101040D070B1B1B161616161612121212",
  "121212121212121212121211100111111111111111141B041B142B041B04141B041H04131A15000fanYenf",
  "afaofanaofaofaofaofaoWWWWW900000aeYaWXWWWWWaWWWWWWWWWWWWWWXomoW00X////////////////////",
  "////////l/v+/VmWcXW0aa0000"]
@[expose] def ext_full_init_arenas : List (SigEntry × Nat) := []

@[expose] def hint_full_init_state_m5 : armIsa.Hints := _decH #[
  "aL6K140B030305050E0606060D0E0303050306030B030B030E030D0E0B030D0904050C0E0E01040E0E0404",
  "090L1L04050506060E0707070D0E050506050705040504050E05040C0L0D0L04030305050E0606060D0E03",
  "0305030603040304030E03010904030E0905050D0509060E090E0E160607060B0B0D050E03311F13151617",
  "1A101G1H1I1J1N1B1K11121L1M0809X8E04091CKE0C7001E0010366MAK8OX6B7FX731L6010296MAKYKL8OZ",
  "C1ZE4ZF3ZL5X6B1E901013bA2aCFb81030000IbA2aCFb81b6Kb4Bb2Nb0JaUIaO0bEMbCLaSHaQGaMAaK7aI6",
  "aG5aE31EI0100IbA2aCFb81b6Kb4Bb2Nb0JaUIaO0bEMbCLaSHaQGaMAaK7aI6aG5aE31EI0100IbA2aCFb81b",
  "6Kb4Bb2Nb0JaUIaO0bEMbCLaSHaQGaMAaK7aI6aG5aE31EI0101063040360270XiXgrhgsrgWWrgrrhgrrgrj",
  "gwreWrgrgrgrWrWWWWWWWWWWWWWWWWWWWWWWWWWWG0mWWWWWWWemWWWWWWWWWWWWWWWaWWWWWWWWWWWWWWWWWW",
  "WWWWWWWWWaaWWWWWW20eWWWWWWWaeWWWWWWWWWWWWWWWoWWWWWWWWWWWWWWWWWWWWWWWWWWWYYmmWWWW00aWWW",
  "WWWWWWWWWWWWWWWWWWWWWWXrWeWXrWXomgqWcgWynWWbeWiq00X//d///////td//////////////+h///////",
  "//X/zaxp//t/ul/+//x/vwkl/z//VuWWWWWWWeuWWWWWWWWWWWWWWXqWWWWWWWWW+WYxaiWWeWdmWXWWaWcbnm",
  "WYWW0YWWWWWWWW00140123"]
@[expose] def ext_full_init_state_m5 : List (SigEntry × Nat) :=
  [(("kissat_parse_header", [i64, i64, i64], [.bool]), 0),
   (("full_init_arenas", [i64, i64, i64, i64], []), 0),
   (("full_init_hdr", [i64, i64, i64, i64], []), 0),
   (("full_zero_tables1", [i64], []), 0)]

@[expose] def hint_full_init_state : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_init_state : List (SigEntry × Nat) :=
  [(("full_init_state_m5", [i64, i64, i64, i64, i64], [.bool]), 48)]

@[expose] def hint_full_m6_mem_init : armIsa.Hints := _decH #[
  "55D030C0K011001K0010102007000e009040//5Q00010"]
@[expose] def ext_full_m6_mem_init : List (SigEntry × Nat) :=
  [(("full_init_state_m5", [i64, i64, i64, i64, i64], [.bool]), 48),
   (("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_full_set_inactive : armIsa.Hints := _decH #[
  "ZO410B0P121523180605050Q1308030303041315171214020C040C160Q160Q160Q040P06060P2606220P24",
  "140P22221314150809050C260Q062J080J0C24090306151B0B01090C24082708110134040209220P584709",
  "040H1G160A060P0D2E082I06010B0P6E0E0P22030C21010C250D0B0E02395600010B0PD0000000164E819B",
  "5BC26406XC00344E815B9B04C00094E815B9BX62X03X84X25X4709YS00484E815B9BX62X03X84X2508YS00",
  "274E815B9BX62X03X8407YS00200000063Z2JZ0J4E0320045Z2JZ0J4EZ96Z831B521107Z2JZ0J4EZ96Z83Z",
  "O7ZB51B721184aLHZ2JZ0JaK416441108aLHZ2JZ0JaK4aNGaI7aQAb4I401B684482AbC6aLHZ2JZ0JaK4aNG",
  "aI7aQAb90b4I3BE2A93200XuWZsWcXmicWccWgWWkWjuudWccWgWuWZWuWYraiYcWepWWeWnWbgmWaWbr10maW",
  "WWWWWWWWWYWWWWWWWWWWXYWaYamWWWWWWWWWYWWWWWWWXXWmW00aWWmWeYXWaWmqWaWWXWYYWWmmqWaWnWYXYe",
  "WWXWWmWWaXWYafWWWWmmWW80uWXoWYWmaYWYYWWWWcWaueZeYYWWWWWXWeWWWWaWYWWXWeWWWamWWWWYWW00X/",
  "//p/+u/lxz/p++d/t//z/xx/+++d/t+aZhyfl//z/+///mz/utX///++/l/FiWXdWmaYWiXXuWeWWYWaaWXXXu",
  "WeXxyqZsmWWYWXWWWlYWde+WWWXXWmWG0000"]
@[expose] def ext_full_set_inactive : List (SigEntry × Nat) := []

@[expose] def hint_full_init_fresh_var : armIsa.Hints := _decH #[
  "Y4321516171A10131G1H1I1J1411141N0B010N1N0N1N0N1101140104E414110D7408110913021408140901",
  "043109050706140402090C21081A08120231010309230P585B0B404X4B5B4ENH04300114E01000854EZ57X",
  "4B5BZ45145811074EZ57X4B5BZ45ZIAZ661478116R23073231602328R227012271822720aWZmZkcXuXZWaW",
  "kWnaegconbrrgrgXYaegrgrgL0mWWWWWWWWWWWWWYWWWWWWWWWWWWWWWWWWW00eWmmWaegWaWYaXXWWWaWWWWW",
  "WWWWWWWWWW00XmXcYWwWXWWWcWWWWWYWWWWWWWWWvpaWWWWW00Z////l++//tlZ/t/xtzz///t////////////",
  "///VmXXWWemyWeWaeYYWWWeWWWWWWWWWWWWWWW00030"]
@[expose] def ext_full_init_fresh_var : List (SigEntry × Nat) := []

@[expose] def hint_full_update_classify_fid : armIsa.Hints := _decH #[
  "J2B1404090B04091B0B080B0B110B0B0404080E30000000014E141010224EE41B20100050Y00aWYXX0000l",
  "t/xzzVeWaYY00000"]
@[expose] def ext_full_update_classify_fid : List (SigEntry × Nat) := []

@[expose] def hints : List armIsa.Hints := [hint_full_zero_tables1, hint_full_zero_tables2,
    hint_full_fixed_bytes, hint_full_init_ptrs, hint_full_init_hdr, hint_full_calc_max_v,
    hint_full_calc_ext_cap_m5, hint_full_calc_scr_cap_m5, hint_full_init_arenas,
    hint_full_init_state_m5, hint_full_init_state, hint_full_m6_mem_init,
    hint_full_set_inactive, hint_full_init_fresh_var, hint_full_update_classify_fid]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("kissat_parse_header", [i64, i64, i64], [.bool]), 0),
   (("m6_hdr_init", [i64], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Internal
