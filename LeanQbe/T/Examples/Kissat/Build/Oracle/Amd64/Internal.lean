module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Internal

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r13, Reg64.rdi, Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.rax, Reg64.rcx, Reg64.rdx,
  Reg64.r14, Reg64.r15, Reg64.rsi, Reg64.r8, Reg64.r9]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.r12), (.gpr Reg64.rdx), (.gpr Reg64.rsi), (.gpr Reg64.r8), (.gpr Reg64.rcx),
  (.gpr Reg64.r9), (.gpr Reg64.rbx), (.gpr Reg64.rbp), (.flag CondCode.nz), (.flag CondCode.nc),
  (.gpr Reg64.rdi), (.gpr Reg64.rax), (.flag CondCode.c), (.gpr Reg64.r13), (.gpr Reg64.r14),
  (.gpr Reg64.r15), (.slot 6 .w64), (.slot 3 .w64), (.slot 2 .w64), (.slot 1 .w64),
  (.slot 0 .w64), (.slot 5 .w64), (.slot 4 .w64), (.flag CondCode.z)]

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

@[expose] def hint_full_zero_tables1 : x64Isa.Hints := _decH #[
  "XK2000111213141516170809CA2ABA2ABA2ABA2B0A091CCA2B0C1B281412020809AB01091C3B0C14AB0109",
  "1C3B0C14AB01091C3B0CH0000000014D01000094D70L7J6H5F4D3B2911B9010094D70L7J6H5F4D3B2911B9",
  "010094D70L7J6H5F4D3B2911B9010514D01000114D01000034DZJ2ZG41B3010034DZJ2ZG41B3010034DZJ2",
  "ZG41B3010514D01000024DaB41B2010024DaB41B2010024DaB41B201031b141B101001b141B101001b141B",
  "10101020010cWWrgroWuWYrgseZWWgrguWgXqXftkrWWgjxrfftkrbczwqqxtgmXgr90YWemWWWWeXYWWWWXWa",
  "eWWWWaWaWmWWWWaeWWWWWWWWWWWWWWWWWWWeWW00XWaeWWWWaWnWWWWWmYaWWWWoWYWeWWWWYaWWWWWWWWWWWW",
  "WWWWWWXaWW00YWaWWWmWeWmWWYWXWYWWWeWWWWWWZaWWYWWvWWWZaWWWimWWXoWWWWW00y/td////p+y////+l",
  "xp///+h/x/d////xp//////////////////yt//VZWeuWWWWiXZWWWWXmaiWWWXqWaWuWWWWaiWWWWWWWWWWWW",
  "WWWWWWZeWW000042340"]
@[expose] def ext_full_zero_tables1 : List (SigEntry × Nat) := []

@[expose] def hint_full_zero_tables2 : x64Isa.Hints := _decH #[
  "Q2B1213151617101D1E1F14111B1B14111B1A0809X8B0A091CKB0C403X416GX24030000JX416GX24X0AX0H",
  "UISJQKOFI0X8LX6MMEKDG7E6C5A3821BJ0100IX416GX24X0HUISJQKOFI0X8LX6MMEKDG7E6C5A3821BI0100",
  "JX416GX24X0HUISJQKOFI0X8AX8LX6MMEKDG7E6C5A3821BJ010QP23651232512306123171233534351345Q",
  "22141221552210122111221212213M2214122155221012211122121221312216T221412215522101221112",
  "21212213722560XiXgrhgsrgWWrgrrhgrrgrjgwreWrgrgrgL0mWWWWWWWemWWWWWWWWWWWWWWWaWWWWWW00eW",
  "WWWWWWaeWWWWWWWWWWWWWWWoWWWWWW00aWWWWWWWWWWWWWWWWWWWWWW00d/d///////td//////////////+h/",
  "/////VuWWWWWWWeuWWWWWWWWWWWWWWXqWWWWWW00076234089"]
@[expose] def ext_full_zero_tables2 : List (SigEntry × Nat) := []

@[expose] def hint_full_fixed_bytes : x64Isa.Hints := _decH #[
  "N14010102020B0303030C0B01010201030104010A010B0B000000000YqWcA0l/+/VXW00000"]
@[expose] def ext_full_fixed_bytes : List (SigEntry × Nat) := []

@[expose] def hint_full_init_ptrs : x64Isa.Hints := _decH #[
  "XI3203030404050B0B0B010C0605151513131313131414141414141414141414141414141B120B1B1B1B1B",
  "1B1B1B111B011B11010230A0banaofaoaofaofaofaofaoeW000000aWWWWWmWWWWWWWWWWWWWWcA0////////",
  "//////////////z/VYW000112"]
@[expose] def ext_full_init_ptrs : List (SigEntry × Nat) := []

@[expose] def hint_full_init_hdr : x64Isa.Hints := _decH #[
  "361Y0202000XgrgrgrgrgrYrgrgrgrgrgrgrgrgrgrgrgrgr500000eWWWWWWWWWWWWWWWWWWWWWWWWW00d///",
  "/////////////////////////////////V00000"]
@[expose] def ext_full_init_hdr : List (SigEntry × Nat) := []

@[expose] def hint_full_calc_max_v : x64Isa.Hints := _decH #[
  "XE4B0904030C0B0B03040B0B0404090B1B0305050406040101010C07050506050105030504040704030101",
  "0C0B0C0B103524A611B30101Q2307000a40Y20XYqWcgWqn00Xf//+//x/vRsWWXWWaWc4001223"]
@[expose] def ext_full_calc_max_v : List (SigEntry × Nat) := []

@[expose] def hint_full_calc_ext_cap_m5 : x64Isa.Hints := _decH #[
  "61B090B0B0C0B00000000000YRX40000"]
@[expose] def ext_full_calc_ext_cap_m5 : List (SigEntry × Nat) := []

@[expose] def hint_full_calc_scr_cap_m5 : x64Isa.Hints := _decH #[
  "81C0B040A0A090B0B1001B00100000001000ZxPa60000"]
@[expose] def ext_full_calc_scr_cap_m5 : List (SigEntry × Nat) := []

@[expose] def hint_full_init_arenas : x64Isa.Hints := _decH #[
  "YG5B0E1F040B0B030309030B0B0606040409070005050404020B0B0B010C0D021212151515151514141414",
  "14141414141414141414141B100B1B1B1B1B1B1B1B111B011B112B011B01111B011F0113171601N230A0fa",
  "nYenfafaofanaofaofaofaofaoWWWWW900000aeYaWXWWWWWaWWWWWWWWWWWWWWXomoW00X///////////////",
  "/////////////l/v+/VmWcXW00016234089"]
@[expose] def ext_full_init_arenas : List (SigEntry × Nat) := []

@[expose] def hint_full_init_state_m5 : x64Isa.Hints := _decH #[
  "aL66120105050B070B0D0D0D0C0B050507050D05010501050B050C0B01050C0902070C0B0B04020B0B0202",
  "090717020B0D0B0E0B0F0F0F0C0B0D0D0E0D0F0D020D020D0B0B020C070C070205050B0D0B0E0E0E0C0B05",
  "050D050E05020502050B05040902000B090D0D0C0D050E0B090B0B15050E0501010C0D0B05341B15121116",
  "17101D1E1F14131B1B14131B1A0809X8B0A091CKB0C7001B0010376A6LA68KX6170X751770102A6A6LA6YK",
  "78KZC4ZE2ZF0ZLDX611BA01013bA3aCGb84030000JbA3aCGb84b6Ab6Hb4Ib2Jb0KaUFaO0bELbCMaSEaQDaM",
  "7aK6aI1aG2aE51BJ0100IbA3aCGb84b6Hb4Ib2Jb0KaUFaO0bELbCMaSEaQDaM7aK6aI1aG2aE51BI0100JbA3",
  "aCGb84b6Hb4Ib2Jb0KaUFaO0bEAbELbCMaSEaQDaM7aK6aI1aG2aE51BJ010T0A30B35704605101722215aE2",
  "215N236512325123061231B1233534351345Q22141221552210122111221212213M2214122155221012211",
  "122121221312216T22141221552210122111221212213722560XiXgrhgsrgWWrgrrhgrrgrjgwreWrgrgrgr",
  "WrWWWWWWWWWWWWWWWWWWWWWWWWWWG0mWWWWWWWemWWWWWWWWWWWWWWWaWWWWWWWWWWWWWWWWWWWWWWWWWWWaaW",
  "WWWWW20eWWWWWWWaeWWWWWWWWWWWWWWWoWWWWWWWWWWWWWWWWWWWWWWWWWWWYYmmWWWW00aWWWWWWWWWWWWWWW",
  "WWWWWWWWWWXrWWWXrWXomgqWcgWqnWWbeWiq00X//d///////td//////////////+h/////////X/zyxp//t/",
  "ul/+//x/vwkl/z//VuWWWWWWWeuWWWWWWWWWWWWWWXqWWWWWWWWW+WYZaiWWeWdmWXWWaWcbnmWYWW00076234",
  "089"]
@[expose] def ext_full_init_state_m5 : List (SigEntry × Nat) :=
  [(("kissat_parse_header", [i64, i64, i64], [.bool]), 0),
   (("full_init_arenas", [i64, i64, i64, i64], []), 56),
   (("full_init_hdr", [i64, i64, i64, i64], []), 0),
   (("full_zero_tables1", [i64], []), 40)]

@[expose] def hint_full_init_state : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_init_state : List (SigEntry × Nat) :=
  [(("full_init_state_m5", [i64, i64, i64, i64, i64], [.bool]), 168)]

@[expose] def hint_full_m6_mem_init : x64Isa.Hints := _decH #[
  "55C0B0C0604100160010102027000e009040//5Q00012"]
@[expose] def ext_full_m6_mem_init : List (SigEntry × Nat) :=
  [(("full_init_state_m5", [i64, i64, i64, i64, i64], [.bool]), 168),
   (("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_full_set_inactive : x64Isa.Hints := _decH #[
  "ZG4B02091415483N1308030303011617151114010C040C2N2N2N0409030309230321092414092126111417",
  "0809030C3N052408040C24090607131B0B190C382008110101240419390248142009010F1E170507090C38",
  "24070204096B0B092A030C26060C220C040B0A392B2B0A0204091BD0000000164A8B9252C46106X800344A",
  "8B529204400094A8B5292X61X06X84X27X4509YK00484A8B5292X61X06X84X2708YK00274A8B5292X61X06",
  "X8407YK00200000065Z21Z2JZ02Z0J4A05C0047Z21Z2JZ04Z0J4AZ97Z861B7C1007Z2JZ0J4AZ97Z86ZB3ZO",
  "01B721085aLFZ2JZ0BZ0JaK1175C1008aLFZ2JZ0JaK1aNEaI0aQ5b4K4D24784402AbC7aLFZ2JZ0JaK1aNEa",
  "I0aQ5b9Db4K34BAA830AaD231632316D22519226132271X322A1E2251G2306XM2261022510XmWZcWcXmicW",
  "ckWgWWiWjnvcWckYgWuWZXuWYraiYcWepWWuXpWbgmWakdr10maWWWWWWWWWWYWWWWWWWWWWXYWaYamWWWWWWW",
  "WWYWWWWWWWXXWmW00aWWmWeYXWaWmqWaWWXWYYWWmmqWaWnWYXYeWWXWWmWWaXWYafWWWWmmWW80uWXoWYWmaY",
  "WYYWWWWcWaueZeYYWWWWWXWeWWWWaWYWWXWeWWWamWWWWYWW00X///p/+u/lxz/p++d/t//z/xx/+++d/t+aZh",
  "yfl//z/+///mz/vtX///++/l/FiWXdWmaYWiXXuWeWWYWaaWXXXuWeXxyqZsmWWYWXWWWlYWce+WWWXXWmWG00",
  "26234089"]
@[expose] def ext_full_set_inactive : List (SigEntry × Nat) := []

@[expose] def hint_full_init_fresh_var : x64Isa.Hints := _decH #[
  "XU311317101D1E121F1B14151B1B1B140604051505150514041B1BEB142C8814091201281B09040B0B2409",
  "0700051B0B190C381D0811010124041939034814404X46564ANK04200114A01000854AZ50X4656Z471B581",
  "0074AZ50X4656Z47Z65ZID1B7810D0202AM2305123351234512316123560232CN225112252122531225482",
  "255P22500yWZWZikfmXdXaWiWpaewcopbrrgrgfYaegrgrgL0mWWWWWWWWWWWWWYWWWWWWWWWWWWWWWWWWW00e",
  "WmmWaegWaWYaXXWWWaWWWWWWWWWWWWWWW00XmXcYWwWXWWWcWWWWWYWWWWWWWWWvpaWWWWW00Z////l++//tlZ",
  "/t/xtzz///t///////////////VmXXWWemyWeWaeYYWWWeWWWWWWWWWWWWWWW00066234089"]
@[expose] def ext_full_init_fresh_var : List (SigEntry × Nat) := []

@[expose] def hint_full_update_classify_fid : x64Isa.Hints := _decH #[
  "D2B1404090B0409381B110B0B2830000000014A141010224AE41B201000pWfmW50Y00aWYXX0000lt/xzzVe",
  "WaYY00000"]
@[expose] def ext_full_update_classify_fid : List (SigEntry × Nat) := []

@[expose] def hints : List x64Isa.Hints := [hint_full_zero_tables1, hint_full_zero_tables2,
    hint_full_fixed_bytes, hint_full_init_ptrs, hint_full_init_hdr, hint_full_calc_max_v,
    hint_full_calc_ext_cap_m5, hint_full_calc_scr_cap_m5, hint_full_init_arenas,
    hint_full_init_state_m5, hint_full_init_state, hint_full_m6_mem_init,
    hint_full_set_inactive, hint_full_init_fresh_var, hint_full_update_classify_fid]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("kissat_parse_header", [i64, i64, i64], [.bool]), 0),
   (("m6_hdr_init", [i64], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Internal
