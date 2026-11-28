module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Backtrack

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X23)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X2)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X8))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.gpr (XRegOrSp.reg (XReg.X20)))]

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

@[expose] def hint_full_assign_lvl : armIsa.Hints := _decH #[
  "X4400011021113021123041516171819130A4114110401110B2401012B3C0C1C0C2C0C2D0D400000003B4E",
  "5DV8X1990X33T76C7FR6P50BiI002A4E5DV8X1990X33T76C7FR60AiI00154E5DV8X199005I0000iiageucY",
  "Wesurgnqg40mYYWWWWWWW00YWWeXXWWWWaXWG0aWWWWWWWWWYeWWWmW10d/////x/llzz////tz+VaWmmYYWWW",
  "WeYX00000"]
@[expose] def ext_full_assign_lvl : List (SigEntry × Nat) := []

@[expose] def hint_full_assign : armIsa.Hints := _decH #[
  "X5510F0F10021013021023041516171819130A4014100400100B2400002B3C0C1C0C2C0C2D0D400000003B",
  "4E5DX18X39BFX53V76C91T6R50BiI002A4E5DX18X39BFX53V76C91T60AiI00154E5DX18X39BF05I0000ZZX",
  "YocXmmYbsbgqjYn30aWmmWWWWWWW00mWYWeeWWWXWea00XWWWWWWWWWWoWWWaWW80X/////+/xx/ll///z/ltV",
  "XWaaWmmWWWYWme00000"]
@[expose] def ext_full_assign : List (SigEntry × Nat) := []

@[expose] def hint_full_save_target_best : armIsa.Hints := _decH #[
  "XS2D041D0B1C1F10131D0G06061D0G0402110101044104410441041D01021G110101041D0G1D0G04021D0D",
  "0D044D044D044D041E0D021G1D0D0D041E0GJ000000025G0CCI3N64E0500016EFCCI3N64EG01D601006EFC",
  "CI3N64EG01D601006EFCCI3N64EG01D601027EFCCI3N64EG0TD0700017EFCCI3N64EG0TD0700017EFCCI3N",
  "64EG0TD0700017EFCCI3N64EG0TD0700037EFCCI3N64EG0XQD07000200000013G0CCI31E301003G0CCI31E",
  "301003G0CCI31E301024G0CCI3Y7E0400014G0CCI3Y7E0400014G0CCI3Y7E0400014G0CCI3Y7E0400034G0",
  "CCI3Z4E0400000XWWWYZoZoZoWWWaWmWWXXvXvXvWWWYYreH0XWeYaWmWmWmWmWnWmaXYWeWeWeWeWemWWW00m",
  "aXYWeWeWeWeYemeYWnWaWaWaWaXaeWWY40mXWXWXWXWXWWWWWeWmWmWmWmWmWWmWW00Z+ltzv/l/l/l/lvk/dx",
  "+y/t/t/t/tytkl/xNXmeYcWmWmWmWmcnWuaXZWeWeWeWeZenmWa80000"]
@[expose] def ext_full_save_target_best : List (SigEntry × Nat) := []

@[expose] def hint_full_backtrack_raw_m5 : armIsa.Hints := _decH #[
  "aE3D021D041D0B1F1011161D0G0D0D1C0G0402130303044304430443041C03021G130303041C0G1C0G0402",
  "100000044004400440041C00021G100000041C0G1H1I1J1K1L1M1N1D153O0O1D0G0O8D0P4F0C0C0G200002",
  "3F030C0G2F6F140F0F0F041D0D0F0G0D0D0002010D1F040F02000F3D0206090A1F0F00020G2D042Q041101",
  "30000702270R54580C0P2D0P1D0PR0000000124E5S0200026K1GF4E5SM6RD0600017I0GFM64E5SRDK11C70",
  "1007I0GFM64E5SRDK11C701007I0GFM64E5SRDK11C701028I0GFM64E5SRDK1X1C0800018I0GFM64E5SRDK1",
  "X1C0800018I0GFM64E5SRDK1X1C0800018I0GFM64E5SRDK1X1C0800038I0GFM64E5SRDK1XUC0800035K1GF",
  "4E5SM61C501005K1GF4E5SM61C501005K1GF4E5SM61C501026K1GF4E5SM6YBC0600016K1GF4E5SM6YBC060",
  "0016K1GF4E5SM6YBC0600016K1GF4E5SM6YBC0600036K1GF4E5SM6Z8C06000235S4EaAO1330100BZPLZNK5",
  "SZJIa15aAO4EZTNZLJZHHZRM238B0201CZPLZNK5SZJIa15aAO4EZTNZLJZHHZRMaM813C0100FaL3ZPLZNK5S",
  "ZJIa15aAO4EaM8aQCZRMZTNZLJZHHaPF0Fmm0003FaL3ZPLZNK5SZJIa15aAO4EZTNZLJZHHaM8b7CaQCZRM0F",
  "iW000AHaL3ZPLZNK5SZJIa15aAO4EZTNZLJZHHZRMaM8cH9b7CaQCcG61FHXWW0110JaL3ZPLZNK5SZJIa15aA",
  "O4EZTNZLJZHHZRMaM8cH9b7CaQCcG6cVQcIA1FJXWW011535S4EdT3030001020010maWWWyWxnmkWiiWmXuWe",
  "WWYWXgxcWbmiXml+azgrgmWmWWXXvXvXvWWWYWeWWWmymymymWWXXgqeH0XWeWWWaWWWWWWWWWWWWWWYWWaWWW",
  "mWaXWWWWWWWWWWmaXYWeWeWeWeWemeYWnWaWaWaWaWaeWWWW00YWmaWWWYWaaWXXXeWmWfWmXWmYWWWeWYWmXW",
  "WWWWWWWeYWnWaWaWaWaXaeaXWemYWYWYWYWoaWWXY40iWfmmcmaaWWWuWWWWWWWWXYWWnWWmWWWiWWWWWWeWmW",
  "mWmWmWmWWWWaWeWeWeWeWeWWeWWW00/x+/n///x/tt/zzyl+//j+/z+/x///l/x+/z/+//////dx+y/t/t/t/t",
  "ytlpz/klx/x/x/x+htd/zxNaXWkWWWaWeeWYYZmXWWoXWYXWaWWWmWaXWYWXWWWWWWuaXZWeWeWeWeZemiYWnm",
  "aWaWaWaXqeuWYa800072034567"]
@[expose] def ext_full_backtrack_raw_m5 : List (SigEntry × Nat) := []

@[expose] def hint_full_backtrack : armIsa.Hints := _decH #[
  "XV3C021C041C0B1F1011161C0G07071C0G0402130303044304430443041C03021G130303041C0G1C0G0402",
  "100000044004400440041C00021G100000041C0G1CJ0000000124E5D0200026K1GF4E5DM6R70600017I0GF",
  "M64E5DR7K11C701007I0GFM64E5DR7K11C701007I0GFM64E5DR7K11C701028I0GFM64E5DR7K1X1C0800018",
  "I0GFM64E5DR7K1X1C0800018I0GFM64E5DR7K1X1C0800018I0GFM64E5DR7K1X1C0800038I0GFM64E5DR7K1",
  "XUC0800035K1GF4E5DM61C501005K1GF4E5DM61C501005K1GF4E5DM61C501026K1GF4E5DM6YBC0600016K1",
  "GF4E5DM6YBC0600016K1GF4E5DM6YBC0600016K1GF4E5DM6YBC0600036K1GF4E5DM6Z8C060002bM4318309",
  "042902110mWmWWXXvXvXvWWWYWeWWWmymymymWWXXgqeH0maXYWeWeWeWeWemeYWnWaWaWaWaWaeWWWW00eYWn",
  "WaWaWaWaXaeaXWemYWYWYWYWoaWWXY40eWmWmWmWmWmWWWWaWeWeWeWeWeWWeWWW00Z//dx+y/t/t/t/tytlpz",
  "/klx/x/x/x+htd/zxNuaXZWeWeWeWeZemiYWnmaWaWaWaXqeuWYa80020"]
@[expose] def ext_full_backtrack : List (SigEntry × Nat) :=
  [(("full_backtrack_raw_m5", [i64, i64], []), 64)]

@[expose] def hint_full_backtrack_ac_fid : armIsa.Hints := _decH #[
  "ZT3D021E0B1E040D1E0P1F1011161E0G0E0E1D0G0402130303044304430443041C03021G130303041C0G1D",
  "0G0402100000044004400440041C00021G100000041C0G0E0B1F1011161E0G0E0E1C0G0402130303044304",
  "430443041C03021G130303041C0G1C0G0402100000044004400440041C00021G100000041C0G0P1EX50000",
  "000124I570200036O1KF4I57Q6VE0600017M0KFQ64I57VEO11C701007M0KFQ64I57VEO11C701007M0KFQ64",
  "I57VEO11C701028M0KFQ64I57VEO1X5C0800018M0KFQ64I57VEO1X5C0800018M0KFQ64I57VEO1X5C080001",
  "8M0KFQ64I57VEO1X5C0800038M0KFQ64I57VEO1Y2C0800035O1KF4I57Q61C501005O1KF4I57Q61C501005O",
  "1KF4I57Q61C501026O1KF4I57Q6YFC0600016O1KF4I57Q6YFC0600016O1KF4I57Q6YFC0600016O1KF4I57Q",
  "6YFC0600036O1KF4I57Q6ZCC06000234I57FD0300017ZR1ZNF4I57FDZT6a2E0700018ZP0ZNFZT64I57FDa2",
  "EZR11C801008ZP0ZNFZT64I57FDa2EZR11C801008ZP0ZNFZT64I57FDa2EZR11C801029ZP0ZNFZT64I57FDa",
  "2EZR1a8C0900019ZP0ZNFZT64I57FDa2EZR1a8C0900019ZP0ZNFZT64I57FDa2EZR1a8C0900019ZP0ZNFZT6",
  "4I57FDa2EZR1a8C0900039ZP0ZNFZT64I57FDa2EZR1b5C0900036ZR1ZNF4I57FDZT61C601006ZR1ZNF4I57",
  "FDZT61C601006ZR1ZNF4I57FDZT61C601027ZR1ZNF4I57FDZT6bIC0700017ZR1ZNF4I57FDZT6bIC0700017",
  "ZR1ZNF4I57FDZT6bIC0700017ZR1ZNF4I57FDZT6bIC0700037ZR1ZNF4I57FDZT6cFC070009040A1029bO43",
  "0A311L42A0211342A0211242A0211042A0211aB42A0211A2319022910eWWaWWWekekekeWWWmYWWWadadada",
  "WWWegrWWYWWWadadadaWWWeXWWWYZoZoZoWWWabgnWmH0aaXWemYWYWYWYWWWYWmaeXWXWXWXWWWWWWWYWmaeX",
  "WXWXWXWXYXWeYaWmWmWmWmWnWWWWaa00YYWmaeXWXWXWXWfYXWeYaWmWmWmWmanWWWeXWeYaWmWmWmWmanWmaX",
  "YWeWeWeWeYemWWaYY40YWaWaWaWaWaWWWWXWYWYWYWYWYWWYWWWWWXWYWYWYWYWYWWWWWmXWXWXWXWXWWXWWWW",
  "W00X//xv+/tdz/z/z/z/bxy/lxp+/+/+/+/ozv//ly/lxp+/+/+/+/oz+ltzv/l/l/l/lvky//nxxNacXWeuYW",
  "YWYWYWwaZWmaiXWXWXWXWjYcWWmZWmaiXWXWXWXWjYXmeYcWmWmWmWmcnZWWkaa800212"]
@[expose] def ext_full_backtrack_ac_fid : List (SigEntry × Nat) :=
  [(("full_backtrack_raw_m5", [i64, i64], []), 64)]

@[expose] def hints : List armIsa.Hints := [hint_full_assign_lvl, hint_full_assign,
    hint_full_save_target_best, hint_full_backtrack_raw_m5, hint_full_backtrack,
    hint_full_backtrack_ac_fid]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Backtrack
