module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Decide

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X2))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.gpr (XRegOrSp.reg (XReg.X5))), (.slot 0 .w64),
  (.slot 1 .w64), (.flag LeanQbe.T.Arm64.ArmCond.lt)]

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

@[expose] def hint_full_next_dec_var : armIsa.Hints := _decH #[
  "ZL201112130415132606271407070708191909330309130626271407070708191909330309061A13241B03",
  "030C2914090909080903080D070E0F052G0F06240G062H0B030I0J1K0L0K0C0D29042M0K05090C67070C2E",
  "0F062505062N0D09070E3B5K0O05090C430404031403080B3914090909080306H00130010036081A203000",
  "154P6081A2F52395020054P6081A2F505000274P6081A2J9F5I307000254P6081A2F52395020274P6081A2",
  "XE9F5XD307000356081A24PY6A135010356081A2Y6A4P05000256081A2Y6A4P050002A6081A2Y6A4PZ4GYV",
  "EYU7YQ9Z150AX000796081A2Y6A4PZHIZAGZ4GZG31K9a0110D6081A2Y6A4PZHIZAGZ4GZG3ZIJZEHZLLZVM4",
  "O59KDa0482Fa7K6081A2Y6A4PZHIZAGZ4GZG3ZIJZEHZLLa4OZVM397EFe132536081A2133010136081A2030",
  "00346081A2bP3040001020010bmWYWWWZmWdiWiZWuiWiiWmZWWucWWWWsWWwmZaoWYuWmvamWsWbYL0XWWmYW",
  "eeeWWWWWWWXWeWWWWWWWWaeYWWWWYWXWWYWWWWeYWWWWWYWoWW00mmeXYaaaWWWeWXWWmaYWeXXeWmYaXWWqYX",
  "WmnWXWWWeaXYWWWYXWfWe00YWmWWWWWXmWZaWaXWeaWaaWWWWWeYWWWeYWWWWXWWXWWWWeWWeWWWW00kk/lzxt",
  "tt///d/zn+/tx/dzyl+Zhtz/+dxz+Yz/z///ltzx///xz/b/lVXnWmYaeeeWWWuWYkXWeaWuYZmXyqeYWXuaYX",
  "zYWYWWWmeYaWWWaYWwWm000042345"]
@[expose] def ext_full_next_dec_var : List (SigEntry × Nat) := []

@[expose] def hint_full_randec_var_lvl_fid : armIsa.Hints := _decH #[
  "ZI3G081304130413120217070702170711010107110D01060202070707030711130318130D031909120202",
  "091206120219090902090707070B0202220D070B03030B07070203021D02190D070B03030B070709030913",
  "1712020303091213031P110D0707071413030303032214020202080906700130010334I5Q7G123010127G4",
  "I02000337G4IYIQ123010237G4IZ2R19301025a0Pa217G4Ia6719501016a0Pa217G4Ia67a9906000602021",
  "B2306XF2260X04061306J2317J22710sWXWqXaXaWWWWWWWWWWfYYeeXaWWYYefeeH0aWYWWWWWWWWWWWWWWWW",
  "WWWWWWWYWWWWmWWWWW00YYXWWYWWWWWWWWfWWWfWWWWeWXXWWWWeWWWXY40eYmWiWYWYWZeWWZeWXYZWWuWWYW",
  "aeWuZWWW00lvxz//xZ/////ucbxucby///Z/zz///Zl///zxNcaYWWayWWWWWdvwadvwZWWWyWYYWWWymWWWYa",
  "8002223"]
@[expose] def ext_full_randec_var_lvl_fid : List (SigEntry × Nat) :=
  [(("full_m7_state_init", [i64], []), 0),
   (("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0)]

@[expose] def hint_full_randec_var_m7 : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_randec_var_m7 : List (SigEntry × Nat) :=
  [(("full_randec_var_lvl_fid", [i64, i64], [i64]), 48)]

@[expose] def hint_full_decide_m7 : armIsa.Hints := _decH #[
  "Y628281712111P19081909090800080918100412040918191S030309031902170647120909170B07010B17",
  "21040H1P10151E110F47141704071708240707283202120222092303900130010014I131010264IHPF183B",
  "7D2196010154IHPF183B7195010244IHPF18319401020000003A4IXF3YH5YJEXU9YL1YF0XS2YDPYBH0AaI0",
  "0294IXF3YH5YJEXU9YL1YF0XS2YDP09aI00154IXF3YH5YJEXU905I001020210ZZXYocXmmYbsbgmwWea+amY",
  "WeeWYYre00aWmmWWWWWWWWWWWWmYYWWmWW40mWYWeeWWWYWnWWWmWWeXXWWeWY20XWWWWWWWWWWoWWWeWYWWWX",
  "WWWWWeWWW00l/////+/xx/ll///x+z//+dm/jzzm/l/xRXWaaWmmWWWaXYWWXulWoYYlWmWa400012"]
@[expose] def ext_full_decide_m7 : List (SigEntry × Nat) :=
  [(("full_randec_var_lvl_fid", [i64, i64], [i64]), 48),
   (("full_next_dec_var", [i64], [i64]), 48)]

@[expose] def hint_m6_hdr_decide_fid : armIsa.Hints := _decH #[
  "Z428281712111P19081909090800080918100412040918191S030309031902170647120909170B07010B17",
  "21040H1P10151E110F47141704071708240707283202120222092303180203090704070809040909041909",
  "090909090909090I090912090D0902C00130010014I131010014I131010264IHPF183B7D2196010154IHPF",
  "183B7195010244IHPF1831940105A4IXF3YH5YJEXU9YL1YF0XS2YDPYBH0AaI00294IXF3YH5YJEXU9YL1YF0",
  "XS2YDP09aI00154IXF3YH5YJEXU905I0021a0319101003a034IZV20300022a034I02000302021bO2301022",
  "100YWWWWWWZZXYocXmmYbsbgmwWea+amYWeeWYYre00YWWWWWWeWWWWWWWWWWWaWmmWWWWWWWWWWWWmYYWWmWW",
  "40XWWWWWmaYeaWWWWWWmWYWeeWWWYWnWWWmWWeXXWWeWY20eWWWWmeWXWWWXWWWWWWWWWWoWWWeWYWWWXWWWWW",
  "eWWW00ly////+/txlt/////+/xx/ll///x+z//+dm/jzzm/l/xRZWWWWXWeameWWWWWXWaaWmmWWWaXYWWXulW",
  "oYYlWmWa400112"]
@[expose] def ext_m6_hdr_decide_fid : List (SigEntry × Nat) :=
  [(("full_randec_var_lvl_fid", [i64, i64], [i64]), 48),
   (("full_next_dec_var", [i64], [i64]), 48),
   (("m6_hdr_init", [i64], []), 0)]

@[expose] def hints : List armIsa.Hints := [hint_full_next_dec_var,
    hint_full_randec_var_lvl_fid, hint_full_randec_var_m7, hint_full_decide_m7,
    hint_m6_hdr_decide_fid]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_m7_state_init", [i64], []), 0),
   (("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("m6_hdr_init", [i64], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Decide
