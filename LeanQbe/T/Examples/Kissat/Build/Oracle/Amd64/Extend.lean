module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Extend

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r14, Reg64.rdi, Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.r13]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rax), (.gpr Reg64.rdx), (.gpr Reg64.r8), (.gpr Reg64.rcx), (.flag CondCode.c),
  (.flag CondCode.z), (.flag CondCode.l), (.gpr Reg64.r9), (.gpr Reg64.rsi), (.gpr Reg64.rdi),
  (.gpr Reg64.rbx), (.gpr Reg64.rbp), (.gpr Reg64.r12), (.flag CondCode.nz), (.gpr Reg64.r13),
  (.gpr Reg64.r14), (.flag CondCode.g), (.flag CondCode.nc)]

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

@[expose] def hint_full_extend_push2 : x64Isa.Hints := _decH #[
  "M400001121301040000352617101204020412280837072001000100349A15813341000ZmwWqZZmYH0eXW00",
  "oWaaWm00XmeeWWWuW00Z///+h/tt+/VXqWeeXW00000"]
@[expose] def ext_full_extend_push2 : List (SigEntry × Nat) := []

@[expose] def hint_full_extend_push_cl : x64Isa.Hints := _decH #[
  "XM4A010024320200041B0B191C08010A0D2030000D00040107073501260113041013110401041E20030D20",
  "30000D00040707352623110470010001027P9RCNBS8UA4FH2117Y01007P9RCNBS8UA4FH22137Y02018P9RC",
  "NBS8UA4FH2X13118Y01078P9RCNBS8UA4FH2Y4E2138Y02019P9RCNBS8UA4FH2Y4EYA1139Y0101BP9RCNBS8",
  "UA4FH2YA1YB3YH0Y4E0BY0001020010XmuyWXuWjWgWWukWWkWYoXvH0YWWYWemWWWWWaWWWWaWWWWWW00XWXX",
  "WaeWaWfWYXWmXYWYWWmY00mWcWWyWaaWWWWZWWdWmWiu00/y/zz/tl/t/b/vz+/yh/x/+XvVZWYYWemWeWwWcY",
  "XWZqWaWX+c0000523450"]
@[expose] def ext_full_extend_push_cl : List (SigEntry × Nat) := []

@[expose] def hint_full_extend_core_fid : x64Isa.Hints := _decH #[
  "Y2231817120D5D35011110041B0D2D014D1A0A0E1D043808090904082G01040E0000040E1E0E1E0E00000H",
  "0H0D192000040118011B01111D0D2430001500101918040DI00000000463C2A7490400005638849C2A7105",
  "01016638849C2A7E00600006638849C2A7E0060003363C2A71B30101463C2X1BA71C40100463C2X1BA7104",
  "01024XAC63C2A70400015XAC63C2A7XDE05G0006XAC63C2A7XDEX1B116G1017XAC63C2A7XDEX1BXH107G00",
  "6663XCAC2Y9EXACA7060000663C2XCAXACY9EA718601017YG963C2XCAXACY9EA70700026XCAC2Y9EXAC63A",
  "7298602018XCAC2Y9EXAC63A7Z38Z2910801017XCAC2Y9EXAC63A7Z3819701000XaXuWWofWiWWWnWWWiWiX",
  "WdmWeXaXvyYL0YaWWWYWeWWaWXaWWaXWWmWWWWYWXWWWWWW00XYWWmXYaWWYWaoWWYWmmeWgWeXXWmWYYWe00u",
  "WWWWWaWXmenWWYaaWaWmWWWWWeaW00zv/+/zxt//x/sf//x+k/l/h/lzz+l/xx/lVYcWXWYaeWWaWfsWWaXnWm",
  "WqWmYYXmWaaWm000042345"]
@[expose] def ext_full_extend_core_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_unperm_fid : x64Isa.Hints := _decH #[
  "Z72005241102030D020218040304100D0D0H1A290904360917071B29090436091A0A1A29090436091B0B19",
  "23030436031A0A130H141327070436071909140D0D0H1101181G0808010101181G0808010101181G080801",
  "0101181G080803010H141101181G08080304D000000053H2O0G20300005O0J8C1G2H219501005O0J8C1G2H",
  "219501005O0J8C1G2H213501037O0J8C1G2H2S3TA19701018O0J8C1G2H2S3XCBTA19801018O0J8C1G2H2XR",
  "AS3XCB19801017YA9O0J8C1G2H2XRA13701037YU3O0J8C1G2H2YT917701022H2O013201002H2O013201002",
  "H2O013201000XeWWXeWqWgWbWWWaZmiWXWyZaZmimkXoXucWWeYWfH0eWWemWWWWWWWWWWXWWaWemWXWWWaWWW",
  "mWWYWWWWWWW00aWWaeWWWWWWWWWnemWYWaeWWmWWYWWWeWWXWYbYeaY40aWXWWmWeWWWWXWmaWaeaXXWmaaYWm",
  "meYWWXWWW00Z/pt/tdt/x/z/+/+ik/tx/tdz+//tx/+/l/xz/vnvYpvNieWeueWaWYWXWXpnWeaWeuYXWWeaWX",
  "WmWaYWckczic8000223"]
@[expose] def ext_full_unperm_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_extend : x64Isa.Hints := _decH #["00102301000000000700010"]
@[expose] def ext_full_extend : List (SigEntry × Nat) :=
  [(("full_extend_core_fid", [i64], []), 40),
   (("full_unperm_fid", [i64], []), 24)]

@[expose] def hints : List x64Isa.Hints := [hint_full_extend_push2, hint_full_extend_push_cl,
    hint_full_extend_core_fid, hint_full_unperm_fid, hint_full_extend]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Extend
