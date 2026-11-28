module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Extend

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[(XRegOrSp.reg (XReg.X0))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.lt), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.flag LeanQbe.T.Arm64.ArmCond.gt),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.flag LeanQbe.T.Arm64.ArmCond.cc)]

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

@[expose] def hint_full_extend_push2 : armIsa.Hints := _decH #[
  "N40000112130104003005100617101204020412280837072001900100349A15813361000ZmwWqXXuYH0eXW",
  "00oWaaWm00XmeeWWWyW00Z///+h/tt+/VXqWeeXW00000"]
@[expose] def ext_full_extend_push2 : List (SigEntry × Nat) := []

@[expose] def hint_full_extend_push_cl : armIsa.Hints := _decH #[
  "XO4701001304320200041A0A1B1C080107070D51010D0104030E3E050311060310041110130403041F2100",
  "0D51010D01040E3E051E0620130470019001027PBRCNAS8V749H2137Y81007PBRCNAS8V749H22307Y82018",
  "PBRCNAS8V749H2X20138Y81078PBRCNAS8V749H2Y4F2308Y82019PBRCNAS8V749H2Y4FYA3109Y8101BPBRC",
  "NAS8V749H2YA3YB0YG1Y4F0Bo80000uadWWyWjWgWWedWWkWYoXuH0XWWXWaeWWWWWaWWWWaWWWWWW00mWmmYa",
  "WaWfWYXWmXYWaWWmY00eWZmWiWaaWWWWZmWcXmWiu00l+l++/xt/t/b/vz+/yh/t/+XuVXmXXWaeWeWwWcYXWZ",
  "qWeWX+d00000"]
@[expose] def ext_full_extend_push_cl : List (SigEntry × Nat) := []

@[expose] def hint_full_extend_core_fid : armIsa.Hints := _decH #[
  "Y9281A12130D301D0000000500070011041A0D2D01201D1C0C0G1D043000070704200H01040G0101042G2G",
  "0G01010I0I0D102A0A040E0F0F0E1E0A0B0A1D0D243A0A15010A011017040DI00000000468C3A249040000",
  "5688A49C3A211501016688A49C3A2E10600006688A49C3A2E1060003368C3A21A30101468C3X1AA2194010",
  "0468C3X1AA219401024XA968C3A20400015XA968C3A2XDG05G0006XA968C3A2XDGX1A116G1017XA968C3A2",
  "XDGX1AXH107G006668XCCC3Y9GXA9A2060000668C3XCCXA9Y9GA217601017YG068C3XCCXA9Y9GA20700026",
  "XCCC3Y9GXA968A2207602018XCCC3Y9GXA968A2Z37Z201A801017XCCC3Y9GXA968A2Z3710701000XWXuWWm",
  "eWiWWWvmWWcWiXWbmWeXWWXiYL0YaWWWYWeWWaWXaWWaXWWmWWWWYWXWWWWWW00XYWWmXYaWWYWaoWWYWmmeWg",
  "WeXXWmWYYWe00uWWWWWaWXmenmWYcaWaWmWWWWWeaW00zv/+/zxt//x/sf//x+k/l/h/lzz+l/xx/lVYcWXWYa",
  "eWWaWfsWWaXnWmWqWmYYXmWaaWm00000"]
@[expose] def ext_full_extend_core_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_unperm_fid : armIsa.Hints := _decH #[
  "ZP280511041102000D02021004030J190D0D0I1723030403030306031A0A1A230304030303060317071723",
  "030403030306031A0A1328080408080806081707180I141827070407070706071303140D0D0I110013010H",
  "0101010101101H0000010101101H0000010101101H000008010I14110013010H01010804D000000053H2O9",
  "G20340005O9J0C1G2H213581005O9J0C1G2H213581005O9J0C1G2H218581037O9J0C1G2H2S8T713781018O",
  "9J0C1G2H2S8XCAT713881018O9J0C1G2H2XR7S8XCA13881017YA3O9J0C1G2H2XR7187G1037YU8O9J0C1G2H",
  "2YT3177G1022H2O918201002H2O918201002H2O918201000eWWXeWqWgWXWWWaWWiWXWWZaWWimWXoWWcWWeY",
  "WeH0eWWemWWWWWWWWWWXWWaWemWXWWWaWWWmWWYWWWWWWW00aWWaeWWWWWWWWWnemWYWaeWWmWWYWWWeWWXWYb",
  "YeaY40aWXWWmWeWWWWXWmaWaeaXXWmaaYWmmeYWWXWWW00Z/pt/tdt/x/z/+/+ik/tx/tdz+//tx/+/l/xz/vn",
  "vYpuNieWeueWaWYWXWXpnWeaWeuYXWWeaWXWmWaYWckczid80000"]
@[expose] def ext_full_unperm_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_extend : armIsa.Hints := _decH #["00102300000000000700010"]
@[expose] def ext_full_extend : List (SigEntry × Nat) :=
  [(("full_extend_core_fid", [i64], []), 0),
   (("full_unperm_fid", [i64], []), 0)]

@[expose] def hints : List armIsa.Hints := [hint_full_extend_push2, hint_full_extend_push_cl,
    hint_full_extend_core_fid, hint_full_unperm_fid, hint_full_extend]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Extend
