module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Watch

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X14)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X13)), (XRegOrSp.reg (XReg.X1)),
  (XRegOrSp.reg (XReg.X4)), (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X20)),
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X11)),
  (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24)),
  (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X7))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.slot 2 .w64), (.slot 1 .w64),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.flag LeanQbe.T.Arm64.ArmCond.gt)]

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

@[expose] def hint_full_wsort_sift : armIsa.Hints := _decH #[
  "V400102530303030304030520000000000006030441010000000002200001023000000003475879301A303",
  "014475879DA23440221020010ZWZWWuWc00YWW00aWeWWWXWW40XXvWkeZo00dp/l/p/y//JiWmWiWZWWC0000"]
@[expose] def ext_full_wsort_sift : List (SigEntry × Nat) := []

@[expose] def hint_full_wstack_radix_sort_m6 : armIsa.Hints := _decH #[
  "b56B100C10007D000E163D060E3D0D0D0D0D0D0D0D0D2F0F3D0D0D0D0D0D0D0D0D2F0F3D0D0D0D0D0D0D0D",
  "0D2F0F3D0D0D0D0D0D0D0D0D2F0F000D0E153D0D0D0D0D0D0D0D0D2F0F00054F0F0G0D00060E3D0D0F0F0F",
  "0F0F0F0F2G0G0H0H5D0D0F0F0F0F0F0F0F2G0G0H0H5D0D0F0F0F0F0F0F0F2G0G0H0H5D0D0F0F0F0F0F0F0F",
  "2G0G0H0H200D0E153D0D0F0F0F0F0F0F0F2G0G0H0H20050E4D4D4D4D000D0E154D00050406K00000000781",
  "AB794758639A147010188179B44758AB639A080000881AB79B44758639A1D80100881AB79B44758639A1D8",
  "0100881AB79B44758639A1D80103881AB7963B447589A08000088179B44758AB639A108010088179B44758",
  "AB639A108010088179B44758AB639A1080105881AB6379B447589A080000881AB7963B447589A20D802018",
  "9AB4815863AB7947080000881AB6379B447589A1080100881AB6379B447589A1080100881AB6379B447589",
  "A1080105881AB794758639AB408000089AB4815863AB7947108010089AB4815863AB7947108010089AB481",
  "5863AB794710801000yWW+ldpmWZWuWiWXmiWdiZWXxWuWkucWZWWWiWcWZWWZWXuuWkcWZnmWuWXmWbgrW00m",
  "mWnWWWWWWfWWWWWnWWWWWWWWWWWWWWWWWWWoWWeWWWaeWWWWWWWWWWWWWWamYaWWWWG0eeWemWWWWXWmWWWWem",
  "WWWWWWWWWWWWWWWWWYXWWaWWWYaWWWWWWWWWWWWWWmeXYWWWW80eYXWmWWXahdaWeobppaniyvahdcfYvvWWWa",
  "WYvvWYXiyuhdcYvvmskeWWmXWWWa40ddd/kl////z+l////kl/////////////////xy//p///xp//////////",
  "///+/dzv////FuuWnmWWWWYXmWWWWnmWWWWWWWWWWWWWWWWWaZWWiWWWaiWWWWWWWWWWWWWXWuYcWWWWG0000"]
@[expose] def ext_full_wstack_radix_sort_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_wstack_defrag_m6 : armIsa.Hints := _decH #[
  "aO27061G0G171I180C60000009093F0J05000D060A240143053J0E0903100002190309000E0D0C1D000902",
  "530303030304030520000000000006030449090000000002200009020C0D0C132906530303030304030520",
  "000000000006030449090000000002200009020D0C03030909030309090C43030H0H0H0F0F34040C0D0D0F",
  "0F0C0C030E190309002020290A030E1503430A05030G0B05K0000000144KEIC7G831AD403005G8C74KEIAG",
  "513A4D505016G8C74KEIAGK341A4D604035EIC7G84KXH10500045G8EIC74KXH10500005XH1C7G8EI4K1D50",
  "1016Y5DXH1C7G8EI4K0600006Y5DXH1C7G8EI4K309A603017Y5DXH1C7G8EI4KYBA234702245G8XH1C7EI4K",
  "1D501016G8XH1C7EI4KZLD0600006G8XH1C7EI4KZLD309A603017G8XH1C7EI4KZLDZTA2347022414K1G101",
  "005EIC7G84KXH12GB502018EIC7G84KXH1bGBbFGbU4080001BEIC7G84KXH1bGBbFGbU4bNHc1Dc3F1AB0100",
  "BEIC7G84KXH1bGBbFGbU4bNHc1Dc3F1AB0100BEIC7G84KXH1bGBbFGbU4bNHc1Dc3F1AB010502023c9A3343",
  "133053423260A2432312502242624A3343133053423260A2432312502242620oYWWWyWWciuWWWWZmZWWWWW",
  "WcWcWXmWiWuWWWcWcWXmWiWWWeeWWWiWkWaYqH0aWmWaeWWWWWWXWWWWWWXWWWWWWWaWWWWWmWWWWWWaWWWWWW",
  "WmaWWWWWWWW00YWeWYaWWWWmgWmWWYWWWmeWmWWWYWWeWeeeWmWWWYWWeYeYWfYWWXWWWeW40YWWWWWWqXnfWY",
  "neWWYZoWymdaWeWWWYZoWymdaWWaXWWWWaWcaWWW00d//v/d/xp///+lZ+///x//+ld+//d/v//l/lld+//d/v",
  "//dxZx/jv/zr///l/NcWuWaiWWWXmyXWWWaWWXmuXWWuWcWWmWmmuXWWuWcWWuayaWocWYgWWWmW80050"]
@[expose] def ext_full_wstack_defrag_m6 : List (SigEntry × Nat) :=
  [(("full_wstack_radix_sort_m6", [i64, i64, i64, i64, i64, i64], []), 0)]

@[expose] def hint_full_watch_push_slow_m6 : armIsa.Hints := _decH #[
  "a45L17070E0C0C170J170J17270E0711010E170711010E2M1N1O0P0P0P01013G0G0Q0J0J170705170C170O",
  "052J380Q07180J08022J3G0G0Q081A02280J0J380J0J3G0G1702070J0H0H07060H170705170C07070G0G27",
  "0O05070H05480D0D0B0B0C0E1A000A0F2F2F2F040A0E15470405072J3Q05070E130379030E153905070717",
  "0303030HO0017001017797R8Q636S4T9L07YV0027797R8Q636S4T9L187YV1027797R8Q636S4T9L187YV100",
  "8797R8Q636S4T9LO808YV003G4TXPQXAM9LXOG797RXCN8Q636SXHPXJ1XEOXNGX880GrxQ002C4TXPQ8QXAM9",
  "LXHP797RXCN636SXEO0CXsM00374TXPQY478QXAM9LXHP07XA001F797RXCN8Q636S4TXPQXEOXAM9LXHPXJ1X",
  "OGXNG0FzbR001G797RXCNYF78Q636S4TXPQXEOXAM9LXHPXJ1XOGXNG0GXwhJ00264TXPQYF7XAM9LXOG06XI0",
  "03C4TXPQXAM9LXOG797RXCNYF78Q636S0CZpQ00254TXPQXAM9LXOG05Q002B797RXCN8Q636SXPQ4TXAM9LXH",
  "P3BGHBpR301D797RXCN8Q636SXPQ4TXAM9LXHPZRHXEO2BGDpR202F4TaHHaJ8aGGXAM9LXHPaLDXPQ797RXCN",
  "8Q636S0Fzm0000G797RXCN8Q636SaGGaJ8aNBaLDaHHXPQ4TXAM9LXHP14GXR100G797RXCN8Q636SaGGaJ8aN",
  "BaLDaHHXPQ4TXAM9LXHP14GXR100G797RXCN8Q636SaGGaJ8aNBaLDaHHXPQ4TXAM9LXHP14GXR10594TaHHaJ",
  "8aGGXAM9LXHPaLDXPQ09000184TaHHaJ8aGGbRQXAM9LXHP08000094TaHHaJ8aGGbRQXAM9LXHPaLD1990100",
  "94TaHHaJ8aGGbRQXAM9LXHPaLD199010094TaHHaJ8aGGbRQXAM9LXHPaLD19901050A3273110860950A3XI4",
  "272211X34272211ZG230B462722112B00XWWuWYrgmWWycWZmWXnnmWWXWWWXWmWXWyWZmcYWZmuWmWZmueYXW",
  "XuYqWoWeeaeeW20eXYWWWWWmXWaWYaWWWWWaWWWWeeWWeWXWWXWmWWaYaYWWaWWmmfWWWWeWWWWWYWa00aWnWW",
  "WWaeWmYWXYWWWWWoWYWWaaWWaWWmeameWWYXYWWWYYWeeamWWWaWYXWXXWoG0iWWeWmWWYYWiYWWWXWWWWWWqW",
  "mWWYWmWaiWXmYWWnmemWWXmfWWaWWumWWWWWWWWWW80X///p+y////pl+/v/zv////+h/ud/tpolt/+/ls/Z//",
  "xyx///xv/lds////t/xz/zz+gViXZWWWWimXWcWYcWWWWXqWduWeijmeWXWmfWyWWaZaWWWacWmufWWWWeWaYW",
  "YYXr00037A8C9DEF"]
@[expose] def ext_full_watch_push_slow_m6 : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 48)]

@[expose] def hint_full_watch_push_m6 : armIsa.Hints := _decH #[
  "XK581A0A0E0C0C011A140C16000D0610000D061G1D1F0G0G00003H0H000C04022J33010G0E2G0J0J3G0J0J",
  "3H1802080J04022J3H01A001700101681796347589806XN0025475863798105U001981IAG179634758K498",
  "09gT000981IAG179634758K49809gT005747G1IA81X3D98X7G07XA001D47G1XF0X3D9881XDH79X5F6358K4",
  "IA0DXtI002A47G1X3D9881XDH79X5FXF0630ApQ002647G1X3D9881XDH06XQ004747G1XF0X3D9881XDH07ZI",
  "0000kZWWXXuWdWiWWycWZmgWYWWYmW20mWWWWWWXWWXWmWWWWWWeWWa00eaeaWXWmfWmWWmfWWWXWaaeWoG0cX",
  "YWWWuWZWaeWiYafnWWWWWWWW80///lplt/z+/j+l/+/a///z/ttl+gVmimeWYXWoXmWXWxWWWYWeemXr00000"]
@[expose] def ext_full_watch_push_m6 : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_wstack_defrag : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_wstack_defrag : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 48)]

@[expose] def hint_full_watch_push : armIsa.Hints := _decH #[
  "XK581A0A0E0C0C011A140C16000D0610000D061G1D1F0G0G00003H0H000C04022J33010G0E2G0J0J3G0J0J",
  "3H1802080J04022J3H01A001700101681796347589806XN0025475863798105U001981IAG179634758K498",
  "09gT000981IAG179634758K49809gT005747G1IA81X3D98X7G07XA001D47G1XF0X3D9881XDH79X5F6358K4",
  "IA0DXtI002A47G1X3D9881XDH79X5FXF0630ApQ002647G1X3D9881XDH06XQ004747G1XF0X3D9881XDH07ZI",
  "0000kZWWXXuWdWiWWycWZmgWYWWYmW20mWWWWWWXWWXWmWWWWWWeWWa00eaeaWXWmfWmWWmfWWWXWaaeWoG0cX",
  "YWWWuWZWaeWiYafnWWWWWWWW80///lplt/z+/j+l/+/a///z/ttl+gVmimeWYXWoXmWXWxWWWYWeemXr00000"]
@[expose] def ext_full_watch_push : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_watch_pop_c0 : armIsa.Hints := _decH #[
  "X43819090E141109090900003A0A030J05091D050D000005090E190971090E1531050D1803500000004547",
  "Q3D478X1D050000747Q3D478X1DPAX301170100747Q3D478X1DPAX301170100747Q3D478X1DPAX30117010",
  "00eWuWYrgmWWYWdWg20eXYWWWWWmWWWWW00aWnWWWWaeegWWWG0eWmWWYYYWWZYW80d//p+y////plZZ//+ViX",
  "ZWWWWimyyWWX00000"]
@[expose] def ext_full_watch_pop_c0 : List (SigEntry × Nat) := []

@[expose] def hint_full_unwatch_large : armIsa.Hints := _decH #[
  "XO3819090E1C1G1901010100003H0H060F00024A0J010A0A0102031C05430301240E310100000D1A130A0E",
  "210E04040A0A000325416H0H18087000000038H9TF47FG78RHU063118a01036H9TF47FG78RH21360202647",
  "FG78RHH9TF243602006H9TF47FG78RH341360302647FG78RHH9TF21360201647FG78RHH9TF0600000YZtZu",
  "WWWXaWWZuYWWkWXuYo20YWXXWWWWWYeaWWWWWWW00XWWmmWWeWXaYXWaeWWaG0fpXeWqWWWqWXeWWucWWumW80",
  "/////z/+kl//d/ztvz/tl//sVYWXnmWWuWYecYWemWWf00000"]
@[expose] def ext_full_unwatch_large : List (SigEntry × Nat) := []

@[expose] def hint_full_has_bin : armIsa.Hints := _decH #[
  "X14909080203020J090J191A474102010801070707070731010105391C07090J071530017001043X18KAXD",
  "117311013X18KAXD117311000XiWyWZxwmW10aWWWWWWWWWWW00YYYWeWWWWWaqG0aYigXvuWW00/xvx/l/+l/",
  "/mWVacaWmWXmWWl/00000"]
@[expose] def ext_full_has_bin : List (SigEntry × Nat) := []

@[expose] def hint_full_delete_bin_side : armIsa.Hints := _decH #[
  "XB3813030E1D1903030301013F0F0J0A0530031C050101000J1515010E6131313103010E156103053F0F18",
  "08800000002647DD78PFF9RA1360100747DD78PFF9RA64117Y0101747DD78PFF9RA64117Y0103647DD78PF",
  "F9RA060000647DD78PFF9RA1360100647DD78PFF9RA1360100647DD78PFF9RA1360101020G10YZmZyWWyyy",
  "/WWWWYiWdWg20YWWnWWWWWWemWWWWWWW00XWWemWWWWYaemaWfWWWG0fmXiWeiiihXWWXWaWZYW80l//y//kl/",
  "///vtkit/j//+VZWWnmWWWWcenpeWoWWX00000"]
@[expose] def ext_full_delete_bin_side : List (SigEntry × Nat) := []

@[expose] def hint_full_delete_binary : armIsa.Hints := _decH #[
  "Z63819090E1D1109090909093F0F0J00053A041C0509090A0J15150A0E6A3A3A3A090A0E156A09053F0F19",
  "090319090E1D1109090909093F0F0J00053A041C0509090A0J15150A0E6A3A3A3A090A0E156A09053F0F19",
  "0919013A0A1C080A0831011C0301180C08H00000000347635803600284763DD78PFF1R058198a210084763",
  "DD78PFF1R058198a210184763DD78PFF1R058198a21038476358DD78PFF1R008600084763DD78PFF1R0581",
  "98a210084763DD78PFF1R058198a210084763DD78PFF1R058198a210534763580360028476358YUDYO3ZAF",
  "Z01ZC019861008476358YUDYO3ZAFZ01ZC019861018476358YUDYO3ZAFZ01ZC019861038476358YUDYO3ZA",
  "FZ01ZC00860008476358YUDYO3ZAFZ01ZC019861008476358YUDYO3ZAFZ01ZC019861008476358YUDYO3ZA",
  "FZ01ZC019861000XXdWpoWmyW/WWdddduWWWWpWXuYmmYZmZyWWyyy/WWWWYiWdWg20eWWWWWWWWmWaeWWWWWY",
  "aWWWWWWWWWWWYWWnWWWWWWemWWWWWWW00aWWWWWWWWeWYaWWWWWnYaXWYeWWaWWWXWWemWWWWYaemaWfWWWG0Z",
  "mXuWYiWhWYZZZYueWWeXWWumYWWfmXiWeiiihXWWXWaWZYW80ltx/z/////d/xp////+jxpb/xl//t///y//kl",
  "////vtkit/j//+VeaWYWWWWWuWaiWWWWXoaiwWamWWeWWWZWWnmWWWWcenpeWoWWX00000"]
@[expose] def ext_full_delete_binary : List (SigEntry × Nat) := []

@[expose] def hint_full_prioritize_binaries_m6 : armIsa.Hints := _decH #[
  "XE2H0H1G10131B0C270707090934040E060405580A1C052A07512935290A0C0E18081949494907080E1548",
  "07051D059001F001005FB9G7HB0D32FD502016FB9G7HB0D3ID1F601027HFFB9G7HIDD3B0291702008B0D3V",
  "4HFFB9G7HID3791803018B0D3V4HFFB9G7HID3791803039HFFB9G7HIDXT1XVAD3B017901009HFFB9G7HIDX",
  "T1XVAD3B017901009HFFB9G7HIDXT1XVAD3B017901000ZmWZvy+eWWWuzpWpWWdWWr90aYWYaWWWWWXWmWWWe",
  "WWYWWWW00YXWXYWWWWWameWWWbWYfWWYW00XXWmeWWaWeinWXWWZYWW00Xvy/zv/////o/l///r/xb//x/VcZW",
  "YcWWWWWjWmWWWgWawWWaW00000"]
@[expose] def ext_full_prioritize_binaries_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_bin_watches_fid : armIsa.Hints := _decH #["000000000000100000"]
@[expose] def ext_full_sort_bin_watches_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_has_ternary : armIsa.Hints := _decH #[
  "YC5H210C1A0A114I0305100C4005040I29051A0C4A05000I2J0B0A0C0A0B1K1F0000000107070I0I15210A",
  "1C02210U012A3G1C06010G0G0557012A0V0J0A0E0J000J0D000J07070J0404252J0J70017001017I147637",
  "9589HGA24I7S23267963589HI14720I672338XVFXTKY7IXRB7963589H1U8ZG1059YKUXVFXTKY7IXRB79635",
  "89H2049d0200AYKUXVFXTKY7IXRB7963589HZ2G3041Ad0302BZA1YKUXVFXTKY7IXRB7963589HZ2G204Bk02",
  "000vmWbxZXcWWbWWZumWlYXzaD0aaWWWWmWWWWWWWWmWWWWWWaWWWmWW00oYWaWagWXXeWWgWeWWWeWYYWWeeW",
  "X00emeWvXWYXZmWWXuWWdWWyW00/+xx/qoph/zzl//h/l//nklxxv/ll/zVXaaWhjiqWYYmWWqWmWWknmaacWm",
  "mWY00000"]
@[expose] def ext_full_has_ternary : List (SigEntry × Nat) := []

@[expose] def hints : List armIsa.Hints := [hint_full_wsort_sift,
    hint_full_wstack_radix_sort_m6, hint_full_wstack_defrag_m6, hint_full_watch_push_slow_m6,
    hint_full_watch_push_m6, hint_full_wstack_defrag, hint_full_watch_push,
    hint_full_watch_pop_c0, hint_full_unwatch_large, hint_full_has_bin,
    hint_full_delete_bin_side, hint_full_delete_binary, hint_full_prioritize_binaries_m6,
    hint_full_sort_bin_watches_fid, hint_full_has_ternary]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Watch
