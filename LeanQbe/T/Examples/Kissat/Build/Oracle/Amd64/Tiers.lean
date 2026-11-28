module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Tiers

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rdi, Reg64.rsi, Reg64.rbx, Reg64.r12, Reg64.r9, Reg64.rbp, Reg64.r13, Reg64.r14,
  Reg64.rdx, Reg64.rax, Reg64.rcx]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rax), (.gpr Reg64.rcx), (.flag CondCode.nc), (.flag CondCode.c), (.gpr Reg64.rdi),
  (.flag CondCode.nz), (.gpr Reg64.rsi), (.gpr Reg64.r14), (.gpr Reg64.r13), (.flag CondCode.z),
  (.gpr Reg64.r9), (.gpr Reg64.rdx), (.gpr Reg64.rbp), (.gpr Reg64.r8), (.gpr Reg64.rbx),
  (.gpr Reg64.r12), (.slot 0 .w64), (.slot 2 .w64)]

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

@[expose] def hint_m6_hdr_init : x64Isa.Hints := _decH #[
  "BC001021330031000100090401440100001441010100144101010014410101000awrgnaXmWbgrD0mYaWWW0",
  "0eXYWWW00YWWmXWWW40X//////dzv///VuYcWWW00000"]
@[expose] def ext_m6_hdr_init : List (SigEntry × Nat) := []

@[expose] def hint_m6_ext_ensure_init : x64Isa.Hints := _decH #["135100000000030804000dN80000"]
@[expose] def ext_m6_ext_ensure_init : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_add_ticks : x64Isa.Hints := _decH #[
  "4452555002000000002445602000254300311042002110klpki3080m40XmWW00Z//t+/NeXW80020"]
@[expose] def ext_m6_hdr_add_ticks : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_sync_legacy_tiers : x64Isa.Hints := _decH #[
  "535101103011014401000252300022000Xeq30804000dx/NaW80010"]
@[expose] def ext_m6_hdr_sync_legacy_tiers : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_recompute_tiers_mode : x64Isa.Hints := _decH #[
  "ZG27150508090A0A0A4B060600000103450C0B01010B06040D010B06040D010B06040D010B06040D010B02",
  "01010B0304060404000404030915060004010B062B060B01000B000B21030B0200000B060E01000E100B00",
  "06026D04040B0B020D04060D040002010341060023007510110301B034F675E0300014EA4F67A810401004",
  "4FA8EA672014020134F67A82603020154F67A8VCEA1B5010154F67A8VCEA2B65020084F67A8VCEAXRBXQ1X",
  "U608000354F67A8VCEG1E5010234F67A84610B3040064F67A8Z6EVCEA416B06040314F01000304021030Z2",
  "2304H22401XR51XeqYzuWWWWZWWWWWWWWWYWWWWWWWWWkWXmW20eWWWeWWWWWWWWWWWWWmWWWWWWWYWeWWW80a",
  "WWWamWWYWWWoWWWWagWaWWWWWXWaWWW40iuWWWXfWWYmWWeXWWWsWmWWWWWcWqoW00dx/t/x/o/dlu//yh///t",
  "tZ/sl////z/pt+tNaWeWaWjWumdWWZqWWWeeyWfmWWWWYWieXe8001525367"]
@[expose] def ext_m6_hdr_recompute_tiers_mode : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_mul", [i64, i64], [i64]), 24)]

@[expose] def hint_m6_hdr_recompute_tiers : x64Isa.Hints := _decH #["2350600030000000XN80000"]
@[expose] def ext_m6_hdr_recompute_tiers : List (SigEntry × Nat) :=
  [(("m6_hdr_recompute_tiers_mode", [i64, i64], []), 88)]

@[expose] def hint_m6_hdr_update_tier_limits : x64Isa.Hints := _decH #[
  "D353003250610010B0B0900010020000000014E010001020200nmy30aW80YW40aWWW00Z+/xx/NXWaaW8000",
  "12"]
@[expose] def ext_m6_hdr_update_tier_limits : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 88)]

@[expose] def hint_m6_hdr_record_used : x64Isa.Hints := _decH #[
  "E452500020609010621030131030130000000024456020001244C002000254300311042002110dWcWi30XW",
  "XWWW80mWmWW40ZWZWW00X+/+/g/NXWXWrW80020"]
@[expose] def ext_m6_hdr_record_used : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_get_tier1 : x64Isa.Hints := _decH #[
  "54525001040300100010024456020001144101010254300311042002110keu308040cWW00Z/z/NYW80020"]
@[expose] def ext_m6_hdr_get_tier1 : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_get_tier2 : x64Isa.Hints := _decH #[
  "6451001310300102445602000254300311042002110da308040ZW00Y//NXWW80020"]
@[expose] def ext_m6_hdr_get_tier2 : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_delaying : x64Isa.Hints := _decH #[
  "5222530050020010001012445602000274300311042002110ZmC0mX00eWH0Xm00X/l+TmX20020"]
@[expose] def ext_m6_hdr_delaying : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_bump_delay : x64Isa.Hints := _decH #[
  "62225300301002000000012445602000274300311042002111E51yZmC0X00H0inm00l+l+TXmX20020"]
@[expose] def ext_m6_hdr_bump_delay : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_reduce_delay : x64Isa.Hints := _decH #[
  "4222530002000000012445602000274300311042002110dZmC0X00H0ZXm00Z//+TX20020"]
@[expose] def ext_m6_hdr_reduce_delay : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_get_watermark : x64Isa.Hints := _decH #[
  "322253020010001012445602000274300311042002110ZmC0X00H0Xm00X/+TX20020"]
@[expose] def ext_m6_hdr_get_watermark : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_set_watermark : x64Isa.Hints := _decH #[
  "2322520000000136B445603000276328300311062822002110ZmC0X00H0Xm00X/+TX20030"]
@[expose] def ext_m6_hdr_set_watermark : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_dr_init : x64Isa.Hints := _decH #[
  "8351000051000000020000000014401000252300022000greaa3080XW40XWW00d///z/NYW80010"]
@[expose] def ext_m6_hdr_dr_init : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_dr_update : x64Isa.Hints := _decH #[
  "YK3510000510000000810001061B0B2501053B06000009060B0B06040D0A0B06040D0A0B06040D0A0B0604",
  "0D0A0B06020B0B06030D040D0D000D0D030915040D0A0B000B200B000B0006000644300275190B0B0B0B70",
  "000000014E01000014E01000324EX31162010224EX3120B2020054EX31Y86Y7BYB405000334EX3GZDH1030",
  "10A02020ZU2310423290230A3230A32202122A02231902089142912A01YI51ZtkWWWWWzuWWWWmWWWWWWWWW",
  "yceigreaa30YWWWWWWWW80YWYWWWWWXYmXWWWWWXWXWWWWWWXW40XpcaWWWWiuYWeWWbmaWWWWWeiWWWWWXWW0",
  "0////tx/x////zzu/zp////v/zl/////z/NeaWaWWWWYYdWYiWWWWcWYmWWWWWYW800312"]
@[expose] def ext_m6_hdr_dr_update : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_add", [i64, i64], [i64]), 0)]

@[expose] def hint_m6_hdr_dr_allow : x64Isa.Hints := _decH #[
  "C35100009250031360503191320010001001440100035230002200L231A0dkia3080mmWXW40ZcWW00Zsw/+",
  "z/NfbWXYW80020"]
@[expose] def ext_m6_hdr_dr_allow : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_div", [i64, i64], [i64]), 24)]

@[expose] def hints : List x64Isa.Hints := [hint_m6_hdr_init, hint_m6_ext_ensure_init,
    hint_m6_hdr_add_ticks, hint_m6_hdr_sync_legacy_tiers, hint_m6_hdr_recompute_tiers_mode,
    hint_m6_hdr_recompute_tiers, hint_m6_hdr_update_tier_limits, hint_m6_hdr_record_used,
    hint_m6_hdr_get_tier1, hint_m6_hdr_get_tier2, hint_m6_hdr_delaying, hint_m6_hdr_bump_delay,
    hint_m6_hdr_reduce_delay, hint_m6_hdr_get_watermark, hint_m6_hdr_set_watermark,
    hint_m6_hdr_dr_init, hint_m6_hdr_dr_update, hint_m6_hdr_dr_allow]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_add", [i64, i64], [i64]), 0),
   (("f64u_div", [i64, i64], [i64]), 24)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Tiers
