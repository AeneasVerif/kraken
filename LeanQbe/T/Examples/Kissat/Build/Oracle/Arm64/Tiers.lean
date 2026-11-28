module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Tiers

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X10)), (XRegOrSp.reg (XReg.X9)), (XRegOrSp.reg (XReg.X6)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X3))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.slot 1 .w64), (.slot 0 .w64), (.slot 2 .w64)]

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

@[expose] def hint_m6_hdr_init : armIsa.Hints := _decH #[
  "O1011017201031432041101020101010101010101010112054025045020000250451220100250451220100",
  "2504512201000mWWWaXmWbgr00mYaWWW00eXYWWW00YWWmXWWW40X//////dzv///VuYcWWW00000"]
@[expose] def ext_m6_hdr_init : List (SigEntry × Nat) := []

@[expose] def hint_m6_ext_ensure_init : armIsa.Hints := _decH #[
  "3110106100000000000804000dN80000"]
@[expose] def ext_m6_ext_ensure_init : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_add_ticks : armIsa.Hints := _decH #[
  "F2202061206120212060230010502012000000002514502000254310301042012100ZnYa0080m40XmWW00Z",
  "//t+/NeXW80020"]
@[expose] def ext_m6_hdr_add_ticks : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_sync_legacy_tiers : armIsa.Hints := _decH #[
  "91101060101020207021014501000252301022100XeW00804000dx/NaW80010"]
@[expose] def ext_m6_hdr_sync_legacy_tiers : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_recompute_tiers_mode : armIsa.Hints := _decH #[
  "ZK28050606090A0B0B0B400C0D01010204460E0305050203000C050203000C050203000C050203000C0502",
  "03050502040C000C0C010C0C070A16000301050200220005050102010521040203050503020F01050F1500",
  "010C0D6G0H0D00000D0G0H0C0G0H010D0204420C0527056506050501010701B034I68510300014EB4I68A9",
  "114010044IA9EB682124020134I68A92C53020154I68A9VEEB155010154I68A9VEEB2205020084I68A9VEE",
  "BXR2XQ5XU008000354I68A9VJEK1F5010234I68A94C2153040064I68A9Z6FVEEB42C016040314I01000902",
  "0214230002200YS6323314305E2232022320223202250122410XeWWzuWWWWZWWWWWWWWWYWWWWWWWWWkWXmW",
  "00eWWWeWWWWWWWWWWWWWmWWWWWWWYWeWWW80aWWWamWWYWWWoWWWWagWaWWWWWXWaWWW40iuWWWXfWWcmWWeXW",
  "WWsWmWWWXWcWqoW00dx/t/x/o/alu/mih//udtZ/seeeeez/od+tNaWeWaWjWxmdWlpqWWdueyWftttttYWjuX",
  "e8003226"]
@[expose] def ext_m6_hdr_recompute_tiers_mode : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_mul", [i64, i64], [i64]), 0)]

@[expose] def hint_m6_hdr_recompute_tiers : armIsa.Hints := _decH #["321060100010000000XN80000"]
@[expose] def ext_m6_hdr_recompute_tiers : List (SigEntry × Nat) :=
  [(("m6_hdr_recompute_tiers_mode", [i64, i64], []), 48)]

@[expose] def hint_m6_hdr_update_tier_limits : armIsa.Hints := _decH #[
  "J1505060205110415060101050400000A05010520000000014I01000302021H2307A22700mm00aW80YW40a",
  "WWW00Z+pxx/NXiaaW800112"]
@[expose] def ext_m6_hdr_update_tier_limits : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("m6_hdr_recompute_tiers_mode", [i64, i64], []), 48)]

@[expose] def hint_m6_hdr_record_used : armIsa.Hints := _decH #[
  "H22020612060203010A000120040031040130000000024551020001245C202000254301310042102010dWc",
  "Wa00XWXWWW80mWmWW40ZWZWW00X+/+/g/NXWXWrW80020"]
@[expose] def ext_m6_hdr_record_used : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_get_tier1 : armIsa.Hints := _decH #[
  "922000611060102054530015001003624551030001145111010256317301320062712102020kWe008040cW",
  "W00Z/z/NYW80030"]
@[expose] def ext_m6_hdr_get_tier1 : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_get_tier2 : armIsa.Hints := _decH #[
  "9220206020201350705102455102000254301310042102010dW008040ZW00Y//NXWW80020"]
@[expose] def ext_m6_hdr_get_tier2 : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_delaying : armIsa.Hints := _decH #[
  "72302020632060220015001012455102000274301310042102010Zm00mX00eWH0Xm00X/l+TmX20020"]
@[expose] def ext_m6_hdr_delaying : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_bump_delay : armIsa.Hints := _decH #[
  "823020206320400022000000012455102000274301310042102010yZm00X00H0inm00l+l+TXmX20020"]
@[expose] def ext_m6_hdr_bump_delay : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_reduce_delay : armIsa.Hints := _decH #[
  "62302020632022000000012455102000274301310042102010dZm00X00H0ZXm00Z//+TX20020"]
@[expose] def ext_m6_hdr_reduce_delay : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_get_watermark : armIsa.Hints := _decH #[
  "5230202063520015001012455102000274301310042102010Zm00X00H0Xm00X/+TX20020"]
@[expose] def ext_m6_hdr_get_watermark : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_set_watermark : armIsa.Hints := _decH #[
  "433000006200000001362455103000276327301310062722102010Zm00X00H0Xm00X/+TX20030"]
@[expose] def ext_m6_hdr_set_watermark : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_dr_init : armIsa.Hints := _decH #[
  "H110106010202061202020201010101010520000000014501000252301022100aW0080XW40XWm00d///z/N",
  "YW80010"]
@[expose] def ext_m6_hdr_dr_init : List (SigEntry × Nat) := [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_m6_hdr_dr_update : armIsa.Hints := _decH #[
  "YV1505060501010611010101050505050505100105010C110112060206310305050A03010100030C0G0100",
  "030C0G0100030C0G0100030C0G010003010100040G0C0G0G050G0G070A160C030G01050125010101050005",
  "01453003761A0101010170000000014I01000014I01000324IX32112010224IX322512020054IX32Y80Y71",
  "YBC05000334IX3KZDL153010E02021ZU231142328023070200102001123070200102001122021227022311",
  "04001212142112700ZtkWWWWWzuWWWWmWWWWWWWWWyYeaWWWaW00YWWWWWWWW80YWYWWWWWXYmXWWWWWXWXWWW",
  "WWWXW40XpcaWWWWiuYWeWWbmaWWWWeeiWYWWWXWm00////tx/x///+Xzu/zoYYYYXdzl/////z/NeaWaWWWX+Y",
  "dWYjzzzz+uYmWWWWWYW800312"]
@[expose] def ext_m6_hdr_dr_update : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_add", [i64, i64], [i64]), 0)]

@[expose] def hint_m6_hdr_dr_allow : armIsa.Hints := _decH #[
  "G1101060101010A110601323106041A1420015001001450100035230102210L23170dkaW0080mmWXW40ZcW",
  "m00Zsw/+z/NfbWXYW80020"]
@[expose] def ext_m6_hdr_dr_allow : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_div", [i64, i64], [i64]), 0)]

@[expose] def hints : List armIsa.Hints := [hint_m6_hdr_init, hint_m6_ext_ensure_init,
    hint_m6_hdr_add_ticks, hint_m6_hdr_sync_legacy_tiers, hint_m6_hdr_recompute_tiers_mode,
    hint_m6_hdr_recompute_tiers, hint_m6_hdr_update_tier_limits, hint_m6_hdr_record_used,
    hint_m6_hdr_get_tier1, hint_m6_hdr_get_tier2, hint_m6_hdr_delaying, hint_m6_hdr_bump_delay,
    hint_m6_hdr_reduce_delay, hint_m6_hdr_get_watermark, hint_m6_hdr_set_watermark,
    hint_m6_hdr_dr_init, hint_m6_hdr_dr_update, hint_m6_hdr_dr_allow]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_add", [i64, i64], [i64]), 0),
   (("f64u_div", [i64, i64], [i64]), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Tiers
