module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Backbone

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)),
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X1)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X7)), (XRegOrSp.reg (XReg.X4)),
  (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X6)),
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28)), (XRegOrSp.reg (XReg.X29))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X15))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.flag LeanQbe.T.Arm64.ArmCond.lt),
  (.gpr (XRegOrSp.reg (XReg.X27))), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.flag LeanQbe.T.Arm64.ArmCond.gt), (.gpr (XRegOrSp.reg (XReg.X29))),
  (.gpr (XRegOrSp.reg (XReg.X28))), (.gpr (XRegOrSp.reg (XReg.X25))), (.slot 1 .w64),
  (.slot 4 .w64), (.slot 3 .w64), (.slot 2 .w64), (.slot 6 .w64), (.slot 5 .w64),
  (.slot 0 .w64)]

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

@[expose] def hint_full_backbone_sched_m6 : armIsa.Hints := _decH #[
  "X920111213045514060707081409250A25140926060A2B0C240446140B09090818260A16182B0B0A150C80",
  "4C3A281602A9402004C3A281603A9B403015C3A28160GB2A9502026C3A28160GBM62A96020301A001014C3",
  "A281602A5402015C3A28160XL51A501026C3A28160XL5XRB1A601000XnWumWsWWWiaZXWXiYL0eWaWYaYWXY",
  "WWWWWeaWW00aWYWXYXWanWWeWYaYWe00mWeWWYWWWaWXWWWaW00Zp/x/zxz/sy//l/xtx/lViWaWYaYWfZWWmW",
  "aeaWm00000"]
@[expose] def ext_full_backbone_sched_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_keep_m6 : armIsa.Hints := _decH #[
  "Y2311A04500333140914001400062B0C280804040D30033614180006063003361418000606300336141800",
  "060630033614180006060B060D1C30033614180006060B0CC000000003719A55269302003719A55369B303",
  "014719A55DB269402053719A551B301003719A551B301003719A551B301024719A55XBB0400014719A55XB",
  "B0400014719A55XBB0400014719A55XBB0400034719A55ZGB0400000etcWWWnkkWnkkWnkkWnkiWWWWoYyu5",
  "0aWYWWemWaWWWaWWWaWWWaWWYWYWWeWW00YWXWWaeWYWWWYWWWYWWWYWWfgnWWaWWG0ZYWaWWccWWccWWccWWc",
  "aWWWYWWie00lvuz//tdnx//nx//nx//nx//bWyvtt/+VcdYWWeukaWWkaWWkaWWkaWWw/ZceeWX00000"]
@[expose] def ext_full_backbone_keep_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_unwind_m6 : armIsa.Hints := _decH #[
  "E43161A0E102A2A2A0E202A2A2A0E2000000015614B55A6831A501000XXpiYZcueL0mWWWWWWa00eWWWmWWY",
  "00naWXYeW00/l//+///xVmWWXWWWa00000"]
@[expose] def ext_full_backbone_unwind_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_prop_m6 : armIsa.Hints := _decH #[
  "XT4F0F131G1H1I1J191K2L6A0E2M0N0M0M05050507073000000O0O0C3A18050A0A0C160P0806020E062646",
  "2A0A0C050C150505050C0K0K150505050C0K0K6001B00100AJJHI4B61FHQLDGB39FL92K5AX020134BVKXD7",
  "1530100DX6NJJHI4B61FHQLDGB39FL9VKXD715DY0100GX6NJJHI4BVKXD7XJ061X8MXLOFHQLDGB39FL915GY",
  "m0102HXT5X6NJJHI4BVKXD7XJ061X8MXLOFHQLDGB39FL90HbW00000ZbvmWXWYuWkWZWljgr90aYWWWWXXWeW",
  "WWWWWaWWWW00YXWWWWWmqaaWmWWWYWWWW00XdYkWWWXWimWWWWeXcaXWWWWW00ilu/vz////++dtt+////x///",
  "/VZmdWcYWWWWXXueeXWWWWaWWWW000040123"]
@[expose] def ext_full_backbone_prop_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_analyze_m6 : armIsa.Hints := _decH #[
  "X75612191A100733080K360808350E162505210821081801010523040E1E150E350520050E010101500110",
  "01036H04BFAD9I7OK11601007H04BFAI7OKB2D915701007H04BFAI7OKB2D915701074XU14BFAD910401000",
  "iuWWWWuaiciXgXukgL0eWWWeXWWWWWWWWWWWW00aWWmaWoWfWmWaWqXWW00ceWWWWiWaXaWWWqbW00d/n/+/t+",
  "x/j+//t+tz//VkWXWeXaWoXWWeXeYWW00000"]
@[expose] def ext_full_backbone_analyze_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_backbone_round_m6 : armIsa.Hints := _decH #[
  "Z24Q1B0B1R19151A1S1L16643B040N0A0E2J0T2B0U0P030B0C05253B3B251110050A0E162A2A2A0E080A0C",
  "2V350P0805060E26333A1C2X00C0C2X00B3B042X01C0B35140A0A050C4C6A0B010C1B01050E1A2525250E1",
  "445012A0U2B0A30140505001C150VE068Q4H5X1NLLSDR4VX01360400D5X1LSNLF9FX24H8Q6X3JX4HX5DRPX",
  "6BX73VX01D0307KX1VXCT5X1LSNLF9FX24H8Q6X3JX4HX5DRX2X0XBJPX6BX7Y6BXI3XIX80KmW0000NX1VXCT",
  "5X1LSNLF9FX24H8Q6X3JX4HX5DRX2X0XBJPX6BX7Y6BXI3XIX8X6NY85Y701ANmW0103JX2X0XCT8Q4H5X1NLL",
  "SF9FX26X3JX4HX5DRPX6BX7YOAXI3XIX8Y6B1VJXWW0102GYTVX2X0XCT5X1LSNLF9FX24H8Q6X3JX4HX5DRPX",
  "6BX70G0006FX1VXCT5X1LSNLF9FX24H8Q6X3JX4HX5DRPX6BX71X0F01037aK34H8QaHVLSNLDR167010088Q4",
  "H5X1NLaK3aHVLSDR2B1802027b064HaHVaK3LSNLDR070000Ab06aK34H8Qb21b1BaHVLSNLDR15A010234HaH",
  "VaK31B301017LSNLDR4HaHVaK3b0621B702018bO1LSNLDR4HaHVaK3b061B8010E0404500682317GA368339",
  "32535634AN230BF226222253F42712B0042712B0L2255422A6Q2262222A352271G22710mWXkZZcWmcjmWWZ",
  "uWWtWZXuiWZWWcppWWccWWcjmWYmjdcWWiuWW/rgr50eWWWWWWYWWWWaWWYWWYWeWWnWYaWWWaaWWmYWWWWWWW",
  "WWWWWYYWWWWW00aWWWeWaXWWWeYWWnWWXWaWWemXWWWWYYmWfXWWWeWWWWWYbWXXXWWWW00dXXYWWYamWWXeWW",
  "ZmXWyaWXWWYWvWWYYWWYamWWWaXoWWaeWWWWWW00Z/tx//l/tz///lv/+zz/z/t//k/z////xw//jz///l////",
  "/vn/zzz////VeaWWmWeYWWWmcWXYYWYWeWWnWYWWWWabWWoYWWWmWWWWWckWYYYWWWW0007B0123CD4EFGH"]
@[expose] def ext_full_backbone_round_m6 : List (SigEntry × Nat) :=
  [(("full_backbone_prop_m6", [i64, i64, .bool], [.bool]), 48),
   (("full_backbone_analyze_m6", [i64, i32, i32, i64], [i32]), 0)]

@[expose] def hint_full_backbone_m6 : armIsa.Hints := _decH #[
  "XO3B04111Q1B08080818084N0B0B040B011V0V0V010B0B010505040B0D0V0V44340A04060806041J1S0J04",
  "0515050D351A0A0L0C1818081A0C9001R0010024H5L0200065MT4HCQPNLX011501016MT4HCQPNLX0X2V060",
  "0012CQ4H2TR202005CQ4HPNLX0XDV35RX1503058CQ4HXTTPNLX0XDVXLX1Y0S1R801018CQ4HXTTPNLX0XDVX",
  "LX1Y0S1R80100AXKRCQ4HXTTPNLX0XDVXLX1Y0SY1J1LA010404015006P20G6020C6XT20C60iWWXWWWWWXyW",
  "WWWWqWWYq10YWWWWeYWWemWmeaYWWWWWWWWWWWW80XWWYoaWWeWeWeaYXYWWeWWeWgbeW40aWWWWWWWWWWWWmm",
  "WWWWWW00d//y//uxp//l/l/ltxzxy/l//l/Zrl/NZWWdaiWWmWmWmeaYaZWmWWmWygmW8000B0123CD4EFGH"]
@[expose] def ext_full_backbone_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_prioritize_binaries_m6", [i64], [.bool]), 0),
   (("full_backbone_sched_m6", [i64], [i64]), 0),
   (("full_backbone_keep_m6", [i64, i64], []), 0),
   (("full_backbone_round_m6", [i64, i64, .bool], [i64]), 208),
   (("full_add_unit", [i64, i32], [.bool]), 128)]

@[expose] def hints : List armIsa.Hints := [hint_full_backbone_sched_m6,
    hint_full_backbone_keep_m6, hint_full_backbone_unwind_m6, hint_full_backbone_prop_m6,
    hint_full_backbone_analyze_m6, hint_full_backbone_round_m6, hint_full_backbone_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_prioritize_binaries_m6", [i64], [.bool]), 0),
   (("full_add_unit", [i64, i32], [.bool]), 128)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Backbone
