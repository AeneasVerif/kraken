module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Dense

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)),
  (XRegOrSp.reg (XReg.X26)), (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.flag LeanQbe.T.Arm64.ArmCond.gt),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X27))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.flag LeanQbe.T.Arm64.ArmCond.ge), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X14))),
  (.gpr (XRegOrSp.reg (XReg.X15))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.flag LeanQbe.T.Arm64.ArmCond.lt), (.flag LeanQbe.T.Arm64.ArmCond.le)]

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

@[expose] def hint_full_dense_occ_cnt_fid : armIsa.Hints := _decH #[
  "R400102020202023000031400052617010201082922170201010605200160010336AM4N0216302000hWWsX",
  "Xu10eWWmWW00mWamWeeW00YXWaYWWuK0X+e/sn/dl/VXtWfkWumW00000"]
@[expose] def ext_full_dense_occ_cnt_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_enter_dense_ex_fid : armIsa.Hints := _decH #[
  "aN360716071607160B160716070607161A0518070607371818160716070607161105180706075C1D1E0E86",
  "071F0F023G18031A260609160H410109110H06090206060G060607060F0I0J4101060603060A0715020005",
  "020200051K0L040K0K0000320200070A035A060B090K032K083K0802060306080A0352000B092B091M0A01",
  "0M06052032020605170M192207060901060M0M0M1M0605O00160010024N5G02000334N5GHB163010134N5G",
  "HB03000234N5GHB03000524N5G02000424N5G02000224N5G02000544NY3CY8EY5D1M401015Y3CY8EY5D4NY",
  "JM0500028Y3CY8EY5D4NYJMYQGYLFYM208b000074NYJMYQGY3CY8EY5DYLF0740009Y3CY8EY5D4NYJMYQGYL",
  "FYM2YVA169b0102AY3CY8EY5D4NYJMYQGYLFYM2YVAZ860Ab000494NZTIZUJZSFYJMYQGY3CY8EY5D1B9X610",
  "0A4NZTIZUJZSFYJMYQGY3CY8EY5DZVB0AX600014N010001B4NZTIZUJZSFYJMYQGY3CY8EY5DZVBa310BXX60",
  "02E4NZTIZUJZSFYJMYQGY3CY8EY5DZVBa41a31a9Aa860EZX6000E4NZTIZUJZSFYJMYQGY3CY8EY5DZVBa41a",
  "31a9Aa860EZX6007I4NZTIZUJZSFYJMYQGY3CY8EY5DZVBb10aMLa41aV2aN4a31a9Aa860IXiX60094Y3CY8E",
  "Y5D4N1M401136cFAcG1Y3CY8EY5D4N16601006Y3CY8EY5D4Nd16cG1060001040010230ZWYXxWWWWWWdiWWW",
  "WycWWXxWXuWWWWWWWdWWWWWYXuaZeYyWd/beYebWWWYmWnWWXeWWWqWafYa10XWWWmeWWWWWaWnWWXYXWaXWmm",
  "WWeWWWaWWeqWWWYWWmWmWXWYeWWWWWXWWWWWWWWWWYaWWWWaWXWWWW80mWWeaamWeWYWWmWWnWmYWmeeWWamWW",
  "WmaaYaWWXWWeeeWmmXaWWmWWWWWWWaqeaYafXWWXbYXWnWem40mXWWavWWWWWWZaeWWWiYaWWvYaumWWWWWYZW",
  "WYWWWWuWXWWimWWWWWWWWWWWWWWWWWWWWWWWWWWW00d+/+lltsXxd/v/+l/+j+/x+/dd//ol//+/ttxt//z//d",
  "ll++/zt/+////////sdltxtjz//znxz+z/k/NXWXmmef+auWcWXmWXoXWaXWuuWWjmWWXWeeaeWWYWWummXXWY",
  "eWXWWWWWWWWfumeaeoYWWYkaYXYWnW8000A24056789AB"]
@[expose] def ext_full_enter_dense_ex_fid : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_arena_sweep_m6", [i64], [i64]), 384),
   (("full_sweep_bins_m6cf", [i64], []), 96),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hint_full_enter_dense : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_enter_dense : List (SigEntry × Nat) :=
  [(("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 656)]

@[expose] def hint_full_rebuild_watches_nosort_fid : armIsa.Hints := _decH #[
  "A38080828082808081808400160010226N4B02000314B01000224BFN0200030204322023H20230eXW10YWW",
  "We00gXgYmb8000//hzZw/qFqYybWhG000224"]
@[expose] def ext_full_rebuild_watches_nosort_fid : List (SigEntry × Nat) :=
  [(("full_arena_sweep_m6", [i64], [i64]), 384),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560)]

@[expose] def hint_full_rebuild_watches : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_rebuild_watches : List (SigEntry × Nat) :=
  [(("full_rebuild_watches_nosort_fid", [i64], [i64]), 592)]

@[expose] def hint_full_m6_dense_prop_lit : armIsa.Hints := _decH #[
  "aA2G1K0K0G0O1P110Q1A1R1N01010101013S0S0SD93A00170O2T0U0T010A090V0V0X03L17050L01090X16A",
  "0A09120H08000321090X001010L0928082108010102030200030210070X0040L0X10T000V4217020702020",
  "827020242020202220121010931010O120H0X202020403040L03041L070B0X10T0U0V0L0X0441704070404",
  "08270A0A4A0A0A0A2A0A21010959E0016001020000000746AGDP9KMNKRX1S1170100746AGDP9KMNKRX1S11",
  "70107BXRU46AGDP9KMNKRX1SYALY1VY2X00BXW00009XST46XRUAGDP9KMNKRX1S20A90200EXRU46AGDP9KMN",
  "KRX1SYALY1VY2X0XSTYDX1Y6L3041EfW0300FXRU46AGDP9KMNKRX1SYALY1VY2X0XSTYDX1Y6LYG1204FfW02",
  "078XRU46AGDP9KMNKRX1S080005GXRU46AGDP9KMNKRX1SZ7AZSX1ZTTZF1ZU0ZRLZQ4ZPX00GYW0002FXRU46",
  "AGDP9KMNKRX1SZ7AZSX1ZTTZF1ZU0ZRLZQ40FYW00058XK046AGDP9KMNKRX1S080003HXK046AGDP9KMNKRX1",
  "Sb51bQUbRVbD2bSLbPTbOX1bNBXJA0HYYe0002FXK046AGDP9KMNKRX1Sb51bQUbRVbD2bSLbPTbOX10FYe000",
  "1020010XgmWZZWgucWWYxWWeWWaWXgWWiiXhWuWWhiWXWWXmWWWWWYXuWbuWcYid//Zmbeq20YWWYWWWWWWWma",
  "eWWWWWWWWWWeWWWWWWYWnWWWWWWeaYWYWYWmWWWWWWWWWWWWWWWW00XWWXWWWWWWWeYaWWXXYYnWWWaWWWWWWX",
  "WemWWaaeaYnWXWneeWneWeWqWeWWWWWYX00XWWWWWWWWfWWWWeWWWWWWaWWWWWWWXaWWWXWWWaWWWWWueWvWYW",
  "aWWWfnWWW00dz//z//////llxt//zzxuyl//t/////zz/k///ttltwz/y+ill+jl/Z+t/l/////xzVYWWYWWWW",
  "WWmmaeWWYYadZmWWeWWWWWYYWnWWWeemebYWZXpmmXomWyXeWmWWWWWaY00003240"]
@[expose] def ext_full_m6_dense_prop_lit : List (SigEntry × Nat) := []

@[expose] def hint_full_m6_dense_prop : armIsa.Hints := _decH #[
  "C2B3601050608010806082106200160010024N6B020001020230XmWWT0XWXWm00me00mWW00l/sxlVfam000",
  "0224"]
@[expose] def ext_full_m6_dense_prop : List (SigEntry × Nat) :=
  [(("full_m6_dense_prop_lit", [i64, i32], [.bool]), 32)]

@[expose] def hint_full_dense_prop_unit_m7 : armIsa.Hints := _decH #[
  "Z736061N0F0O160X31C1G1I01010606060A0A3J0J0J19310E170O220E0206060P173L0K0761220H0800032",
  "A090P06060L060928080P06060L062901260X20819290606060101340404193A01170O2A060A0L0L0K1732",
  "100721210H034A2A0H01090K01010201090919I0016001026ANLIJG4BHCBF06000074BHCBFX2JANLIJG1A7",
  "010074BHCBFX2JANLIJG1A70104BXGE4BHCBFX2JANLIJGXQLXJ6XKP0BXe0000B4BXGEHCBFX2JANLIJGXQLX",
  "J6XKP204BXe0200CXGE4BHCBFX2JANLIJGXQLXJ6XKPXRK304ACXe0302DXGE4BHCBFX2JANLIJGXQLXJ6XKPX",
  "RKXVA204DXe02038XGE4BHCBFX2JANLIJG0800018XGE4BHCBFX2JANLIJG08000900000005ANLIJGZM44B16",
  "501005ANLIJGZM44B16501049a46ANLIJGZM44BaE2a7La8K09g00006a46ANLIJGZM44B060000Aa46ANLIJG",
  "ZM44BaE2a7La8KaG011Ag01056a46ANLIJGZM44B0600016a46ANLIJGZM44B060001040810430ZkWcuhoWuf",
  "mnuWYWWcWYWWWWWWWWXtWkeZXcYdWYqe90aXXWWaWWWWYWWWWWWWWXWfaWXWeWeaWWmXWWWWWWWWWWWWWW00YW",
  "mmWYeWYmXWaWYmXWWWmaYmWmWWbYWWeeqWYWmWgWaWWWXY00XWWXcWYeXmeeWmaumWWWYWWWmWWaWWWWpWcXXW",
  "YWpYmWW00lx++//vl/w/z/t/w/z//+/tu/+///nx//dct/x+//h/t///zxVaXXWWcmWbWYWeWbWYWWXWedWXWW",
  "WkaWWuveWaXWWqWeWWWYa0000824056789"]
@[expose] def ext_full_dense_prop_unit_m7 : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 128)]

@[expose] def hint_full_dense_flush_units_m7 : armIsa.Hints := _decH #[
  "D2G1631050108210B110O060608300160010024N6G162010024NB6020001020230ZWXL0XWem00ae00XWW00",
  "Xk//tlVnWWem00003240"]
@[expose] def ext_full_dense_flush_units_m7 : List (SigEntry × Nat) :=
  [(("full_dense_prop_unit_m7", [i64, i32], [.bool]), 208)]

@[expose] def hint_full_watch_large_clauses_fid : armIsa.Hints := _decH #[
  "c82J1N1I160D81050L0L003K0E0A0E06052432020605170619220706090A060606061M1803060K060O2621",
  "0H08063A0A063606060A1L60240H080030000036060600150P0A010917063136210H08063A0A063606060A",
  "70240H080030000036060600150P0A01091706315F3C0A0F06060302040715060105060601051K00010K0K",
  "06063L0L0607040356020K032K083K080L0603060804035L062F0C06060302000715060105060601051L0A",
  "010L0L060634040607000356020L032L083L0804060306080003540643R000000005AI8N6JDD4B1G50101B",
  "4BVE6JLGPLAI8NDDM1UKQ016BXm2113CX0AM1AI8N6JLGDDUKQ04BVEPL16CXi0100C4BVE6JLGPLAI8NDDM1U",
  "KQ0XH60CXm20027XVMAI8N6JDD4BLG07000384BXVM6JLGVEAI8NDD08G001AAI8N6JLGUK4BVEXVMDDPL1AAc",
  "G102AAI8NYUL4BVE6JLGUKXVMDD1PAaG110AAI8NYUL6JLGUK4BVEXVMDD3PA1Ab0300DAI8NYUL6JLGUK4BVE",
  "XVMDDZ11Z0AYVP10Db0103AAI8NYUL4BVE6JLGUKXVMDD0AaG001AAI8NYUL4BVE6JLGUKXVMDD1AAaG10294B",
  "XVM6JLGVEAI8NDDYUL1P9G110AAI8NYUL4BVE6JLGUKXVMDD31PAAaG300DAI8NYUL4BVE6JLGUKXVMDDaU1b0",
  "AaVP10DaG104A4BXVM6JLGVEcECAI8NDDcAF0AnG00014B010001B4BXVM6JLGVEcECAI8NDDcAFcFA0BXnG00",
  "2E4BXVM6JLGVEcECAI8NDDcAFcGFcFAcL4cK20EZnG000E4BXVM6JLGVEcECAI8NDDcAFcGFcFAcL4cK20EZnG",
  "006I4BXVM6JLGVEcECAI8NDDcAFdD6d20cGFdBLd31cFAcL4cK20IXinG00714B010001AXVMAI8N6JDD4BLGc",
  "ECeJFVE0Ay0002DXVMAI8N6JDD4BLGeKCVEeJFcECeP0eO20DXy0000DXVMAI8N6JDD4BLGeKCVEeJFcECeP0e",
  "O20DXy0006HXVMAI8N6JDD4BLGfH6f6AeKCfF4VEf71eJFcECeP0eO20Hxm0001020430YfWWzmWWWZmuWZsWZ",
  "mWWWWWWWYWXxWWWWdXmWdiWdWWWWWWWWkxmkWWWkXuZkWyZmcydWWWdWyXtWdWyXsWWaWWXmXWzmZmX/oL0aWW",
  "aeaWmaYWWWmWWWeWWnWWWeWWemeXWeaWWXWWWWmWXYWWWWWWemWWWWWWWWWWWWWaeWWWWWWWWWWWWeamWWeaWW",
  "WWWWmWW00mWWWWYaYWeYXWWWfWWWXWeeaeWWWWaeaWmaYWWWoWWWYWmmemWWWWaeWWWXeWWWWYmWWYaWWWWqWW",
  "WWWqWaYeWWaYYeWaWWeWW00inWWWXmemXoafnWWWWWWaWWWvYWWWZWnWZaepYWWWWWWecfmcWWYdWyXcakXuYi",
  "ZWWXZmkWpXZmkWoZWWWeWmWYimXoWWW00k/////vtx/lxy///a///z/lltl////plt+/tv//+f///x++/k////",
  "/ta///yl////u///xol//+d////+d/pxl/dtxxWzp//l//VXWWWWWceaWmaZWWWxWWWYWmmemWWWWimeXWecWW",
  "XsWWWaXXWnWWWWWexWWWZmWWWWdWWWajmWWXuWWWWXuWiamWueaa/YiWWmWW0000A24056789AB"]
@[expose] def ext_full_watch_large_clauses_fid : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144)]

@[expose] def hints : List armIsa.Hints := [hint_full_dense_occ_cnt_fid,
    hint_full_enter_dense_ex_fid, hint_full_enter_dense, hint_full_rebuild_watches_nosort_fid,
    hint_full_rebuild_watches, hint_full_m6_dense_prop_lit, hint_full_m6_dense_prop,
    hint_full_dense_prop_unit_m7, hint_full_dense_flush_units_m7,
    hint_full_watch_large_clauses_fid]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_arena_sweep_m6", [i64], [i64]), 384),
   (("full_sweep_bins_m6cf", [i64], []), 96),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 144),
   (("full_add_unit", [i64, i32], [.bool]), 128)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Dense
