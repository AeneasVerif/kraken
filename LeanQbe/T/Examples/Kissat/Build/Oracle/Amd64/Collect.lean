module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Collect

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r14, Reg64.rdi, Reg64.rsi, Reg64.rax, Reg64.rdx, Reg64.rbx, Reg64.rbp, Reg64.r12,
  Reg64.r13, Reg64.r15, Reg64.rcx, Reg64.r8, Reg64.r9]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rdx), (.flag CondCode.g), (.flag CondCode.z), (.gpr Reg64.rax), (.gpr Reg64.rsi),
  (.gpr Reg64.r15), (.gpr Reg64.rdi), (.gpr Reg64.rcx), (.gpr Reg64.r8), (.flag CondCode.nz),
  (.flag CondCode.nc), (.flag CondCode.c), (.gpr Reg64.r9), (.flag CondCode.l),
  (.gpr Reg64.rbp), (.gpr Reg64.r12), (.gpr Reg64.rbx), (.gpr Reg64.r13), (.gpr Reg64.r14),
  (.slot 6 .w64), (.slot 3 .w64), (.slot 4 .w64), (.slot 5 .w64), (.slot 2 .w64),
  (.slot 1 .w64), (.slot 0 .w64), (.slot 8 .w64), (.slot 7 .w64), (.slot 11 .w64),
  (.slot 10 .w64), (.slot 9 .w64)]

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

@[expose] def hint_full_lit_rank_m6 : x64Isa.Hints := _decH #[
  "D3021020000230300002303030310013001000iXm6000X80YcWu10///yFZG0000"]
@[expose] def ext_full_lit_rank_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_sweep_bins_range_m6 : x64Isa.Hints := _decH #[
  "YI340415131617183303090AA3000A1B330B2943033C0C020332210D1C030B4E19000B032F090F0B5G130F",
  "0F0B000032210D100B320B0009000F0B4G0F0B000900132B1B030AA3000A1B330B03031C1H0B0H0BK00000",
  "000A4I84A5NJCKE6ELG75MI80A0000A4I84I8A5NJCKE6ELG75M13A0100A4I84I8A5NJCKE6ELG75M13A0100",
  "A4I84I8A5NJCKE6ELG75M13A0105A4I84A5NJCKE6ELG75MI81HA0102DXMN4IXHHI884A5NJCKG75ME6ELXRC",
  "1OD0104D4I84A5NJCKE6ELXHHY7CXMNG75MI81GD0100EA5NJCK84G75MY7C4IXHHY8PI8Y6OELXMN23GE0201",
  "E4IXHHI8Y8P84Y6OA5NJCKG75MY7CELXMN23GE0201F4IXHHI8Y8P84Y6OA5NJCKG75MY7CELXMNYA31GF0103",
  "IYBG4IXHHI8Y8P84Y6OA5NJCKG75MY7CELXMNYA3Z2FYEE10IaWW0105F4IXHHI8Y8P84Y6OA5NJCKG75MY7CE",
  "LXMNYA31GF0100HYBG4IXHHI8Y8P84Y6OA5NJCKG75MY7CELXMNYA3Z2F0H0002I4IXHHI8Y8P84Y6OA5NJCKG",
  "75MY7CELXMNYA3YBGYEEZ2F0IYWW0004H4IXHHI8Y8P84Y6OA5NJCKG75MY7CELXMNYA3YBGYEE0HYWW0004E4",
  "I84A5NJCKE6ELG75MI8XHHY7CaBGXMN0E0000E4I84A5NJCKE6ELXHHY7CaBGXMNG75MI813E0100E4I84A5NJ",
  "CKE6ELXHHY7CaBGXMNG75MI813E0100E4I84A5NJCKE6ELXHHY7CaBGXMNG75MI813E010J020010235272341",
  "6233322363XQ23234224314130313541303132413031304131313041313130225222303XC2213M2210I224",
  "0N2214XC22320YmWuWYrgsWWWWWXpWWWdWWWuyWWzmXmYuWWcdWyyZWiWXgrhWXwr90YXWWeXYWWWWWnWaeWWe",
  "YameWaYWeWWaeWWWWXWmWWWWaWnWWWWWmWW00XWmWaWnWWWWaemYaWWaXYeaWnXWaWWYaXaWmaeeaWWaYWemWW",
  "WYeWW00XYWeWmWWYYWWWYWnWWWXWWWWcWWinWmWeWWWXWieWWaWeWWXWWWW00Xy+l/p+y////pk/xt//tzxlt+",
  "fz/t//utyt+/ollt//tv/kl///vl//VZXmWiXZWWWWinWaeWWeYameXsYWeWWdeZeXWjmmeWWecWnmWWWcmWW0",
  "0076567809"]
@[expose] def ext_full_sweep_bins_range_m6 : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 136)]

@[expose] def hint_full_rewatch_range_m6 : x64Isa.Hints := _decH #[
  "bK4I1G1H236B4E0A330321020303280803032303030314043C3C0C21020C0C2C0C0C0C2C0C0C0C1B060803",
  "0B1903063833032102030328080303230303034C3C0C21020C0C2C0C0C0C2C0C0C0C1B0608030B19030638",
  "33243600050703030A0308091B080C0B08080C0B280C28083C0C0809080A58030C0A324203030A0302030A",
  "5308200403030A0307091B080C0B08080C0B280C27073C0C07090C0A56030E070B0C0A324203030A030203",
  "0A53070E070B2E070BO00130010074FCHAG8IF3FQ6M177010184FCHAG8IFQ6MREN708Y00028CHAG8IN7RE4",
  "FFQ6M188G1029CHAGXM44FN78IREFQ6M169Y01009CHAGXM48IN7RE4FFQ6M36839X0300CCHAGXM48IN7RE4F",
  "FQ6MXP3XO8XN61CCX01039CHAGXM44FN78IREFQ6M09Y00019CHAGXM44FN78IREFQ6M189Y010294FCHAG8IF",
  "Q6MREN7XM4169Y01009CHAGXM44FN78IREFQ6M33689Y0300CCHAGXM44FN78IREFQ6MZO3ZQ8ZP61CCY0104D",
  "4FCHAG8IFQ6Mb4NREbD5bB6bBOb74b7P0Ddq000014F010001E4FCHAG8IFQ6Mb4NREbD5bB6bBOb74b7PbC00",
  "Edq0002H4FCHAG8IFQ6Mb4NREbD5bB6bBOb74b7PbE7bC0bJJbI30Hdq0000H4FCHAG8IFQ6Mb4NREbD5bB6bB",
  "Ob74b7PbE7bC0bJJbI30Hdq0006M4FCHAG8IFQ6Mb4NREbD5bB6bBOb74b7PcB8c0KbE7c9Rc1Cc1LbC0bJJbI",
  "30MYdq000784F8ICHAGFQ6Mb4NRE08a000014F010001CCHAG8IFQ6Mb4NRE4FbB6bBOdH0bD50Cw0002FCHAG",
  "8IFQ6Mb4NRE4FdI4bD5dH0dM3bB6bBOdN70FiY0000FCHAG8IFQ6Mb4NRE4FdI4bD5dH0dM3bB6bBOdN70FiY0",
  "007KCHAG8IFQ6Mb4NRE4FeF7e48dI4eDLbD5e5Ce5PdH0bB6bBOdNKdM30KcYY000S040A2071F4383354bH23",
  "0232311223236236B34211220H42112206233B4434C2C30237C322B6522B452243B22C4C2243A22C652234",
  "5224364211220X9233A4230C0234C322A3522A0M22C0N22C3522300YeWmWWkuWWWZuyWWXxWXvoWWWWWWXWW",
  "zmWWWdnuWZsWZpaWWWWWWZskXuWWWuZWiyWuZWiydWWWZWiXpmWuZWiyZm/sL0XWYaWWYaYWeYXXWWWeWWWaWW",
  "eqWWaWWaeaWmaYWWWmWWWeWWnWWWWWWWnWWWWWWWWWWWWWWYaWWWWWWWWWWWWXWWWW00mWYWWXYXWaXWmmWWam",
  "WWWmaaYaWWWWYaYWeYXWWWfWWWXWeeaeWWWWWemWWWYmWWWWYmWWXYWWWWgWWWWWYmWmXWW00aWWmcemWWWuae",
  "aWvYaumWWWWWYWWWinWWWXmemXoafnWWWWWWaXocWyWWaiXmYkaiXmYiZmWWnmcWfvaiXmYiXmWW00/+l/v//y",
  "xz/tz+kl//ol//+/ttxt////vtx/lxy///a///z/lltl/////kf///u/////u///zvd///Z/////u/+/z//VXm",
  "WcWWZaYWeYXnmWWjmWWXWeeaeWWWWceaWmaZWWWxWWWYWmmemWWWWWnsWWWdWWWWWdWWWYcuWWWyWWWWWdWXWY",
  "WW00096567809"]
@[expose] def ext_full_rewatch_range_m6 : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hint_full_rewatch_arena_m6 : x64Isa.Hints := _decH #["00102042000000000300000"]
@[expose] def ext_full_rewatch_arena_m6 : List (SigEntry × Nat) :=
  [(("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 344)]

@[expose] def hint_full_sweep_bins_m6cf : x64Isa.Hints := _decH #[
  "YH2C0C13171617143303090AA3000A1B330B29430338080203322113322D1300080B4F190G03030B000032",
  "21150B0000322D12000B32030B0309031G030B4E0G2B1B030AA3000A1B330B020303181H0B0H0BM0000000",
  "094I7CD6DK9NBPMJF7H409000094I7CH4D6DK9NBPMJF7139010094I7CH4D6DK9NBPMJF7139010094I7CH4D",
  "6DK9NBPMJF7139010594I7CD6DK9NBPMJF7H41H90102DXLLH47C9NB0BPMJF7D6DKXGH4IXQ813D0102CXLLH",
  "47C9NBPMJF7D6DKXGH4IXQ81MC0104CD6DKXGHXLLYG8F74I7C9NBPMJH41EC0100E4IXGHYEOH47CYFRYDM9N",
  "BPMJF7YG8DKXLL2GEE0201EH4YEO7CYFRYDM9NBPMJF7YG8DKXGHXLL4I2GEE0201IYJE9NBP7CMJF7YG8DKXG",
  "HXLLYIG4IYQ3YMFYEOH4YFRYDM10IeW0103IYJE9NBP7CMJF7YG8DKXGHXLLYIG4IYQ3YMFYEOH4YFRYDM10Ie",
  "W0105HYJEH4YEO7CYFRYDM9NBPMJF7YG8DKXGHXLL4IYIGYQ30H0000IH4YEO7CYFRYDM9NBPMJF7YG8DKXGHX",
  "LL4IYIGYJEYMFYQ30IYWW0005FH4YEO7CYFRYDM9NBPMJF7YG8DKXGHXLL4IYIG1EF0102HH4YEO7CYFRYDM9N",
  "BPMJF7YG8DKXGHXLL4IYIGYJEYMF0HYWW0002D4I7CD6DK9NBPMJF7H4XGHYG8aCEXLL0D0000DD6DKXGHaCEX",
  "LLYG8F74I7C9NBPMJH413D0100DD6DKXGHaCEXLLYG8F74I7C9NBPMJH413D0100DD6DKXGHaCEXLLYG8F74I7",
  "C9NBPMJH413D0105C4I7CD6DK9NBPMJF7H4XGHYG8aCE0C000O02001823310230A5232322363XQ234342240",
  "422325413035364130353222321415035504151355041313532226414374313K221042242F221042242F22",
  "11P224192213XE22340gWWXmWbgriWWXpWWWWXuWWuyWWikWWsWWikWcdWyyZWiWXgrhWXwr90maWWWmYaWWWW",
  "XYWWeWnWWYWWYWemXWaWWWWXWeWmWWWWaWnWWWWWmWW00eYWWaeXYWWWWenWWaWemYXaXXWaWmmYXWaWmmWeea",
  "WWaYWemWWWYeWW00aWmWmXWWWaaWWnWWWeWeWWWcWWWZWWYWWWYWWXWieWWaWeWWXWWWW00ldv//tdzv////cz",
  "//t/k/xydzz/t++/xz/t++//llt//tv/kl///vl//VucWWeuYcWWWWvYWWeWnWaZuYYWeXXWaYWeXXWWmmeWWe",
  "cWnmWWWcmWW00086567809"]
@[expose] def ext_full_sweep_bins_m6cf : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 136)]

@[expose] def hint_full_sweep_bins : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_sweep_bins : List (SigEntry × Nat) :=
  [(("full_sweep_bins_m6cf", [i64], []), 264)]

@[expose] def hint_full_sweep_copy : x64Isa.Hints := _decH #[
  "c6661E101I1G0000040409070A165806065806065806065803060A1B071658030B070F0F251H0H09283804",
  "040B42040B3208290104331C0B120202032G3F00000E0E0703030A131I091B06080B1606080B381H260635",
  "0506090I0920030C0A3205130903020I0925062603030A131H091B07000B1707000B371028083I0I08090H",
  "0920033C0A320I130903020H092I087G03030A1C133707380802002B0607070B030AA3000A1B330B06A707",
  "2D0203031A300A0029180G1E1F1H060C0C5910090022290000B003S001700101377K0M41331100377K0M41",
  "331100377K0M4133110544PCEAO6N1340100BE0YF5IGYCF4PCEAO6N77YIHGI23CBe0201FYK3E0YF5IGYCF4",
  "PCEAO6N77YLCYQ8YIHGIYR40FYm0003CE0YF5IGYCF4PCEAO6N77YIHGIYLC13Ce0100ECEGIIGE0YF5YCF4PA",
  "O6N77YLCYK3YQ8YIH0Eam0008444ZTGa5Ea1F04A00014P010001544a1Fa5EZTGa3005A002844a1Fa5Ea67a",
  "30aB3ZTGaDI08Y2000844a1Fa5Ea67a30aB3ZTGaDI08Y2006C44a1Fa5Eb86aS8a67b65a30aUHZTGaDIaB30",
  "Co2006144010000244ZTG022001444ZTGa1Fa5E046002744c46a5Ec93ZTGa1FcBH07XG000744c46a5Ec93Z",
  "TGa1FcBH07XG006B44d68cQ7c46d4Ia5EcS0ZTGa1FcBHc930BiG009444eFCeAGf16040000644eFCeAGf16e",
  "R8f371360100644eFCeAGf16eR8f371360100644eFCeAGf16eR8f3713601070000003944g67gVFh1HgD3h2",
  "6gTEgRGgQ8092002844g67gVFh1HgD3h26gTEgRG08200O040720214232452242YD223244302311XU421124",
  "292220C2220F230222220Y3230222220E23021222002220F23021222002220YB23021222002220Z1222034",
  "211242B22200cuxthWuuXZwXgfmymZcfaoyWiWXgrhWWZWyzeXuXucWWYWyXuZWXvrmWeWWYmYWXmWWmdWWiWd",
  "csWXWWWgWXxWWWkWcZmXyWkWhWW/WWX+ZydulmWWgL0aWnWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWWWWWWWmWWmeaWXeWWWWmWXYWWWWWWWWWWW00XWaaWWWYYXWqWWWWWYWemWWWYaaaWWYWWWW",
  "WemeXWmWWamWWWaWmmeaWWWYaYWeaWWoWWWWmYYXWmWWYqeWYeaYYWaWYWWeWWnWWWWWWWWnWW00eWWWWWWWWf",
  "WWWWWWWYWWWWWaWeWWXXXWWieXWWWWYaWWWaeWXYaumWWWWWWYWWWnWWWXYWaepYWWWWWWWeWvWWWdWXWmWaWd",
  "WmeWgmWmrnhYsbeWgW00Z//////zz/tt///xxz+d/////v/kl///vtpt//x/////c/lz+l//ol///t++/lt///",
  "vtx/lp/+f///+/xxz+///udd/vltxx/t/x//d/+y///////+j//VYYWeeWWWaaYXuWWWWWcWnmWWWceieWWaWW",
  "WWWvWmYXmWWjmWWWeXXWmeWWWceaWmiWXsWWWXWaaYXWWWduuWcmeaaWeWaWWuWXZWWWWWWWXoWW0003656780", "9"]
@[expose] def ext_full_sweep_copy : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

@[expose] def hint_full_rewatch_arena : x64Isa.Hints := _decH #["00102042000000000300000"]
@[expose] def ext_full_rewatch_arena : List (SigEntry × Nat) :=
  [(("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 344)]

@[expose] def hint_full_move_red_pass2_m6 : x64Isa.Hints := _decH #[
  "X66I10140F0F091C0C083404040E0707090A4020202003000A1B40030B1933030B2E18160B0B0H703435H7",
  "70300009COEP8GAI5H4N7K65GF1690101DAI5H8G4N7K65I6R4GFL8COSEEP0Dm0000FCOSEEP8GI6L8R4U7KC",
  "AI5H4N7K65GF13FX0100FCOSEEP8GI6L8R4U7KCAI5H4N7K65GF13FX0100FCOSEEP8GI6L8R4U7KCAI5H4N7K",
  "65GF13FX0105CCOEP8GAI5H4N7K65I6R4GFL80CYW00050805B0940820318630231433A12323Y722A192232",
  "0aWfZWyeXuWXpckWWdWWL0aWWeXXWXYWWWWXWWWW00YWWaWmmWnWWWWamWWe00XWiWWWWmWWWWapWY00zv//t+",
  "+l+y////o///lVYcWWeXXmXZWWWWjWWWm00046567809"]
@[expose] def ext_full_move_red_pass2_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_move_red_end_buf_m6 : x64Isa.Hints := _decH #[
  "ZM5H161E150B3808033G0G0719090C0C090A4020202003000A1B40030B1909133003030B00212F0F020808",
  "0B230I0C0C090A4020202003000A1B40030B190309031F3F0H0H0B0F212F0F02330B0303240B2607000H0H",
  "0918080E3707070F0C0C090A4424242403040A1B44030B1933030B2F1E1G0B0B0IO047P434M6L2I5402008",
  "7P9H9K4M6LDEB6F534IO80301A7P9H9K4M6LDEB6F5H4S72IOA0201DJO7P9H9K4M6LDEB6F5H4S7IIMN0DaW0",
  "001FJO7P9H9K4M6LH4S7IIMNDEB6F5X1CQG0Fmm0000GJO7P9H9K4M6LH4S7IIMNQGX1CL8DEB6F513GXm0100",
  "GJO7P9H9K4M6LH4S7IIMNQGX1CL8DEB6F513GXm0100GJO7P9H9K4M6LH4S7IIMNQGX1CL8DEB6F513GXm0106",
  "FJO7P9H9K4M6LH4S7IIMNDEB6F5X1CQG18Fmm0101GJO7P9H9K4M6LH4S7IIMNDEB6F5X1CQGY180Gmm0004FI",
  "I7P9K4M6LH4S7JODEB6F5L8YRCMNQG0FuW0000FYRCMNQGII7P9K4M6LH4S7JOL8DEB6F513F6100FYRCMNQGI",
  "I7P9K4M6LH4S7JOL8DEB6F513F6100FYRCMNQGII7P9K4M6LH4S7JOL8DEB6F513F6105CII7P9K4M6LDEB6F5",
  "H4S7J0JO0C0001FII7P9K4M6LH4S7JODEB6F5L8YRCMNQG13FuW0101GII7P9K4M6LH4S7JODEB6F5L8YRCMNQ",
  "GZT30GuW00054434MaQI6L0400009aTOaU07PaS6aQI4M6LaR5b0H1G90101DaS6aQI7P4M6LaR5b2GbB7b0Hb",
  "5EaTObCFaU00Dm0000FaTObCFaU07Pb2Gb5EbB7bECb48aS6aQI4M6LaR5b0H13FX0100FaTObCFaU07Pb2Gb5",
  "EbB7bECb48aS6aQI4M6LaR5b0H13FX0100FaTObCFaU07Pb2Gb5EbB7bECb48aS6aQI4M6LaR5b0H13FX0105C",
  "aTOaU07PaS6aQI4M6LaR5b2GbB7b0Hb5E0CYW000I04351031123386430A344141B031BB2323XI2232XB224",
  "1XE22321223104283313X0423024194283313322357231A322A0XT223072221922350YWanmkaWyWWvpdWWZ",
  "mWWWWXuccWkWWmZmWZciyWWiWWiiWyWeXuWXpckWWYdWYL0YWWaWmmWnWWWWWmWWWWmXWYWmeWWWYWYaWWWWYW",
  "WmaXWmWXXWXYWWWWXXWWWW00XWWYWeeWemWWWYeWWaWeWmXWeaWWnXWXYWWWWfWWeYWmeWammWnWWWWamqWWe0",
  "0mcWWWWeWWWWYfmXWWWWuoXWdWWWWWXWWWWWeaWXaYWkWWWWWmWWWWaWpaW00ky//x/ld/kl///vl//t/d+lz/",
  "lt/+zy/zv////b//dx+/l/s+l+y////o+t//lVXZWWaWmuWnmWWWcmWWeWuXmYWmeWXYZWYcWWWWwWWuaXWmWf",
  "XmXZWWWWjXeWWm00066567809"]
@[expose] def ext_full_move_red_end_buf_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_move_red_end_m6 : x64Isa.Hints := _decH #[
  "N470B9808081C0603040B122A032A0B534403040B13071740000000044G5E6087134010044G5E608724340",
  "20545E4G60871440101040620510nWaXzumuuWaluH0YWWWWWWeWWW00XWWWbXYaWWW40YWeauWWWWnce00d//",
  "y///qyxp///NZWWWhZaiWWW8000256"]
@[expose] def ext_full_move_red_end_m6 : List (SigEntry × Nat) :=
  [(("full_move_red_end_buf_m6", [i64, i64, i64, i64], []), 104)]

@[expose] def hint_full_arena_sweep_m6 : x64Isa.Hints := _decH #[
  "ZU25131H1610282214090B09270B60190B00030B0C0B220713190703030B373019070300030B2B700B2I37",
  "03040C03030B6808030B19031B39030B0C0C0C0C0C1C190B07000B12020202080300007909173307070B03",
  "2124040203091903030C0B19090307020F034E080E0B7B920B1B434F030F0B47A3080A1B330B291303P001",
  "3001009474L65HKEOAH8NC6CP24I90204965M4EO4LHKAH8NC6CP23I9020084L65HKEOAH8NC6CP08000094L",
  "65HKEOAH8NC6CPM423C90207A65M4XEIEO4LHKAH8NC6CP13A0100B65M4XEIEO4LHKAH8NC6CPXI30BXW0002",
  "C65M4XEIEO4LHKAH8NC6CPY00XP30CXW000244LY8S65HK7EFJRQHT40700A4LY8S65HKE3EOAH8NC6CP7GEFJ",
  "RQTA070094LY8S65HKEOAH8NC6CP7GEFJRQT90702JYCEYDFYEJYFRYGQYHT4LHK65EOY8SYMIAHYBG8NC6CPY",
  "Q7YI01CJaYW0103LYS4YTCYCEYDFYEJYFRYGQYHT4LYMI65YBGYQ7HKEOYI0AH8NC6CPY8S13Lam0100LYCEYD",
  "FYEJYFRYGQYHT4LHK65EOY8SYMIAHYBG8NC6CPYQ7YI0ZE3YTC0LaYW0009IYEJYGQZSUYHT4LY8S65HKEOAH8",
  "NC6CPa88YCEYFRYDFYMI0IaWW0001LYEJYGQZSUYHT4LY8S65HKEOAH8NC6CPa88YCEYFRYDFYMIaB0a9MYBG1",
  "CLaWW0101MYEJYGQZSUYHT4LY8S65HKEOAH8NC6CPa88YCEYFRYDFYMIaB0a9MYBGaLC0MaWW0007DZSUYHT4L",
  "Y8S65HKEOAH8NC6CPa88YCE4FJRQD04038cDT464LY8Sc7EcCHcARc9J080000BcDT464LY8Sc7EcCHcARc9Jc",
  "8F65HK0B000684LcARc9Jc7E65cDTY8ScCH1F801015cDT4LY8Sc7EcCH0500006cDT4LY8Sc7EcCHd5713601",
  "006cDT4LY8Sc7EcCHd5713601006cDT4LY8Sc7EcCHd57136010V7234102301022A43633B314323YN23B204",
  "23122B1A3601303733833A30C2103601A037A38A3AAB2224022B412353822B5522B5X2239C020B3N221012",
  "3530221002210D2222X222381436A383323733223132210062101313A3D2214X6223612237X92214240A32",
  "3A1aO51uXmWbgrireWdtWeWZWWWWWWmWWeWccWkWbxmWWWYWWXuWmluWzmWWWXkuWXeWWWY/mWWnpgL0mYaWWW",
  "WWWeWWaWfeYWWmWWYWXWYWmeWWmWWWWWWWWaYWWWWWWWWYWaWXWaXWaWWWWXaaWW00XWeXYWWWWWWaWWYWaaXW",
  "WeWXXWWoXWeaWYeWWbgeqWWYXXaWYWWaaXWYWWmYWmYeqWaaoYWW00mXWWWaWWXWpWWWWWWWYWWWWWWWoXWdWW",
  "voWWcWWaWeWXceWimWWeWceaWWWWYWimWWWWW00lz/dzv//////p//x/ttz//lxry/+xz/lt/xl//mZct/pxzz",
  "mlv//pty/x/+lx+/uct/pshx//VYWuYcWWWWWWiWWaWeeYWWmagZWXaYWmeWamWWlyveWiaYYlmcWWieZWaWXm",
  "aXWdveWifqaWW000C6567809"]
@[expose] def ext_full_arena_sweep_m6 : List (SigEntry × Nat) :=
  [(("full_sweep_bins_range_m6", [i64, i64], []), 248),
   (("full_sweep_copy", [i64, i64, i64, i32, .bool], [i64]), 296),
   (("full_move_red_end_m6", [i64, i64, i64], []), 136),
   (("full_rewatch_range_m6", [i64, i64, i64], [.bool]), 344)]

@[expose] def hint_full_mark_reasons_m6 : x64Isa.Hints := _decH #[
  "R421G1F1H18131E1I17072B3303030B39130B03000A200C0000071B3000000018G854MIEHCFKEAG4617801",
  "019G854MIEHCFKEAG46T70900000XWcWYdWicgrgJ0aWWmmmeWWWWW00YWWeeeaWeWWW40YaWWWaWWWW00Zv//",
  "dllt/l///NcWWummeWmWWW8000556780"]
@[expose] def ext_full_mark_reasons_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_arena_sweep : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_arena_sweep : List (SigEntry × Nat) :=
  [(("full_arena_sweep_m6", [i64], [i64]), 504)]

@[expose] def hint_full_mark_reasons : x64Isa.Hints := _decH #[
  "R421G1F1H18131E1I17072B3303030B39130B03000A200C0000071B3000000018G854MIEHCFKEAG4617801",
  "019G854MIEHCFKEAG46T70900000XWcWYdWicgrgJ0aWWmmmeWWWWW00YWWeeeaWeWWW40YaWWWaWWWW00Zv//",
  "dllt/l///NcWWummeWmWWW8000556780"]
@[expose] def ext_full_mark_reasons : List (SigEntry × Nat) := []

@[expose] def hints : List x64Isa.Hints := [hint_full_lit_rank_m6,
    hint_full_sweep_bins_range_m6, hint_full_rewatch_range_m6, hint_full_rewatch_arena_m6,
    hint_full_sweep_bins_m6cf, hint_full_sweep_bins, hint_full_sweep_copy,
    hint_full_rewatch_arena, hint_full_move_red_pass2_m6, hint_full_move_red_end_buf_m6,
    hint_full_move_red_end_m6, hint_full_arena_sweep_m6, hint_full_mark_reasons_m6,
    hint_full_arena_sweep, hint_full_mark_reasons]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_wstack_defrag_m6", [i64], []), 136),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Collect
