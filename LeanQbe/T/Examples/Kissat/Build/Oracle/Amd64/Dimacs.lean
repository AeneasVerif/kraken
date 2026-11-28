module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Dimacs

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rax, Reg64.rdi, Reg64.rbp, Reg64.r8, Reg64.r12, Reg64.rcx, Reg64.rsi, Reg64.rdx,
  Reg64.rbx]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rax), (.gpr Reg64.rdi), (.flag CondCode.c), (.gpr Reg64.rcx), (.gpr Reg64.rdx),
  (.flag CondCode.z), (.gpr Reg64.rsi), (.flag CondCode.nc), (.gpr Reg64.r8),
  (.flag CondCode.nz), (.gpr Reg64.r9), (.gpr Reg64.rbx), (.flag CondCode.l),
  (.flag CondCode.g), (.gpr Reg64.r12), (.gpr Reg64.rbp)]

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

@[expose] def hint_kissat_is_ws : x64Isa.Hints := _decH #["41001020000000000020JC0000"]
@[expose] def ext_kissat_is_ws : List (SigEntry × Nat) := []

@[expose] def hint_kissat_is_digit : x64Isa.Hints := _decH #["2110200000000010160000"]
@[expose] def ext_kissat_is_digit : List (SigEntry × Nat) := []

@[expose] def hint_kissat_skip_ws_comments : x64Isa.Hints := _decH #[
  "D221304010204050012130500124001000100156101010115610101021561010101020010eWW00aWYYW00Y",
  "XXXe1000XxzzzpTaYYYi20000"]
@[expose] def ext_kissat_skip_ws_comments : List (SigEntry × Nat) := []

@[expose] def hint_kissat_skip_ws1 : x64Isa.Hints := _decH #[
  "N30070304030204030204080402080002130403020400022001000104256411020100010XXWWYWem00mmXX",
  "Wae4000X+ldz+lppNXmuYXmii80000"]
@[expose] def ext_kissat_skip_ws1 : List (SigEntry × Nat) := []

@[expose] def hint_kissat_read_nat : x64Isa.Hints := _decH #[
  "N330708080002080302200004020400020408000807030230010001021562381020025641238202000XWWW",
  "WWWW10XWWXWWe00oWmmaa40mWWWW00/+f/cltpNXsWvmei80000"]
@[expose] def ext_kissat_read_nat : List (SigEntry × Nat) := []

@[expose] def hint_kissat_parse_header : x64Isa.Hints := _decH #[
  "ZN321301080201050012130500121719001703010302010002130103020100020002030219292900070301",
  "03020100021301030201000203070808000208030220000102010002010800080703024A00070301030201",
  "00021301030201000203070808000208030220000102060002060018000807030220G00100010026456102",
  "01002645610201012645610201022645610201052645602000226456102010825664020002256641020103",
  "2645602000226456238202002645623820205364Z8A5603000235664Z8A1030105264Z8A23820200364Z8A",
  "5623830201020010YWWWeWWWWWWWWWWWXYWWWWWWWWWWWWWWcimWWWWWWYaWWeWW00eWWaaWXWWeeWXWWWYWWY",
  "WWmWaaWWmWWWWWeeWXWWWaWYYW00amWYYWmmmaaWemeWXaXXWeeeYYWaeaenamaaWemefYXXXe10aWWWWWWWWW",
  "WWWWWWXWWWWWWWWWWWWWWYWWWWWWWWWWWWW00d///ol/yv++k/pv/ldl/yp+i/ldlvy/tptkzo/pv/ldljxzzz",
  "pTjmWZcXXnWicWmumWZiXpWmumcZWeienYjWicWmumoaYYYi20000"]
@[expose] def ext_kissat_parse_header : List (SigEntry × Nat) := []

@[expose] def hint_kissat_next_lit : x64Isa.Hints := _decH #[
  "Y7300213040802040500121305001217150808030208030220000402040002040800080703024005120000",
  "0007080803020803022000040204000204080008070302400512000000B001000100241561020100241561",
  "02010124156102010224156102010515601000115623810200256412382020715601000215623810200256",
  "41238202000enWWWWWWWWWYamWWWWWWWmWXWWW10XWWXWWeWWWWWmWWmWaWWmWeeW00oWWoWmmaaaWamWfWeeY",
  "YXaeaabW40cWWWWmWWWWWWmWWWeWWWWWWWWWWW00/+h/+f/cltpt/o//a/pdxvztlttslNXqWXsWvmeieWjWWx",
  "WiuacYemeefm80000"]
@[expose] def ext_kissat_next_lit : List (SigEntry × Nat) := []

@[expose] def hint_kissat_check_model : x64Isa.Hints := _decH #[
  "Z56B0249200211080A02080500121105001217150A0A01020A000220000802080002080A000A0701020005",
  "02000000070A0A01020A000220000802080002080A000A07010200050200000015050001450C030D030012",
  "00021301080201050012130500121900H00100010225664020000456647EAB1F4010155664HF7EAB135010",
  "0656647EHFI3AB106010065664HFI37EAB106010065664HFI37EAB106010165664HFI37EAB106010265664",
  "HFI37EAB106010565664HFI37EAB06000165664HFI37EAB21A6020765664HFI37EAB06000265664HFI37EA",
  "B21A6020C25664102010025664102010125664102010225664102010408023045306317222718226002260",
  "0mWWWWmWdmWWWWWWWWWWWWWWWWWWWWWWWeWWmWWWW+00eWaaWWYYWWWWWWWeWYYWWaWWWWaWXXWWYWWeWaaWWW",
  "W20aYYYmYXWWeXeWgWamXXWYYYWYmYeWmmXXWoaYYYmYXWG0mWZWWWaWWWWWWWeWWYWWWWWWWWWWWWWWW00Ztt",
  "xxxdxy/jlyl/Z/ol+i/xvx/u/vd/clzy+xtxxxdxz+VeeaaauaZWomZmWyWjmXpWacaWdWcuWvmYZXaeaaauaY",
  "X00023824"]
@[expose] def ext_kissat_check_model : List (SigEntry × Nat) :=
  [(("kissat_parse_header", [i64, i64, i64], [.bool]), 0)]

@[expose] def hint_full_skip_cl : x64Isa.Hints := _decH #[
  "Y9400213040802040500121305001217150808030208000220000402040002040800080703020005120000",
  "00070808030208000220000402040002040800080703020005120000001505B00100010024156020000241",
  "56102010024156102010024156102010124156102010224156102010524156020001241562382020724156",
  "02000224156238202000aWWWWWWWWWWWmWWWWWWWWYWWaWWW30aWXXWWYWWWWXWWeeWWmWYWXXWW00XeWfWYeW",
  "mmXXXWXaWoWaaWeeanWmmqWG0ZWWWYWWWWWWWaWWWmWWWWWWWWWWWW00Xyl/b/vd/clzyz/yt+f/vp/ldsz+++",
  "v+VZmWwWcuWvmYZYWZeXsWciWmufYXXXcX00000"]
@[expose] def ext_full_skip_cl : List (SigEntry × Nat) := []

@[expose] def hints : List x64Isa.Hints := [hint_kissat_is_ws, hint_kissat_is_digit,
    hint_kissat_skip_ws_comments, hint_kissat_skip_ws1, hint_kissat_read_nat,
    hint_kissat_parse_header, hint_kissat_next_lit, hint_kissat_check_model, hint_full_skip_cl]

@[expose] def ext : List (SigEntry × Nat) := []

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Dimacs
