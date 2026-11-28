module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Search

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X20)),
  (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X23)),
  (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X5)),
  (XRegOrSp.reg (XReg.X4))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X0))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.slot 1 .w64), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X22))), (.slot 2 .w64),
  (.slot 0 .w64), (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.gpr (XRegOrSp.reg (XReg.X5)))]

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

@[expose] def hint_full_preprocess_m6 : armIsa.Hints := _decH #[
  "Y2200110021312021001120001000210011001320200011202020004055001100112010001000110025200",
  "01000100021001100110060407040406120100010001000270010001081480100001480100021480100071",
  "4801000B14801000014801000202001XB20210aemWXaaWWWeeoamWWWZWemWYWeH0YYWWWWaWWWWWWWWWW00o",
  "ebWYanYaoeWnaYnXWWWYYqomXYaoeqY40mWWWWWWWWWWWWWWWWWWWWWWWWWW00////+xln/xmzxsxl+ztuzz//",
  "/xwcu/zxsxkdxNXamkWalYafamXYedYYWWWabvdWYafanua8000202"]
@[expose] def ext_full_preprocess_m6 : List (SigEntry × Nat) :=
  [(("full_lucky_late_m7", [i64], [i64]), 1024),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_arena_sweep_m6", [i64], [i64]), 384),
   (("full_compact", [i64], [i64]), 624),
   (("full_scale_delta_m5", [i64, i64], [i64]), 16),
   (("full_probe_m6", [i64, .bool], [i64]), 1120)]

@[expose] def hint_full_simplify_m6 : armIsa.Hints := _decH #[
  "U4001121001100212100100011001100110061407040406120100010001006001000100348695403000124",
  "86902000414801000414801000014801000502001223131230402240F22310enYWmWemW10aWWa80YXeWnYa",
  "eoXXYXW40aWWWWWWWWW00d+xyl+yhtkxzzxz/NXaZmXZqenaYYaYW800210"]
@[expose] def ext_full_simplify_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_probe_m6", [i64, .bool], [i64]), 1120),
   (("full_eliminate_m6", [i64, .bool], [i64]), 1200),
   (("full_compact", [i64], [i64]), 624)]

@[expose] def hint_full_search_m6 : armIsa.Hints := _decH #[
  "aO22023014040500040510000100001A00000404010400000100M001300212020002000204010B04050012",
  "010402040A0504040A05041100020004060001040B000A0202150222220237100600000014060A05000005",
  "0A0A0400001200040000000001000011000200070C03030000100100040D00000001040D00001201000104",
  "050004000100001201120002000000000002000232013001K0010001021481410102248J41020101148010",
  "00114801000114833CE1030314833CE103035XT3XUCXVE48Y700500045XT3XUCXVE48Y7014501124XT3XUC",
  "XVE481040103448XT3XUCXVE10401008XT3XUCXVE48Z79Z8FZ6BZ540800027XT3XUCXVE48Z79Z8FZ6B1G70",
  "1017XT3XUCXVE48Z79ZFGZ8F1B701044XT3XUCXVE4810401044XT3XUCXVE480400024XT3XUCXVE48040002",
  "4XT3XUCXVE48040004448XT3XUCXVE0400064XT3XUCXVE48104010902001aD432331152241423010411Z/y",
  "WWWWWWWWW0301320511224052301022400l///wWWWWWWWYr00YXYWWYaWeeWYaWWeWWWWWWYWWWWXaWWWWWWW",
  "XXWWWWWWWWWXWWWWWXWW00ebWamWWXWqXWnWqXYWaaWXYeWaWWWWfWWWbXXWoXafWWebWmoffXWWWWWWmYWXWm",
  "mWA0mWWWWWWWWWWWWWWWWZeWXWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW00Z/ln/s//+z+dy+b+dyh/tt/zx",
  "l/t/xucby/trzzkxztjttln++xjjz/////+/x/z++//3mkWfWWXYXuZXwXuZqWeeWYamWeWadvwZWegYYnaYeo",
  "eemkXXaooYWWWWWXWaWYXXWWS003502675"]
@[expose] def ext_full_search_m6 : List (SigEntry × Nat) :=
  [(("full_lucky_late_m7", [i64], [i64]), 1024),
   (("m6_hdr_init", [i64], []), 0),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_reduce_m6", [i64, .bool], [i64]), 688),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_log10_u64", [i64], [i64]), 0),
   (("full_restart", [i64], []), 112),
   (("full_reorder_queue_m7", [i64], [i64]), 256),
   (("full_rephase", [i64], []), 656),
   (("full_simplify_m6", [i64, .bool, .bool], [i64]), 1232),
   (("m6_hdr_decide_fid", [i64], [i64]), 80),
   (("full_switch_mode_m7", [i64], []), 96),
   (("full_analyze_core_m6", [i64], [i64]), 848),
   (("m6_hdr_dr_update", [i64], []), 48)]

@[expose] def hint_kissat_solve_bytes_seeded : armIsa.Hints := _decH #[
  "S620202000D000D0000000H060A0I0412110J1202010K3210002I12002001000109443OGP8T91040106020",
  "21K4304328020015231972282A22910geWaWWWWWW00eWmWWWWW00aWgnaYXaL0Xeo00l/x//t/YztvuoLaWWe",
  "WzYecdjA003202"]
@[expose] def ext_kissat_solve_bytes_seeded : List (SigEntry × Nat) :=
  [(("full_m6_mem_init", [i64, i64, i64, i64, i64], [i64]), 64),
   (("full_parse_body_m6", [i64, i64], [i64]), 624),
   (("full_preprocess_m6", [i64], [i64]), 1152),
   (("full_search_m6", [i64], [i64]), 1312),
   (("full_extend_core_fid", [i64], []), 0),
   (("full_unperm_fid", [i64], []), 0),
   (("kissat_check_model", [i64, i64, i64, i64, i64], [i64]), 48)]

@[expose] def hint_kissat_solve_bytes : armIsa.Hints := _decH #["000000000000300000"]
@[expose] def ext_kissat_solve_bytes : List (SigEntry × Nat) :=
  [(("kissat_solve_bytes_seeded", [i64, i64, i64, i64, i64, i64], [i64]), 1360)]

@[expose] def hints : List armIsa.Hints := [hint_full_preprocess_m6, hint_full_simplify_m6,
    hint_full_search_m6, hint_kissat_solve_bytes_seeded, hint_kissat_solve_bytes]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_lucky_late_m7", [i64], [i64]), 1024),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_arena_sweep_m6", [i64], [i64]), 384),
   (("full_compact", [i64], [i64]), 624),
   (("full_scale_delta_m5", [i64, i64], [i64]), 16),
   (("full_probe_m6", [i64, .bool], [i64]), 1120),
   (("full_backtrack", [i64, i64], []), 96),
   (("full_eliminate_m6", [i64, .bool], [i64]), 1200),
   (("m6_hdr_init", [i64], []), 0),
   (("full_reduce_m6", [i64, .bool], [i64]), 688),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_log10_u64", [i64], [i64]), 0),
   (("full_restart", [i64], []), 112),
   (("full_reorder_queue_m7", [i64], [i64]), 256),
   (("full_rephase", [i64], []), 656),
   (("m6_hdr_decide_fid", [i64], [i64]), 80),
   (("full_switch_mode_m7", [i64], []), 96),
   (("full_analyze_core_m6", [i64], [i64]), 848),
   (("m6_hdr_dr_update", [i64], []), 48),
   (("full_m6_mem_init", [i64, i64, i64, i64, i64], [i64]), 64),
   (("full_parse_body_m6", [i64, i64], [i64]), 624),
   (("full_extend_core_fid", [i64], []), 0),
   (("full_unperm_fid", [i64], []), 0),
   (("kissat_check_model", [i64, i64, i64, i64, i64], [i64]), 48)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Search
