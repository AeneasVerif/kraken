module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Search

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rbx, Reg64.rdi, Reg64.rbp, Reg64.rax, Reg64.rdx, Reg64.rsi, Reg64.r15, Reg64.r14,
  Reg64.r12, Reg64.r13, Reg64.r9, Reg64.r8]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.flag CondCode.nz), (.flag CondCode.z), (.gpr Reg64.rbp), (.gpr Reg64.rax),
  (.flag CondCode.nc), (.flag CondCode.c), (.gpr Reg64.rcx), (.gpr Reg64.rbx), (.slot 1 .w64),
  (.gpr Reg64.rsi), (.gpr Reg64.rdx), (.gpr Reg64.r14), (.gpr Reg64.rdi), (.gpr Reg64.r12),
  (.gpr Reg64.r13), (.slot 0 .w64), (.gpr Reg64.r15), (.gpr Reg64.r8), (.gpr Reg64.r9)]

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

@[expose] def hint_full_preprocess_m6 : x64Isa.Hints := _decH #[
  "XC302112110120111011202031011011010113046020110010102151101011202013050604060605110010",
  "1011700130010814701000014701000214701000714701000B14701000014701000202001XB20230faWWWW",
  "avofXaioWWuuoammWeZWvoecWfJ0YYWWWWaWWWWWWWWWW00oebWYanYaoeWnaYnXWWWYYqomXYaoeqY40mWWWW",
  "WWWWWWWWWWWWWWWWWWWWWW00////+xln/xmzxsxl+ztuzz///xwcu/zxsxkdxNXamkWalYafamXYedYYWWWabv",
  "dWYafanua8000202"]
@[expose] def ext_full_preprocess_m6 : List (SigEntry × Nat) :=
  [(("full_lucky_late_m7", [i64], [i64]), 1240),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_arena_sweep_m6", [i64], [i64]), 504),
   (("full_compact", [i64], [i64]), 760),
   (("full_scale_delta_m5", [i64, i64], [i64]), 40),
   (("full_probe_m6", [i64, .bool], [i64]), 1256)]

@[expose] def hint_full_simplify_m6 : x64Isa.Hints := _decH #[
  "L5011202111201020201305160406060511001010036001300100347685903000124768020004147010004",
  "147010000147010004020012231412305022500fWWWWepcfmWvmW30aWWa80YXeWnYaeoXXYXW40aWWWWWWWW",
  "W00d+xyl+yhtkxzzxz/NXaZmXZqenaYYaYW800210"]
@[expose] def ext_full_simplify_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_probe_m6", [i64, .bool], [i64]), 1256),
   (("full_eliminate_m6", [i64, .bool], [i64]), 1416),
   (("full_compact", [i64], [i64]), 760)]

@[expose] def hint_full_search_m6 : x64Isa.Hints := _decH #[
  "ZC21013316060403060430131A03032030O0411101110301100B1403110011160406160406101113051009",
  "0B0C030101140121210134130503030316050A0403030A09090603031103060330301103040D0202401305",
  "2300153100030014030603003100111103231111310040K0013001021471610102247J6132010114701000",
  "114701000114732DE1030314732DE103035XT2XUDXVE47Y730500045XT2XUDXVE47Y7316501024XT2XUDXV",
  "E471340103447XT2XUDXVE14401008XT2XUDXVE47Z7FZ88Z6BZ590800027XT2XUDXVE47Z7FZ88Z6B1G7010",
  "17XT2XUDXVE47Z7FZFGZ881B701044XT2XUDXVE4713401044XT2XUDXVE470400024XT2XUDXVE470400024X",
  "T2XUDXVE47040004447XT2XUDXVE0400064XT2XUDXVE47134010502001aD4313301A206342073720631bF5",
  "1aWWYeWieWWuWeWWumZXYcWXWcYcWWWWWWWWWWWWWnaXXaWWeeaWm////wmifmauWYr00YXYWWYaWeeWYaWWeW",
  "WWWWWYWWWWXaWWWWWWWXXWWWWWWWWWXWWWWWXWW00ebWamWWXWqXWnWqXYWaaWXYeWaWWWWfWWWbXXWoXafWWe",
  "bWmoffXWWWWWWmYWXWmmWA0mWWWWWWWWWWWWWWWWXeWXWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW00Z/ln/s",
  "//+z+dy+j+dyx/tt/zxl/t/x/+byztrzzkxztjttln++xjjz/////+/x/z++//3mkWfWWXYXuZXoXuZaWeeWYa",
  "mWeWaWXwZYegYYnaYeoeemkXXaooYWWWWWXWaWYXXWWS0026028976"]
@[expose] def ext_full_search_m6 : List (SigEntry × Nat) :=
  [(("full_lucky_late_m7", [i64], [i64]), 1240),
   (("m6_hdr_init", [i64], []), 0),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_reduce_m6", [i64, .bool], [i64]), 856),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_log10_u64", [i64], [i64]), 8),
   (("full_restart", [i64], []), 200),
   (("full_reorder_queue_m7", [i64], [i64]), 280),
   (("full_rephase", [i64], []), 840),
   (("full_simplify_m6", [i64, .bool, .bool], [i64]), 1448),
   (("m6_hdr_decide_fid", [i64], [i64]), 152),
   (("full_switch_mode_m7", [i64], []), 200),
   (("full_analyze_core_m6", [i64], [i64]), 1000),
   (("m6_hdr_dr_update", [i64], []), 72)]

@[expose] def hint_kissat_solve_bytes_seeded : x64Isa.Hints := _decH #[
  "S610101030503050303030C050A060911100H1101000I3113032611032001300109442OFP7T81340105020",
  "21K430532A020035231BI22B10geWaWWWWWW00eWmWWWWW00aWgnaYXaL0Xeo00l/x//t/YztvuoLaWWeWzYec",
  "djA003202"]
@[expose] def ext_kissat_solve_bytes_seeded : List (SigEntry × Nat) :=
  [(("full_m6_mem_init", [i64, i64, i64, i64, i64], [i64]), 184),
   (("full_parse_body_m6", [i64, i64], [i64]), 760),
   (("full_preprocess_m6", [i64], [i64]), 1288),
   (("full_search_m6", [i64], [i64]), 1528),
   (("full_extend_core_fid", [i64], []), 40),
   (("full_unperm_fid", [i64], []), 24),
   (("kissat_check_model", [i64, i64, i64, i64, i64], [i64]), 48)]

@[expose] def hint_kissat_solve_bytes : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_kissat_solve_bytes : List (SigEntry × Nat) :=
  [(("kissat_solve_bytes_seeded", [i64, i64, i64, i64, i64, i64], [i64]), 1576)]

@[expose] def hints : List x64Isa.Hints := [hint_full_preprocess_m6, hint_full_simplify_m6,
    hint_full_search_m6, hint_kissat_solve_bytes_seeded, hint_kissat_solve_bytes]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_lucky_late_m7", [i64], [i64]), 1240),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_arena_sweep_m6", [i64], [i64]), 504),
   (("full_compact", [i64], [i64]), 760),
   (("full_scale_delta_m5", [i64, i64], [i64]), 40),
   (("full_probe_m6", [i64, .bool], [i64]), 1256),
   (("full_backtrack", [i64, i64], []), 168),
   (("full_eliminate_m6", [i64, .bool], [i64]), 1416),
   (("m6_hdr_init", [i64], []), 0),
   (("full_reduce_m6", [i64, .bool], [i64]), 856),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_log10_u64", [i64], [i64]), 8),
   (("full_restart", [i64], []), 200),
   (("full_reorder_queue_m7", [i64], [i64]), 280),
   (("full_rephase", [i64], []), 840),
   (("m6_hdr_decide_fid", [i64], [i64]), 152),
   (("full_switch_mode_m7", [i64], []), 200),
   (("full_analyze_core_m6", [i64], [i64]), 1000),
   (("m6_hdr_dr_update", [i64], []), 72),
   (("full_m6_mem_init", [i64, i64, i64, i64, i64], [i64]), 184),
   (("full_parse_body_m6", [i64, i64], [i64]), 760),
   (("full_extend_core_fid", [i64], []), 40),
   (("full_unperm_fid", [i64], []), 24),
   (("kissat_check_model", [i64, i64, i64, i64, i64], [i64]), 48)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Search
