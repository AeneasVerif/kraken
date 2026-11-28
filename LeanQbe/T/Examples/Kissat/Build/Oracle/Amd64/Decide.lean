module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Decide

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rax, Reg64.rcx, Reg64.r12, Reg64.rbp, Reg64.r9, Reg64.rbx, Reg64.r13, Reg64.r14,
  Reg64.r15, Reg64.rdi, Reg64.rsi, Reg64.rdx, Reg64.r8]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.r8), (.gpr Reg64.rsi), (.gpr Reg64.rdx), (.flag CondCode.nz), (.gpr Reg64.r9),
  (.gpr Reg64.rax), (.flag CondCode.c), (.flag CondCode.z), (.gpr Reg64.rcx),
  (.flag CondCode.nc), (.gpr Reg64.rbx), (.gpr Reg64.r12), (.gpr Reg64.rbp), (.gpr Reg64.r15),
  (.gpr Reg64.r13), (.gpr Reg64.r14), (.gpr Reg64.rdi), (.slot 6 .w64), (.slot 3 .w64),
  (.slot 4 .w64), (.slot 2 .w64), (.slot 0 .w64), (.slot 5 .w64), (.slot 1 .w64)]

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

@[expose] def hint_full_next_dec_var : x64Isa.Hints := _decH #[
  "Z320111223141526064337181808350508150626433718180835050806151523190505094337080507060A",
  "0B040C2504062305062D090A0804180C080906332B080B05096C0C092E0F062B0B0624060F0C0E392C280C",
  "0B05091525030323170953370506H00150010036081A203000154G6081A2F42585020054G6081A2F405000",
  "274G6081A2J8F4I507000254G6081A2F42585020274G6081A2XE8F4XD507000356081A24GY6H1550103560",
  "81A2Y6H4G05000256081A2Y6H4G050002A6081A2Y6H4GZ45YVBYUAYQ8Z1C0AX000796081A2Y6H4GZHIZAJZ",
  "4JZGA189a0100F6081A2Y6H4GZHIZAJZ4JZGAZI4ZIKZEDZLCZLLZVM4NB58Fa0402Ga786081A2Y6H4GZHIZA",
  "JZ4JZGAZI4ZIKZEDZLLa4NZVM3FCEGe030536081A2153010136081A203000346081A2bP504000CYS236092",
  "206XC2340C2331F23522430332402311X12201322036231362244042032440kdmXZWWWZWWciWiZWuiWiyWm",
  "ZWWucWWXu+WWwmZaodZuWmvanu+WbcL0XWWmYWeeeWWWWWWWXWeWWWWWWWWaeYWWWWYWXWWYWWWWeYWWWWWYWo",
  "WW00mmeXYaaaWWWeWXWWmaYWeXXeWmYaXWWqYXWmnWXWWWeaXYWWWYXWfWe00YWmWWWWWXmWZaWaXWeaWaaWWW",
  "WWeYWWWeYWWWWXWWXWWWWeWWeWWWW00kk/lzxttt///d/zn+/tx/dzyl+Zhtz/+dxz+Yz/z///ltzx///xz/b/",
  "lVXnWmYaeeeWWWuWYkXWeaWuYZmXyqeYWXuaYXzYWYWWWmeYaWWWaYWwWm00076532678"]
@[expose] def ext_full_next_dec_var : List (SigEntry × Nat) := []

@[expose] def hint_full_randec_var_lvl_fid : x64Isa.Hints := _decH #[
  "ZA3C0723231518081202020812021G0G0G021G060G02080802020205021G1505172605180812020208261G",
  "0G1808080G08020202090G0G280602090505020G0G0805081602180601090505010G0G0805081511120205",
  "05081215051G110502020213150505050543370806700150010334A5L7C183010127C4A02000337C4AYIL1",
  "83010237C4AZ2N18301025a0Ga217C4Aa6218501016a0Ga217C4Aa62a9806000602059B230AXF22A0X040A",
  "030AJ231BJ22B11YQ5AXu+WXWqXaXaWWWWWWWWWWfcYeuXaWWYYefevH0aWYWWWWWWWWWWWWWWWWWWWWWWWYWW",
  "WWmWWWWW00YYXWWYWWWWWWWWfWWWfWWWWeWXXWWWWeWWWXY40eYWWiWWWWWXeWWXeWXWZWWuWWWWWeWuZWWW00",
  "lvxz//x///////+bx/+by///d/zz///xl///zxNcaYWWaWWWWWWWXwaWXwZWWWuWYYWWWamWWWYa8002253"]
@[expose] def ext_full_randec_var_lvl_fid : List (SigEntry × Nat) :=
  [(("full_m7_state_init", [i64], []), 0),
   (("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24)]

@[expose] def hint_full_randec_var_m7 : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_randec_var_m7 : List (SigEntry × Nat) :=
  [(("full_randec_var_lvl_fid", [i64, i64], [i64]), 72)]

@[expose] def hint_full_decide_m7 : x64Isa.Hints := _decH #[
  "XQ272711121G10271808080704070817231203081718180505020518022641120808291109110G23001410",
  "1010100G0G531103012723010127A208900150010014A151010264AH0FG85B1D2186010154AH0FG85B1185",
  "010244AH0FG8518401020000003A4AXF5YHNYJKXU8YL0YFLXS2YD4YBI0A000294AXF5YHNYJKXU8YL0YFLXS",
  "2YD409000154AXF5YHNYJKXU805000A02059YR233C1230C1231C1232CU2293722B0222B0C22A2322B10xZd",
  "kocXnmYdqbgnoaua+imYWeuWYcre00aWmmWWWWWWWWWWWWmYYWWmWW40mWYWeeWWWYWnWWWmWWeXXWWeWY20XW",
  "WWWWWWWWWoWWWeWWWWWXWWWWWWWWW00l/////+/xx/ll///x+z//+l//jzzm/l/xRXWaaWmmWWWaXYWWXmWWoY",
  "YlWmWa400415"]
@[expose] def ext_full_decide_m7 : List (SigEntry × Nat) :=
  [(("full_randec_var_lvl_fid", [i64, i64], [i64]), 72),
   (("full_next_dec_var", [i64], [i64]), 104)]

@[expose] def hint_m6_hdr_decide_fid : x64Isa.Hints := _decH #[
  "YE272711121G10271808080704070817231203081718180505020518022641120808291109110G23001410",
  "1010100G0G531103012723010127A2085725130807130505031505050565051805060508C00150010014A1",
  "51010014A151010264AH0FG85B1D2186010154AH0FG85B1185010244AH0FG851840105A4AXF5YHNYJKXU8Y",
  "L0YFLXS2YD4YBI0A000294AXF5YHNYJKXU8YL0YFLXS2YD409000154AXF5YHNYJKXU805000214A151010014",
  "A01000214A01000A02059YR233C1230C1231C1232CU2293722B0222B0C22A2322B10bgqYWYWbmWxZdkocXn",
  "mYdqbgnoaua+imYWeuWYcre00YWWWWWWeWWWWWWWWWWWaWmmWWWWWWWWWWWWmYYWWmWW40XWWWWWmaYeaWWWWW",
  "WmWYWeeWWWYWnWWWmWWeXXWWeWY20eWWWWmWWWWWWXWWWWWWWWWWoWWWeWWWWWXWWWWWWWWW00ly////+/txlt",
  "/////+/xx/ll///x+z//+l//jzzm/l/xRZWWWWXWeameWWWWWXWaaWmmWWWaXYWWXmWWoYYlWmWa400415"]
@[expose] def ext_m6_hdr_decide_fid : List (SigEntry × Nat) :=
  [(("full_randec_var_lvl_fid", [i64, i64], [i64]), 72),
   (("full_next_dec_var", [i64], [i64]), 104),
   (("m6_hdr_init", [i64], []), 0)]

@[expose] def hints : List x64Isa.Hints := [hint_full_next_dec_var,
    hint_full_randec_var_lvl_fid, hint_full_randec_var_m7, hint_full_decide_m7,
    hint_m6_hdr_decide_fid]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_m7_state_init", [i64], []), 0),
   (("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("m6_hdr_init", [i64], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Decide
