module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Parse

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rbp, Reg64.rsi, Reg64.rbx, Reg64.rdi, Reg64.r12, Reg64.r13, Reg64.rax, Reg64.r14,
  Reg64.r15]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rax), (.gpr Reg64.rbp), (.flag CondCode.nc), (.gpr Reg64.rcx), (.gpr Reg64.rdx),
  (.flag CondCode.nz), (.gpr Reg64.rdi), (.flag CondCode.c), (.gpr Reg64.r8), (.gpr Reg64.rsi),
  (.gpr Reg64.r12), (.gpr Reg64.r9), (.gpr Reg64.r13), (.gpr Reg64.rbx), (.gpr Reg64.r15),
  (.flag CondCode.z), (.gpr Reg64.r14), (.flag CondCode.g), (.slot 0 .w64)]

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

@[expose] def hint_full_activate_lit_fid : x64Isa.Hints := _decH #[
  "XQ30010213241504431607040618191324240240001010002A0665030219142510020300002302060A0B10",
  "001207351C0514040423031232084513500000002581514DR6X1305200100000084YJA8151YI610441007Y",
  "JA8151YI6YKBZ0C4D1074101040010231O51XmXsdauWpmoWcWfrWiiqfYfmgwqYtXj10eWWWWWWWWWWWWWXWW",
  "WWWWWWWWWWWW00aWeeWYabWYWXYWemWWWWWaWWWWWYW80uWpXWjWWmWWZWWWWWWWWWWmWWWmWWW00////t/ll/",
  "xtn/x/zx/k//////t//+l/x/FeWmmWaekWaWYaWnWWWWWWeWWXmWaWG00042045"]
@[expose] def ext_full_activate_lit_fid : List (SigEntry × Nat) :=
  [(("f64u_inv_u64", [i64], [i64]), 8),
   (("f64u_sub", [i64, i64], [i64]), 8)]

@[expose] def hint_full_ingest_cl : x64Isa.Hints := _decH #[
  "bQ31141A1E2000500713060807060F0017130F0017121F0B0B03070B000720000807060007060B000B0203",
  "07000F17000000020B0B03070B000720000807060007060B000B020307000F170000001F0F130000080226",
  "0F0B02060B160303260606002F050G08122C35021323030317130323030317130323030317130323030317",
  "1003021713230303171007052323032H0F04291007151029090A070F0F1F000300002234020403251C1618",
  "111A190B0B551405042F250404B400V0010001004944D71BA36G94030074DDEHI599471BA2CG702009LCMG",
  "944D71BADEHI5910901009LCMG944D71BADEHI5910901009LCMG4DDEHI599471BA10901019LCMG4DDEHI59",
  "9471BA10901029LCMG4DDEHI599471BA10901059LCMG944D71BADEHI590900019LCMG944D71BADEHI5923B",
  "902079LCMG944D71BADEHI590900029LCMG944D71BADEHI5923B9020A9LCMG944D71BADEHI5923090201AL",
  "CMG944D71BADEHI59ZE310A0104671BAaG64DaHGaI90600007944D71aG6aHGaI9BA10701007944D71aG6aH",
  "GaI9BA10701007944D71aG6aHGaI9BA10701028944D71aG6aHGaI9BAaL00800018944D71aG6aHGaI9BAaL0",
  "0800018944D71aG6aHGaI9BAaL00800018944D71aG6aHGaI9BAaL00800038944D71aG6aHGaI9BAc2008000",
  "424D711C20100471BAaG64D29040202571BAaG64DcG0195010234D71d1C03000034D71d1C1A30104000000",
  "394DdG3e71e9AdI0eB9e58e36e1C09200284DdG3e71e9AdI0eB9e58e3608200202023E23060ZijxrmiiWnz",
  "XgrcXvmWWWuWWiXpWWXYcWWaeuenmnZXYcWWXnWiWWWXmXWWXWWWWWWWWWWWaWWWWWWWWWmWXWWWWywL0XWaaW",
  "WWWWWWWYXWWWmWmWWXWeWaeXWWYWWaWWeWWmWWWWWWWeaWWWWWXWWeeWWmWWWWeWYYWWaWWmWeeWWWW00mYYWW",
  "WWeaYWXemWeeWgWXWmaWYaWmWXWWYWWaWYeWYWmWWYaXWgWYeWoWaaWeeeWfWamXXWYYXaeaabWaWW00aWWWWW",
  "WWWamWWXWWWWWWiWWcWfmWWWZWYWWkWWyWXuWZWWWmWYmWWWmWWWuWWWmWWWWWWXWWWaWWWWWWWWWWWWWWW00Z",
  "//////++/xx////ltx/ikl/ld/h/z+lt/xp+//z//x//t/vl/xu///xtz/Z/vl+f/vp/ldl/b/ol+i/xvztltt",
  "slt//VXXWaaWWWWmeaWpnmWmuWqWYXmeWaiXWWYWWaWWeWcmWadWWWaeYWyWcmXsWciWmumWwWjmXpWacYemee",
  "fmeWW00016204578"]
@[expose] def ext_full_ingest_cl : List (SigEntry × Nat) :=
  [(("full_activate_lit_fid", [i64, i32], []), 56),
   (("full_add_clause", [i64, i32, i32, .bool], [i64]), 312)]

@[expose] def hint_full_tumble_finish_fid : x64Isa.Hints := _decH #[
  "X63B0213140500000B101F00020002393F09193F09193F0919082F0900021730092F000700000B50000000",
  "23467BC40300004467BC4A318401004467BC4A318401004467BC4A310401000YWWiuWWvXwZqdiWWnWb30mW",
  "XYWWWWWWWWXWWXW00eWWnWWWWWWWWemWWm80aeWmeWeWmXaaWWWW00X//k/+yz/x/t/l/cz/+bFnWXZYWaWeWm",
  "WvYWXwG0000"]
@[expose] def ext_full_tumble_finish_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_parse_body_m6 : x64Isa.Hints := _decH #[
  "YA303907130512A004021740078570175G1F0F0F000F0A170G0E1F0F3017200713090607090F0017130F00",
  "17152B0213190502363F06163F06163F0616082F0600021730062F000700000BK00100010024D5C0200014",
  "4DB9E35C104010044DB9E35C104010044DB9E35C104010525C4D142010025C4D3AG12030024D5C33A02030",
  "024D5C2A12020135C4DXI1343G3030535C4DXU1343G3030A34DYK45C103010034D5CYK4103010134D5CYK4",
  "103010234D5CYK4103010424DYK402000144DYK4ZCBZH904000054DYK4ZCBZH9ZF3185010054DYK4ZCBZH9",
  "ZF3185010054DYK4ZCBZH9ZF31050101040510230YWWiuWWvXwZqdiWgcWWYWWWYWaWWWYWWWWYWZ/YZYWYrg",
  "sWnXL0mWXYWWWWWWWWYWWXWWmmWWWmWeWemWWWeaWWXWXYWWWWWWe00eWWnWWWWWWWWfWmmmeegWeWeWbWaWrW",
  "WaWaWWmWnWWWWaaa00aeWmeWeWmXaWWWWWWWWWWWWWWWWWWWWWWWWWXWWmWWYWWW00X///k/+yz/x/t/l/b+++",
  "/lli/l/d/n/tsX//p/t/+l+y////pttVnWXZYWaWeWmWwXXXWmmpWmWuWkWef+WWiWeWXmXZWWWWiee0000620",
  "4578"]
@[expose] def ext_full_parse_body_m6 : List (SigEntry × Nat) :=
  [(("full_skip_cl", [i64, i64], [.bool]), 0),
   (("full_ingest_cl", [i64, i64], [i64]), 376),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_wstack_defrag_m6", [i64], []), 136)]

@[expose] def hint_full_parse_body : x64Isa.Hints := _decH #["000000000000300000"]
@[expose] def ext_full_parse_body : List (SigEntry × Nat) :=
  [(("full_parse_body_m6", [i64, i64], [i64]), 760)]

@[expose] def hints : List x64Isa.Hints := [hint_full_activate_lit_fid, hint_full_ingest_cl,
    hint_full_tumble_finish_fid, hint_full_parse_body_m6, hint_full_parse_body]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_inv_u64", [i64], [i64]), 8),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("full_add_clause", [i64, i32, i32, .bool], [i64]), 312),
   (("full_skip_cl", [i64, i64], [.bool]), 0),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_wstack_defrag_m6", [i64], []), 136)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Parse
