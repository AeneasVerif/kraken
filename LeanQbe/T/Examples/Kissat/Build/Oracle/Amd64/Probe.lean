module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Probe

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rdi, Reg64.rbx, Reg64.rsi, Reg64.r12, Reg64.rax, Reg64.rcx, Reg64.rbp, Reg64.r13,
  Reg64.r14, Reg64.r15]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.flag CondCode.nz), (.gpr Reg64.rax), (.gpr Reg64.rcx), (.gpr Reg64.rdx),
  (.flag CondCode.nc), (.gpr Reg64.rdi), (.gpr Reg64.r15), (.gpr Reg64.r14), (.gpr Reg64.r8),
  (.flag CondCode.c), (.gpr Reg64.rbp), (.gpr Reg64.r13), (.flag CondCode.z), (.gpr Reg64.rsi),
  (.gpr Reg64.r9), (.gpr Reg64.rbx), (.slot 0 .w64), (.slot 3 .w64), (.slot 2 .w64),
  (.gpr Reg64.r12)]

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

@[expose] def hint_full_probe_dticks_m6_hdr : x64Isa.Hints := _decH #[
  "84011120302020401200110010114501000262300022000Xe60G080eW00z//FYWWG0010"]
@[expose] def ext_full_probe_dticks_m6_hdr : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_full_probe_m6 : x64Isa.Hints := _decH #[
  "e781210601010606420107416810600501021920010001200A102B1C010901011410010110010902011C0A",
  "103A10301C0A10301C0A103C10010001200A102B120D1C010105090005050410010110010902011C0A103A",
  "10301C0A10301C0A10301C0A102101050524090102020402021004300A10300B0B10090D2C0A102E05000C",
  "0A0920020460080201091C0A090A1040110001300A203A1C0B0901012420110130110902012C09201C0A20",
  "2A203A2050010D01010D0D1C0A2040110001300A203B271D0103031C060101090002020420110130110902",
  "012C09201C0A202A203A20501C0A203101050524090203130403031004400A20401A0A1001020D0D0D2C0A",
  "10253A2A1A20XK00110010034FCG5H03000164FCGK6X0I5HR71A6010074FCG5HX6AR7K6X0I1J7010084FX7",
  "8CGK6X0I5HX6AR72128020284FCG5HX6AXMJR7K6X0I08000084FCGX0IK65HX6AXMJR708000084FCG5HX6AX",
  "MJR7K6X0I08000684FCG5HX6AXMJR7K6X0I08000084FCG5HX6AXMJR7K6X0I08000284FCG5HX6AXMJR7K6X0",
  "I08000184FCG5HX6AXMJR7K6X0I08000484FCG5HX6AXMJR7K6X0I08000384FCG5HX6AXMJR7K6X0I0800048",
  "4FCG5HX6AXMJR7K6X0I08000084FCGK6X0I5HX6AXMJR708000084FCG5HX6AXMJR7K6X0I08000684FCG5HX6",
  "AXMJR7K6X0I08000084FCG5HX6AXMJR7K6X0I08000384FCG5HX6AXMJR7K6X0I08000184FCG5HX6AXMJR7K6",
  "X0I08000484FCG5HX6AXMJR7K6X0I08000384FCG5HX6AXMJR7K6X0I08000384FCG5HX6AXMJR7K6X0I08000",
  "39c854FCG5HX6AXMJR7K6X0I2129020094FCG5HX6AXMJK6R7X0Ic9109000284F5HX6AXMJCGK6X0IR708000",
  "684FCG5HX6AXMJK6X0IR708000194FCG5HX6AXMJK6X0IR7d2B09000384FCG5HK6X0IR7X6AXMJ1280100A4F",
  "5HX6AXMJdG5dFECGK6X0IR7212A020844FCG5H7J1A4010044FCG7J5H04000044FCG5H7J04000664FCG5H7J",
  "f0Af3B06000064FCG5H7Jf0Af3B06000264FCG5H7Jf0Af3B06000164FCG5H7Jf0Af3B0600085gLA4FCG5H7",
  "J05000344FCG5H7J1A4010054FCGgLA7J5H0500005gLA4FCG5H7J05000674FCG5H7JgLAhS7i4607000074F",
  "CG5H7JgLAhS7i4607000374FCG5H7JgLAhS7i4607000174FCG5H7JgLAhS7i4607000844FCG5H7J0400045k",
  "754FCG5H7J2235020054FCG5H7Jk8205000844FCG5H7J04000154FCG5H7Jl6A05000324FCG02000X202010",
  "023320203462304N2324X62240XM2240D2240J2240J2240X12240G231552251X62240C2240J2240J2240J2",
  "240XC2240X12240XJ2240X12240YA2240C2240E2240Q2240X22240YK2240C2240D2240N2240XG2240X6224",
  "0P22408XD51Y751aM51ZC54YO51Z551bF51Z554XYiYYWeoWWWfWvYiZWWeeWWoauWiafmepXYiWcWaYXoaZWW",
  "WWrfYiZWXWvYiWWcepWepXYiWcWYXWvYXnmWfYiZWXWvYeWWW+WuWWeoWWXWanaYWWmWWWnaWanaWanaWanaYa",
  "mWWXWWmWWWenaYWWYXYeWfYeWfYeYamWWWmWemWYameWWeelXdxvyZYT0aWXWYWWWeYfWWfWWWWnXWWWWWWWWW",
  "WWWWWWWWWWWWWWWWeWeYWWWeWmWWWWWWWWWWWWWWWWWWWWWWWeWeYWWWaXWWWWmWWWWWaWmWWWaoWXaWWWWmWW",
  "WmWWWmWWWWWWWaWYaamWWWWWWmeWWWXWWWXWWWWWWWWYWXYXWWWWWYXXWWWWWWWWW00mWWWWaYWWmXWWmaWamW",
  "amWXWemWYWWaWWmaegWWYWWaaammWWWmaWaXWWmaWeWaWWaWWmaegWWXWWYYWoWWmaWaXWWmYemWaWfeWaYWYW",
  "eWeaWfWWoWWeaeWeaeWeaeWeWXWmWYWXYYeeWWeaWeamWmemWmemWmWXWmWXWWnWoWXWmXWmmWYWWWWWW00YWW",
  "WWWWWWWWWWWWWWWWWWmWWWWXWWWWWWWWWWWWWWWqWWWWWWWWWWWWWeWWWWWaWWWWWWWWWWWWWYYWWWWWWWWWWW",
  "WWWWWaWWWWWWWWWWWWWWWWWWWWWeWWWWmWWWWWWWWWWWWWWWWWWWWWWWWaWWWWaWWWWWWWWXXWWWWXeW00l+//",
  "///tx/+/z/+/t/sv/s//z/k//x//t/+/tlh+lx//tts+///+/t/tz/+/t/l/t//t/+/tlh/dz//xx+x/+/t/tz",
  "/+/vkf/r/bl/txtx/l/lt/jp+x//ltl/ltl/ltl/l/z+/dx/zxxll//lt/ls/+/k/+/k/+//z+/pz/+z+x/z+/",
  "z++i/x//////VXWWWWWeaWXWYWXWeWfcWfWWYWnWWaWWeWXWemqXmaWWeefXWWWXWeWeYWXWeWmWeWWeWXWemq",
  "WuYWWaaXaWXWeWeYWXWcnsWgWwmWeaeaWmWmeWoiXaWWmemWmemWmemWmWYXWuaWYaammWWmeWmfWXWnWXWnWX",
  "WWYXWiYWXYXaWYXWYXXpWaWWWWWW00046163789"]
@[expose] def ext_full_probe_m6 : List (SigEntry × Nat) :=
  [(("full_probe_dticks_m6_hdr", [i64, .bool], [i64]), 16),
   (("m6_hdr_init", [i64], []), 0),
   (("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 792),
   (("full_congruence_dense", [i64, i64], [i64]), 872),
   (("full_dense_bin_roundtrip_fid", [i64], []), 376),
   (("full_rebuild_watches_nosort_fid", [i64], [i64]), 728),
   (("full_substitute", [i64], [i64]), 808),
   (("full_backbone_m6", [i64, i64], [i64]), 792),
   (("full_vivify_m6_hdr", [i64], [i64]), 1160),
   (("full_sweep_dense_m6", [i64, i64, i64], [i64]), 904),
   (("full_transitive_m6", [i64, i64], [i64]), 792),
   (("full_has_factor_cands_fid", [i64], [.bool]), 0),
   (("full_factor", [i64, i64], [i64]), 888),
   (("full_update_classify_fid", [i64], []), 0),
   (("f64u_nlogpown", [i64, i64], [i64]), 72),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_to_u64", [i64], [i64]), 0),
   (("full_scale_delta_m5", [i64, i64], [i64]), 40)]

@[expose] def hints : List x64Isa.Hints := [hint_full_probe_dticks_m6_hdr, hint_full_probe_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 792),
   (("full_congruence_dense", [i64, i64], [i64]), 872),
   (("full_dense_bin_roundtrip_fid", [i64], []), 376),
   (("full_rebuild_watches_nosort_fid", [i64], [i64]), 728),
   (("full_substitute", [i64], [i64]), 808),
   (("full_backbone_m6", [i64, i64], [i64]), 792),
   (("full_vivify_m6_hdr", [i64], [i64]), 1160),
   (("full_sweep_dense_m6", [i64, i64, i64], [i64]), 904),
   (("full_transitive_m6", [i64, i64], [i64]), 792),
   (("full_has_factor_cands_fid", [i64], [.bool]), 0),
   (("full_factor", [i64, i64], [i64]), 888),
   (("full_update_classify_fid", [i64], []), 0),
   (("f64u_nlogpown", [i64, i64], [i64]), 72),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_to_u64", [i64], [i64]), 0),
   (("full_scale_delta_m5", [i64, i64], [i64]), 40)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Probe
