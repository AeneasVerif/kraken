module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Probe

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X1)),
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X2)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X27)), (XRegOrSp.reg (XReg.X28)), (XRegOrSp.reg (XReg.X29))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X1))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X29))),
  (.gpr (XRegOrSp.reg (XReg.X27))), (.gpr (XRegOrSp.reg (XReg.X22))),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X2))),
  (.gpr (XRegOrSp.reg (XReg.X25))), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X26))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X23))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.slot 4 .w64), (.slot 0 .w64), (.slot 1 .w64),
  (.slot 3 .w64)]

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

@[expose] def hint_full_probe_dticks_m6_hdr : armIsa.Hints := _decH #[
  "B2000010000120302020402200120010114201000262300022000XW00G080eW00zd/FYuWG0010"]
@[expose] def ext_full_probe_dticks_m6_hdr : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0)]

@[expose] def hint_full_probe_m6 : armIsa.Hints := _decH #[
  "j6520215220602020606270809020A42090B1C0D1E02014F110F020C0F03120102010212010G02010H0H0I",
  "1J020302020C0402010202020102030C021J0G02010H0H1G02010H0H02011J0G02010H0H02011J0G02010H",
  "0H1J020102010212010G02010H0H0I1C001J02020F03010F0F0K02010202020102030C021J0G02010H0H1G",
  "02010H0H02011J0G02010H0H02011J0G02010H0H02011J0G02010H0H02020F0F2403020C0C040C0C0F010K",
  "22010G02010H0H02010I0I020103002J0G02010H0H0L02010J0G030C110F044E110E0F0C031J0G030G0201",
  "0H0H0202010209010922010G0202010H0H1G1J0M0302021904020201020909020202010902030C02091J03",
  "12011J0G0202010H0H0G0202010H0H1G0202010H0H22010200020200001J0G0202010H0H02020102090109",
  "22010G0202010H0H1M27100209091J080202030109090K020201020909020202010902030C02091J031201",
  "1J0G0202010H0H0G0202010H0H1G0202010H0H22011J0G0202010H0H12020F0F2403090C1C040C0C0F010K",
  "32010G0202010H0H0G02010M0707020103020000002J0M02010H0H023G2G1G0202010H0HXK00120010034H",
  "C55N030001C4HN7C5X5DK6X4OX2BX1PX0QO85NRA1GC0100D4HN7C5O85NX6GRAX5DK6X2BX1PX0QX4O1MD010",
  "0E4HN7X7EC5X5DK6X4OX2BX1PX0QO85NX6GRA22CE0202E4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E000",
  "0E4HN7C5K6X2BX1PX0QX5DX4OO85NX6GXMMRA0E0000E4HN7C5O85NX6GXMMRAX5DK6X2BX1PX0QX4O0E0006E",
  "4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0000E4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0002E4H",
  "N7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0001E4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0004E4HN7",
  "C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0003E4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0004E4HN7C5",
  "O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0000E4HN7C5O85NX6GXMMRAX5DK6X2BX1PX0QX4O0E0000E4HN7C5O8",
  "5NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0006E4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0000E4HN7C5O85N",
  "X6GXMMRAX5DK6X4OX2BX1PX0Q0E0003E4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0001E4HN7C5O85NX6",
  "GXMMRAX5DK6X4OX2BX1PX0Q0E0004E4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0003E4HN7C5O85NX6GX",
  "MMRAX5DK6X4OX2BX1PX0Q0E0003E4HN7C5O85NX6GXMMRAX5DK6X4OX2BX1PX0Q0E0003Fc8F4HN7C5O85NX6G",
  "XMMRAX5DK6X4OX2BX1PX0Q22CF0200F4HN7C55NX6GXMMX5DK6X4ORAO8X2BX1PX0Qc920F0002E4H5NX6GXMM",
  "C5N7X5DK6X4OX2BX1PX0QO8RA0E0006E4HN7C55NX6GXMMX5DK6X4OX2BX1PX0QRAO80E0001F4HN7C55NX6GX",
  "MMX5DK6X4OX2BX1PX0QRAd2IO80F0003E4HC55NN7X5DK6X4OX2BX1PX0QO8RAX6GXMM1FE0100G4H5NX6GXMM",
  "dG2dFLC5N7X5DK6X4OX2BX1PX0QO8RA2CFG020844HC55N7I1G4010044HC57I5N04000044HC55N7I0400066",
  "4HC55N7If0Gf3M06000064HC55N7If0Gf3M06000264HC55N7If0Gf3M06000164HC55N7If0Gf3M0600085gL",
  "G4HC55N7I05000344HC55N7I1G4010054HC5gLG7I5N0500005gLG4HC55N7I05000674HC55N7IgLGhS7i480",
  "7000074HC55N7IgLGhS7i4807000374HC55N7IgLGhS7i4807000174HC55N7IgLGhS7i4807000844HC55N7I",
  "0400045k7F4HC55N7I29C5020054HC55N7Ik8905000854Hl1GC55N7I05000174Hl1GC55N7Il67l4M070003",
  "24HC502000G02010023420203062224N6304315330Y62200122208220032220ZG232452242G22011222182",
  "20132221q622240YYWWWWWWWWWWWXWWWeWWmWWWaWWWWWWWWWYWWWWWWWWWWWreWWXWWWWWWWWYWWWWWWWWWYW",
  "WWWWWWWmWeWWXWWWWWWWWWsWmWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWeWWWWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWWWWWWhWXZuiZY50aWXWYWWWeYfWWfWWWWnXWWWWWWWWWWWWWWWWWWWWWWWWWeWeYWWWeWmW",
  "WWWWWWWWWWWWWWWWWWWWWWeWeYWWWaXWWWWmWWWWWaWmWWWaoWXaWWWWmWWWmWWWmWWWWWWWaWYaamWWWWWWme",
  "WWWXWWWXWWWWWWWWYWXYXWWWWWYXXWWWWWWWWW00mWWWWaYWWmXWWmaWamWamWXWemWYWWaWWmaegWWYWWaaam",
  "mWWWmaWaXWWmaWeWaWWaWWmaegWWXWWYYWoWWmaWaXWWmYemWaWfeWaYWYWeWeaWfWWoWWeaeWeaeWeaeWeWXW",
  "mWYWXYYeeWWeaWeamWmemWmemWmWXWmWXWWnWoWXWmXWmmWYWWWWWW00aWWWWWWWWWYWWWWWWWWWWWWWWWWWWW",
  "WmWWWWXWWWWWWWWWWWWWWWyWWWWWWWWWWWWWeWWWWWaWWWWWWWWWWWWWYYWWWWWWWWWWWWWWWWaWWWWWWWWWWW",
  "WWWWWWWWWWeWWWWmWWWWWWWWWWWWWWWWWWWWWWWWaWWWWaWWWWWWWWXXWWWWXuW00l+/////txn+/z/+/t/sv/",
  "s//z/k//x//t/+/tlh+lx//tts+///+/t/tz/+/t/l/t//t/+/tlh/dz//xx+x/+/t/tz/+/vkf/r/bl/txtx/",
  "l/lt/jp+x//ltl/ltl/ltl/l/z+/dx/zxxll//lt/ls/+/k/+/k/+//z+/pz/+z+x/z+/z++a/x//////VXWWW",
  "WWeakXWYWXWeWfcWfWWYWnWWaWWeWXWemqXmaWWeefXWWWXWeWeYWXWeWmWeWWeWXWemqWuYWWaaXaWXWeWeYW",
  "XWcnsWgWwmWeaeaWmWmeWoiXaWWmemWmemWmemWmWYXWuaWYaammWWmeWmfWXWnWXWnWXWWYXWiYWXYXaWYXWY",
  "XXxWaWWWWWW0YWWWWWWWWWWWWYWWWWWWWWWWWWWWWWWWWWWWWWWYWWWWWWWWWWWWYWWWWWWWWWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWeWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWYWaW005B167839ABCDE"]
@[expose] def ext_full_probe_m6 : List (SigEntry × Nat) :=
  [(("full_probe_dticks_m6_hdr", [i64, .bool], [i64]), 16),
   (("m6_hdr_init", [i64], []), 0),
   (("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 656),
   (("full_congruence_dense", [i64, i64], [i64]), 720),
   (("full_dense_bin_roundtrip_fid", [i64], []), 208),
   (("full_rebuild_watches_nosort_fid", [i64], [i64]), 592),
   (("full_substitute", [i64], [i64]), 656),
   (("full_backbone_m6", [i64, i64], [i64]), 656),
   (("full_vivify_m6_hdr", [i64], [i64]), 976),
   (("full_sweep_dense_m6", [i64, i64, i64], [i64]), 688),
   (("full_transitive_m6", [i64, i64], [i64]), 656),
   (("full_has_factor_cands_fid", [i64], [.bool]), 0),
   (("full_factor", [i64, i64], [i64]), 688),
   (("full_update_classify_fid", [i64], []), 0),
   (("f64u_nlogpown", [i64, i64], [i64]), 48),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_to_u64", [i64], [i64]), 0),
   (("full_scale_delta_m5", [i64, i64], [i64]), 16)]

@[expose] def hints : List armIsa.Hints := [hint_full_probe_dticks_m6_hdr, hint_full_probe_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("m6_hdr_init", [i64], []), 0),
   (("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 656),
   (("full_congruence_dense", [i64, i64], [i64]), 720),
   (("full_dense_bin_roundtrip_fid", [i64], []), 208),
   (("full_rebuild_watches_nosort_fid", [i64], [i64]), 592),
   (("full_substitute", [i64], [i64]), 656),
   (("full_backbone_m6", [i64, i64], [i64]), 656),
   (("full_vivify_m6_hdr", [i64], [i64]), 976),
   (("full_sweep_dense_m6", [i64, i64, i64], [i64]), 688),
   (("full_transitive_m6", [i64, i64], [i64]), 656),
   (("full_has_factor_cands_fid", [i64], [.bool]), 0),
   (("full_factor", [i64, i64], [i64]), 688),
   (("full_update_classify_fid", [i64], []), 0),
   (("f64u_nlogpown", [i64, i64], [i64]), 48),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_to_u64", [i64], [i64]), 0),
   (("full_scale_delta_m5", [i64, i64], [i64]), 16)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Probe
