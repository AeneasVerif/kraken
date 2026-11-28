module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Eliminate

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rbp, Reg64.rcx, Reg64.r12, Reg64.rdx, Reg64.rbx, Reg64.r13, Reg64.rsi, Reg64.r14,
  Reg64.rdi, Reg64.r15, Reg64.rax, Reg64.r9, Reg64.r8]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rdx), (.gpr Reg64.rcx), (.gpr Reg64.rbx), (.gpr Reg64.r13), (.gpr Reg64.rsi),
  (.gpr Reg64.rax), (.gpr Reg64.r9), (.flag CondCode.c), (.gpr Reg64.rdi), (.gpr Reg64.r8),
  (.flag CondCode.nz), (.flag CondCode.nc), (.flag CondCode.g), (.gpr Reg64.r12),
  (.gpr Reg64.rbp), (.gpr Reg64.r15), (.flag CondCode.z), (.gpr Reg64.r14), (.slot 0 .w64),
  (.flag CondCode.l), (.slot 1 .w64), (.slot 2 .w64), (.slot 4 .w64), (.slot 6 .w64),
  (.slot 5 .w64), (.slot 3 .w64), (.slot 25 .w64), (.slot 7 .w64), (.slot 26 .w64),
  (.slot 27 .w64), (.slot 29 .w64), (.slot 30 .w64), (.slot 23 .w64), (.slot 8 .w64),
  (.slot 15 .w64), (.slot 14 .w64), (.slot 22 .w64), (.slot 24 .w64), (.slot 11 .w64),
  (.slot 28 .w64), (.slot 21 .w64), (.slot 12 .w64), (.slot 9 .w64), (.slot 10 .w64),
  (.slot 17 .w64), (.slot 16 .w64), (.slot 13 .w64), (.slot 18 .w64), (.slot 19 .w64),
  (.slot 20 .w64)]

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

@[expose] def hint_full_bve_collect_m7 : x64Isa.Hints := _decH #[
  "X0501112130435053606060748091A0B2805084A4B0B00240705052C0B052407274001400100014001006R",
  "66D7EF3D2B1254642006R66D7EF3D2B125464201040010230XmiWWudpuufmZpoL0XWmWWWeWWWWWWWWWW00m",
  "eYmWaXeaWYmXWWW00uYWWiXmeeWmfne00+/lw//tzlt/w/z///VXWmbWWeYmeWbWYWWW000044025"]
@[expose] def ext_full_bve_collect_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_resolve_pair : x64Isa.Hints := _decH #[
  "YO5F191618020D1A003E00030A25350A052C01012A0G2G0124100700002C0G4A0132010F0A25350A052C00",
  "002A0G2G0024110705052C01012A0G2G01242A0B10200010002000100020001000200011000B1710200011",
  "070415A074HB9D6F87IHD9F2457G201A4HB9D6F87IHD9FG2Q3OE240AmG201B4HB9D6F87IHD9FG2Q3OET014",
  "BmG10834HB9D62453020274HB9D6F8HDY9FY722417Y020184HB9D6F8HDY9FY72YC1148Y010A3ZQ54HZP403",
  "00005ZQ54HZP4B9D611501005ZQ54HZP4B9D611501005ZQ54HZP4B9D6115010304046078B2301Y422100YW",
  "fmWYifncauWWiZWuiWWucXmudWZnWmiWWucXmudWZnYL0aWXYWWWWWWWYWWWWWWaWWmmWXWWWWWaWaWWmmWXWW",
  "WWW00YWWnWWWWWWWfWWabWmYWWegXWmXWYWYmYWWegXWmXWYW00auWndaypoiWWcWWaWWWiWWeWZmfmWWWWWiW",
  "WeWZmfmW00/v/+y///////b//tr+/v//lhz+/z/x/u/v//lhz+/z/x/VcWXZWWWWWWWwWWegXWcWWmqYXWYWaW",
  "dWcWWmqYXWYWaW00016402579"]
@[expose] def ext_full_bve_resolve_pair : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_weaken : x64Isa.Hints := _decH #[
  "X55H1565051A15052E1A1E45053101050E050504010E0705053G2J1605090709070156060D074001500100",
  "842BK5F9H606I73JL1D8ZK101942BK5F9H606I73JLMD09ZK002A42BK5F9H606I73MDXCEJL18AZK10908303",
  "0510960489231A3232AI22A15221132230X2226282230322300dcWWcdWWWkdmbma/L0YWWWWWWWmYWWWWYWW",
  "WW00XWWWWfWeeXWWWWWeWeW00ZYaWWXmWXcWmWyWW00y////b/llz/////l/l/VZWWWWwWmmYWWWWWmWmW0003",
  "6402579"]
@[expose] def ext_full_bve_weaken : List (SigEntry × Nat) :=
  [(("full_extend_push_cl", [i64, i32, i32], [.bool]), 40),
   (("full_delete_binary", [i64, i32, i32], []), 24)]

@[expose] def hint_full_bve_commit_res : x64Isa.Hints := _decH #[
  "b24E121D97190903050G0G0G0301080508070101AG0E050E2B163426060720001A04000606342606072000",
  "1A040006063426060720001A040006063426060720001A040005040B17183428080721011A04010507000F",
  "0A15340405050B05010A1708090708080907290628083101080A080B58050F07010B3G4G05050B050G050B",
  "55080F071F07350503056F301G0G0501050728081A0908050721011A080124130407M00150010064H8E8MA",
  "2CD6N146010284H8E8MA2CD6NROQ308a000284HA2CDP9Q38M6NRO1F8G10294HXKE8MA2CD6NROQ3XGF09a00",
  "00AA2CDXKEP9Q3XGF4H8M6NRO15AG100AA2CDXKEP9Q3XGF4H8M6NRO15AG100AA2CDXKEP9Q3XGF4H8M6NRO1",
  "5AG101BA2CDXKEP9Q3XGF4H8M6NROXO50BG001BA2CDXKEP9Q3XGF4H8M6NROXO50BG001BA2CDXKEP9Q3XGF4",
  "H8M6NROXO50BG001BA2CDXKEP9Q3XGF4H8M6NROXO50BG003BA2CDXKEP9Q3XGF4H8M6NROa950BG00274H8MA",
  "2CD6NROQ307Y0000B4HQ3XKEaU0aUIaVK8MA2CD6NRO1FB2101B4HaUIaVKXKE8MA2CD6NROQ3b1F0Bm000034",
  "HQ3XKE032001D4HaU0aUIaVKXKE8MA2CD6NROQ3b1Fb640DbW0002G4HaU0aUIaVKXKE8MA2CD6NROQ3b1Fb74",
  "bB5b64bC10GnW0000G4HaU0aUIaVKXKE8MA2CD6NROQ3b1Fb74bB5b64bC10GnW0007K4HaU0aUIaVKXKE8MA2",
  "CD6NROQ3b1Fc48bP9b74c2PbQ6b64bCLbB50KbXW000BA4H8E8MA2CD6NROQ3e00e510Ai000H0207812340D2",
  "3637235AbF230332319XF2321023313221292211S2211C221292211I2230F2204A2303522300XWWiWpWXcW",
  "WkvcebmWWWkuWWWZuyWWZsWZpaWWWWWWkWWWfmcyWWXcWxmYiXtWauZkWfmcyXmYkzmWWWW/+L0aYWWWeWWmWW",
  "WWWWYXYWWYaYWeYXXWWWmWWWeWWneWWWYWWaWWemWWmWWWXWWWWYWWWWaWWWWWWWWWWWWWW00YWWWWaWWegWWW",
  "WWXWXWWXYXWaXWmmWWfWWWXWeeaeWYXWWYWWaeWWeWWWWmWWWXWWWWYWWaWmWWWmbeXWW00maWXWWYWWceWXWW",
  "WWWcemWWWuaeWXoafnWWWWWWadWWWWmYgWaWYWfiWaWouWeXbmWmYgWaWcimemWmWW00lv//z/tx/lZ/////y/",
  "y//yxz/tz+kl//a///z/lltl/xy+/x//tdx/l//t+///lz//+/x//t+///+Xnlz//VcWWYWeaWmyWWWWWZWZWW",
  "ZaYWeYXnmWWxWWWYWmmemWaZXWaWWeuaWmWWeXWWWmYWWXWaWWeXWWWX+kmYWW00076402579"]
@[expose] def ext_full_bve_commit_res : List (SigEntry × Nat) :=
  [(("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 296),
   (("full_add_unit", [i64, i32], [.bool]), 232)]

@[expose] def hint_full_bve_ext_need : x64Isa.Hints := _decH #[
  "F49160A2505251A053505050508110730018001004A68954602814C2015A6895460D1185C1000yhW50mWWW",
  "W00eWWmWG0ckXu00dd/+/+VuWXWX00000"]
@[expose] def ext_full_bve_ext_need : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_weaken_unit_fid : x64Isa.Hints := _decH #[
  "O4G350B131H1A1505201A0045053101050002071105240405400150010234E545I03600074E545IHHF36F7",
  "D127Z610184E545IHHF36F7DK208Z600208306021093008XA22600imWXu+bmbeS0YWWWWWWWW00XWWWWeWeY",
  "10aWWauYWyWW00d//y////l/lxTZWWWWmWma20016402579"]
@[expose] def ext_full_bve_weaken_unit_fid : List (SigEntry × Nat) :=
  [(("full_delete_binary", [i64, i32, i32], []), 24)]

@[expose] def hint_full_bve_var_m7 : x64Isa.Hints := _decH #[
  "eU3507010008090602031D1H1F1515051515050512130135053606060748091A0B2805084A4B0B09210705",
  "052C0B052107271H0H0H0812130F0935053606060748091A0B2805084A4B0B09210705052C0B052107271G",
  "0G0A0A0508050B0A0612051A053505051B29291A09390908080815071A021H0A2606281A08360609090915",
  "07150G0G05050A050A0528190B090B1G0G0A2A58090819082A052A0535053515I70808082809081104280A",
  "580808280908180909080A08080A0508090929180G0G0H0B07090907030309050A5F2F0749090903031609",
  "070909090808072J0G09091B160B062A00040505050504045A060A061G2A0606A609420752075207594508",
  "05050H0F0F1808071505072A0505070BCG0G1311471G2402100B011G05X9001500101KA0AK4EVQ5R9LFSX0",
  "THDEODPJMUUSVBX0CX1QX2LX37X4NX51X6KG100OX0T4EHDA0AKXG6J4JMX43X22VQ5R9LFSEODPUUSVBX0CX1",
  "QX2LX37X4NX5251OYW0200OX0T4EHDA0AKXG6J4JMX43X22VQ5R9LFSEODPUUSVBX0CX1QX2LX37X4NX5251OY",
  "W020BL4EYUX6A0AKVQ5R9LFSX0THDEODPJMUUSVBX0CX1QX2LX37X4NX511LX0100QYUX6ZJ6Z1HA0AKZ7FZ63",
  "Z424EVQ5R9LFSX0THDEODPJMUUSVBX0CX1QX2LX37X4NX5251QXW0200QYUX6ZJ6Z1HA0AKZ7FZ63Z424EVQ5R",
  "9LFSX0THDEODPJMUUSVBX0CX1QX2LX37X4NX5251QXW020DMb114EYUX6A0AKVQ5R9LFSX0THDEODPJMUUSVBX",
  "0CX1QX2LX37X4NX50MY0003MA0AKb11YUX64EVQ5R9LFSX0THDEODPJMUUSVBX0CX1QX2LX37X4NX51FMY0101",
  "ObD2bB6b114EYUX6A0AKVQ5R9LFSX0THDEODPJMUUSVBX0CX1QX2LX37X4NX5285Oe0200ObD2bB6b114EYUX6",
  "A0AKVQ5R9LFSX0THDEODPJMUUSVBX0CX1QX2LX37X4NX518Oe0102QbD2bB6b114EYU4YUX6A0AKVQ5R9LFSX0",
  "THDEODPJMUUSVBX0CX1QX2LX37X4NX5bR518Qm0102N4E5RX0TA0AKb11VQYUX6FSHDCX1BX0UUSVJMQX2LX3N",
  "X57X4EODP9LcEF19N2101PcIHcG2A0AKcEFb11YUX64EVQ5R9LFSX0THDEODPJMUUSVBX0CX1QX2LX37X4NX52",
  "95Pm0201QcIHcG2A0AKcEFb11YUX64EVQ5R9LFSX0THDEODPJMUUSVBX0CX1QX2LX37X4NX5cL519Qm0102N4E",
  "5RX0TA0AKb11VQYUX6FSHDCX1BX0UUSVJMQX2LX3dAX7NX57X4EODP9L15N2100N4E5RX0TA0AKb11VQYUX6FS",
  "HDCX1BX0UUSVJMQX2LX3dAX7NX57X4EODP9L0N2002N4E5RX0TA0AKb11VQYUX6FSHDCX1BX0UUSVJMQX2LX3d",
  "AX7NX57X4EODP9L15N2102OFS4EHDCX1b11BX0UUSVYUX6JMQX2LX3X0TA0AKVQdAX7NX57X45REODP9LdR50O",
  "mWW000184E5RX0TA0AKb11VQYUX608200264E5RX0TA0AKb1106200224E5R022002B4EFS5RX0TAKb11VQYUX",
  "6dAX7UUSV43HF8B4401MFS4EHDCX1b1IBX0UUSVYUX6JMQX2LX3X0TAKVQdAX7NX57X4eCX85REODP0MmWW000",
  "3M4EeTX9eOXAHDCX1b1IBX0UUSVFSYUX6JMQX2LX3X0TAKVQdAX7NX57X4eCX85R63HF859MYWWW0602O4EeTX",
  "9eOXAHDCX1b11BX0UUSVFSYUX6JMQX2LX3X0TAKVQdAX7NX57X4eCX85RfH4fHP53HF85OYWWW0500R4EeTX9g",
  "0XBfSNeOXAHDCX1b11BX0UUSVFSYUX6fHPJMQX2LX3X0TA0AKVQdAX7NX57X4eCX85RfTO53HF52RXWWWW0501",
  "X04Eg23g3Hg4FeTX9g0XBfSNeOXAHDCX1b11BX0UUSVFSYUX6fHPg62JMQX2LX3X0TA0AKVQdAX7NX57X4eCX8",
  "5RfTOg550X0mWWWW0000X0g23g3Hg4Fg55g624EeTX9g0XBfSNeOXAHDCX1b11BX0UUSVFSYUX6fHPJMQX2LX3",
  "X0TA0AKVQdAX7NX57X4eCX85RfTO0X0XWWWWW0002R4EeTX9g0XBfSNeOXAHDCX1b11BX0UUSVFSYUX6fHPJMQ",
  "X2LX3X0TA0AKVQdAX7NX57X4eCX85RfTO53HF52RXWWWW0506X2NX5QX2hCXChAXDLX3h7XEh3HgO5g62eTX9g",
  "0XBfSNeOXAHDCX1b11BX04EUUSVFSYUX6fHPh08JM7X4eCX85RA0AKfTOX0TVQdAX73936X2aWWWW0301X3NX5",
  "QX2hCXChAXDLX3h7XEh3HgO5g62eTX9g0XBfSNeOXAHDCX1b11BX04EUUSVFSYUX6fHPh08JM7X4eCX85RA0AK",
  "fTOX0TVQdAX7hG613X3aWWWW0103X0g23g3Hg4FgO54EeTX9g0XBfSNeOXAHDCX1b11BX0UUSVFSYUX6fHPJMQ",
  "X2LX3X0TA0AKVQdAX7NX57X4eCX85RfTOg620X0mWWWW0006X8g23g3Hg4FgO54EeTX9g0XBfSNeOXAHDCX1b1",
  "1BX0UUSVFSYUX6fHPJMQX2LX3X0TA0AKVQdAX7NX57X4eCX85RfTOg62i88iTXFiUXGiG9iVXEiSXCiRXDiQXH",
  "0X8amWWWW0002X7g23g3Hg4FgO54EeTX9g0XBfSNeOXAHDCX1b11BX0UUSVFSYUX6fHPJMQX2LX3X0TA0AKVQd",
  "AX7NX57X4eCX85RfTOg62i88iTXFiUXGiG9iVXEiSXCiRXD0X7amWWWW0003R4EeTX9g0XBfSNeOXAHDCX1b11",
  "BX0UUSVFSYUX6fHPJMQX2LX3X0TA0AKVQdAX7NX57X4eCX85RfTO53HF52RXWWWW0501B4EFSkO35RX0TA0AKb",
  "11VQYUX6dAX70B8003D4EFSkO35RX0TAKb11VQYUX6dAX7l2FU4UU0D800244EFSkO35R04800734Em13lTD11",
  "301003lTD4Em6103000YR02008243MA37622313D23OA223FA123UA023TA023PA12354123Q50432126P343R",
  "A26O4233B383E934738C3N8041A03BAX423B1141AZ/////V3BA041AZ/////V3BA123B1F23B1141AZ/////V",
  "3BA323B1A226RYP22ABYO23SAX4230144231210F226B723L802301123015226P22214122A34439A235523C",
  "AE233C1221022210A223334361210043A835612231C2266422BC522655432A3010208A062A2210231G23DC",
  "462A22102310A3G53HA2A22102312226E2226GA22COC22A2122A2122A2022AE362A221023122214362A221",
  "0231H23HA023IA023JA123G6843DA3K3062A2210231362A2210231262A22102319226K3226G1226H3226D6",
  "226J3226I462A2210231062A2210231062A2210231022A2722A2E2301422AQ8223U4223T22231523010221",
  "062231D2301G202A0XWWunjeXueeaaWWXmeeWWWWWWWcuxksXnWW+mWcYeXmWWWXyWxWWWWWcWWWeuWvZWWl/z",
  "kkccWYXueWmWWWXeWWWWXusWeWWZniWZnaWWWWWWiZWWcXy+cYiWyygWWWucWWiZvyiauXvveqrgW10eYaWYWW",
  "WWWWWWaaWWWmaYWeWWWWWWWaXYWWWWWWmaWXWWXYWWXWWXWWWXWWWWWWoWWWWWWWWmWWWmXWXWeWWWXWWWWWXY",
  "WWWWeWWWmWoWeaWWWYWWWWWWWWWWWWmeWWWaWWWWWWWWWWWWWWW00XYWXeWWWWWWmYYYWWWYXWaWWWWWWWYWnW",
  "WWeemgYWWmWWmWYWnfeWWeWWWYWWWXWWWWWeeWWWWWeWmqYaWWYmmWXWXWnWWYWaWYWemfgaYWqWXWgXWWqWeW",
  "WWWeaXeWYWqYWXeWmWWWWWWW40eWWWWWWWWWWaWXXZiWWWWWWWeWWWWWWWYeWWWWWWWWWyyWeWYaWWZmWWWkWi",
  "XuWWWWZZXWWWmWWWWWWXWWWWWWiyZmWWWvucWfuWWiWWWWcWmWZWiYYWaYigWiWWiXWWcWuaaWeauqWWWWW00l",
  "xt/zx/yl/////+dxuf///vy/p//////xx+z///lk/Zx/+d/+//x+iWl//j///x///z/////ll/////l++tvtzl",
  "w+l/z/z+y//x/t/x/kljhtx+t/z/hz/+t/l////ltzl/x+tx/zl+////////7aeWYaWZmWWWWWXuadsWWWcZWi",
  "WWWWWWaaXYWWWmnWyaWXuWXWWaXp/mWWoWWWaWWWYWWWWWmmWWWWWmXXeceYmbXmWYWYXZWWaWeWaWnmoqeaXe",
  "WYWqYWXeWmWWWWmeYmWaXeaWYmXWWWWWWWWO00V6402579"]
@[expose] def ext_full_bve_var_m7 : List (SigEntry × Nat) :=
  [(("full_bve_weaken_unit_fid", [i64, i32, i32, i32], [.bool]), 88),
   (("full_set_inactive", [i64, i32, i32], []), 72),
   (("full_bve_gates_m7", [i64, i32, i32, i32], []), 472),
   (("full_bve_gates_fid", [i64, i32, i32, i32], []), 888),
   (("full_bve_resolve_pair", [i64, i32, i32, i32], [.bool]), 56),
   (("full_wstack_defrag_m6", [i64], []), 136),
   (("full_bve_weaken", [i64, i32, i32, i32], [.bool]), 120),
   (("full_bve_commit_res", [i64, i64, i64], [i64]), 408),
   (("full_dense_prop_unit_m7", [i64, i32], [.bool]), 312)]

@[expose] def hint_full_bve_var_key_m7 : x64Isa.Hints := _decH #[
  "YD222B140E0E35053909071609074A010505274A000505010B1E0E35053606071406074A000505274A0905",
  "05000B1B010B00050501012A15250515200507040B00000408080500050B051B050105600150010146248B",
  "4CE114010166248B4CEQ6R92516020336248XI1103010156248XI1Y14Y26250502031Z111510101020468X",
  "051052A51052X051052A51052ZewiWWWlWZuaddWWdmXyYZpn60eWYWWWWWWaWXWWWW00amWWmWWmWaWXXWWWe",
  "WYWWmmWW80mWqWXWeWeWYXWmeWZYmXWmeaWXne00ltt/Y//+/w+e/sdzz///alxZ++///FeeWzWWXWbXtWfuYY",
  "WWWxmayXXWWWG000240"]
@[expose] def ext_full_bve_var_key_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_heap_up_m7 : x64Isa.Hints := _decH #[
  "O421E000B0719180D25050B260E0E0A140421010B3B450A353000000033F9ID6I15341007F9ID6ISEH8Q68",
  "2157410242303XK22300ZWZiycWZXom50XWWWWWWWWW00mXXWXWeWb00XWXaaYmfWuW00//+/zz/z/XonVXWYY",
  "WYW+jk00013402"]
@[expose] def ext_full_bve_heap_up_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_heap_down_m7 : x64Isa.Hints := _decH #[
  "X64D1F000B0715140129090B2H0F0F00010B58080B2206072E0E0720070802063B282900010B3940000000",
  "33F5II6K19341008F5II6KH48D53SFQH3019843029X29F5II6KH48D53SFQH3826983050205632313E2301X",
  "R2231122100iWZcWcXmicWZXom50maWWWWWWW00YWWmWeYXWaWeWb00aWXoWYWmaYWfWuW00Z//v/+u/lxz/p/",
  "XonVcWXdWmaYWiW+jk00026402579"]
@[expose] def ext_full_bve_heap_down_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_heap_push_m7 : x64Isa.Hints := _decH #[
  "Z442110H0B071F1334012000070B250D02050B07060E0021010B13050H0A190928080B3B410A310707030F",
  "0B0700040529090B1H0F0F05080B51010B2206072E0E0725070102063B212905080B3902030B0705060021",
  "010B1E03030A190928080B3B410A31A001D001041X0D0100034X0DX56X706I11481008X0DX56X706IXGHX6",
  "EXE3X12118810415D01000545DYE0YGK6I194810085DYE0YGK6IYF4YA3YPFYNH3589883029YV95DYE0YGK6",
  "IYF4YA3YPFYNH31269G30745DaB5aD06I114810085DaB5aD06IaM3aC6aKEa72118810904026008C4303311",
  "42211A22A0XM2270R231AXQ2270122A1XN22700iWjpmuWeiWWXmWiuWucXmuWeiWWWWiWjpmuWeiWWiXnom50",
  "aWWWWWWWWWWWWWWWYWmWWWWWWYWWWaWWWWWWWWWWWWWW00YWaaWaYWbWWWeWYWXWeaWmYWbXeWWYWaaWaYWbWX",
  "eWWb00aWammgXWcWWWmWceWeYWmeXWcWWWWaWammgXWcWWaauWW00///x/tt/tuiX///d/xZz/lt+luiXyl//x",
  "/tt/tuiX/yl//nVaWeeWedp+WWWuWayYWmeXmdp+ZmWWaWeeWedp+WZmWWk00026402579"]
@[expose] def ext_full_bve_heap_push_m7 : List (SigEntry × Nat) :=
  [(("full_bve_var_key_m7", [i64, i32], [i64]), 24)]

@[expose] def hint_full_bve_heap_pop_m7 : x64Isa.Hints := _decH #[
  "XN35100G0715010107012D0A21010700230F0B0700160524040B2H0F0F09050B51010B2208072E0E072907",
  "0102083B212409050B3405070560015001026EK7I48D590540610012EK7I0210055EK7IX20X5POL145H100",
  "AEK7IX20X5POLX46U3KDXFFXDH3954AH302BXL4EK7IX20X5POLX46U3KDXFFXDH3128BX23085230A52311G2",
  "321M233AXR2212122A3422A1122A10XmWiuWucXmuWiceWuXmcWe50YWmWWWWWWWXWaWeW00eWYWXWeaWmXWXe",
  "WmYWaYG0eWmWceWeYWmeXaZWWiWmZWW00+///d/xZz/lt+lyceWw/x/tuVXWWWuWayYWmeXmZvt/bWaWed0004",
  "6402579"]
@[expose] def ext_full_bve_heap_pop_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_bve_collect_nbrs_m7 : x64Isa.Hints := _decH #[
  "YD391314151E11161H000821010735053F0F0F0741081A0B21050102022A3E0A2535050A05074A3G2G0720",
  "11071705050A05074A3G2G0720172715071A0B340454045404540421040B1735052107D0010001002J6LH1",
  "020100CLHJ679B4935DDMN8NNMOHLFI205CX0200CLHJ679B4935DDMNNMOHLFIP510CX0101ELHJ679B4935D",
  "DMNNMOPPHLFEFIX7F205EX0200ELHJ679B4935DDMNNMOPPHLFEFIX7F205EX0204EXL5LHJ679B4935DDMNNM",
  "OPPHLFIX7F10EY0100GLHJ679B4935DXO2XLKDMNNMOPPHLFIX7FXVE201GXWX0201HLHJ679B4935DXO2XLKD",
  "MNNMOPPHLFIX7FXVEY2110HXWX0108FXE8LHJ679B4935DDMNNMOPPHLFEFIX7F10FY01093ZU0J6LH1130100",
  "3ZU0J6LH11301003ZU0J6LH113010902026923007836835332134A022157433A244A2200N22823231AXG22",
  "000XpWWizpskvmWWWXmZZnyWWWWiWuylWXuZpWufmZpmWrgL0mWaeWWWWWWWemnWYeeaXYWemWoYXWemWWWWWW",
  "WWWaWWW00eWYaWWWWWWXaeemXaaYWnWaeWfXWmaeWeaWYmXWWYWWW00vWYcivpcimWWWWmWWmWWWWWaWWaWWWy",
  "XmeeWmfnWWWW00dd/xp//////ytdk/zttx+b/td/jz+/nl/lt/w/z//x///VuWaiWWWWWWZeunWYeeaXwWeuWo",
  "YXWkmWmeWbWYWWaWWW00076402579"]
@[expose] def ext_full_bve_collect_nbrs_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_elim_bve_m7 : x64Isa.Hints := _decH #[
  "bI3H151E111911180A0BA5000B173507490E9B1A1G1G0305271G240D110B051G0D0A0BA5010B1735070A45",
  "050G3G0023071G3A1G1G1701080G07010D000700230A2000070825010B0705040828080B20010106010B50",
  "000B2D09072F0F072607000D093B202806010B3801070D151G010B20080A3A00351G1A0G0F01271G240D10",
  "0B011G170F0A400007211A3G012D072A2A30075G001B0G2G2A15070105050B050A0BK5010B1755070A0BK5",
  "010B1755072A05X90015001007425X99N7HDOBEF90700009BEF942J8H15X99N7HDO15901009BEF942J8H15",
  "X99N7HDO15901009BEF942J8H15X99N7HDO15901053427H5X93158303006425X9XFE9N7HDO358XE6030474",
  "25X9XFE9N7HXNXEDO070000842Y035X9XFE9N7HXNXEDO15801008425X9XFE9N7HXNXEDOY250800048429N7",
  "H5X9YHDXNXEXFEDO0800008425X9YHDXFE9N7HXNXEDO15801008425X9YHDXFE9N7HXNXEDO15801008425X9",
  "YHDXFE9N7HXNXEDO15801057427H5X9XFE9NXNXEDO14701009429F9N7H5X9YHDXNXEXFEDO24390201A429F",
  "9N7H5X9YHDXNXEXFEDOZA314A01047427H5X9XFE9NDOXNXE315X1703007427H5X9XFE9NXNXEDO25X170200",
  "7427H5X9XFE9NXNXEDO25X1702049ZSX1425X9XNXE7H9NXFEDOZR51D90102DZSX1425X9XNXE7H9NXFEDOZR",
  "5aAXAa5Pa91a680Dm0001BZSX1425X9XNXE7H9NXFEDOZR5aAXAa5P0Bm0005EZSX1425X9XNXE7H9NXFEDOZR",
  "LaAXAa5PaU5b0X6aKXB18Eem0100KZSX1425X9XNXE7H9NXFEDOZRLaAXAa5PaU5b0X6aKXBaV4aVKaQIaG3bA",
  "Rb8M3618Kem0302LbG8ZSX1425X9XNXE7H9NXFEDOZRLaAXAa5PaU5b0X6aKXBaV4aVKaQIaG3bARb8M30D9Ln",
  "W030BBcSI427H9NDO5X9XNXEdD3XFEZSX1dEK0B0000C42dKFcSIdD3ZSX1dEK7H9NDO5X9XNXEXFE11C0100C",
  "cSI427H9NDO5X9XNXEdD3XFEZSX1dEKdM10C00047427H5X9XFE9NXNXEDO25X1702019427H9Ne7FDO5X9XNX",
  "EdD3XFE24D90201A427H9Ne7FDO5X9XNXEdD3XFEeAD14A0109142010001342fF07H030000342fF07H03000",
  "7342fF07H1530100342fF07H1530100342fF07H1530105342fF07H1530100342fF07H1530100342fF07H15",
  "3010X402048A23513436A3C6XK41A03DA1226CZ8206A741A038AD226C4233162392E23A33232A9230A423B",
  "89237114343316X72217A223A1221B022A2022A2022A2022A202229L22666230A0205A0231AX422A1541A1",
  "38A322A5E22865206A341A138AO23D3A226C0uZuWZz+/lWWZuWZz+/lWWWaXnmYXmWWWWWWXusXmXXWWunWaX",
  "mycXWWXmWiuWucXmuWicWXmZWiWWYaemWWyZWWuWYrgsWWeWcaeYaetvwWuWYrgsWbgL0XWXYWWWWWWnWXYWWW",
  "WWWmXWWaYeaWeoWWnWaYWmWaaWeYaWWWWWWWWWWWWWWWYWmWWWWWWWYWeWmWWnYWeYXWaeXYWWWWXXWYWnWenY",
  "WWWeXYWWWWXWW00mWnWWWWWYemWnWWWWWYeWmYYXaYWaXWWemYXWeXYYWWXYXfWXXWoWWWWeWYWXWeaWmXWYmX",
  "WaWegaenYaXWmYaWnWWWWammWWemaenWWWaWnWWWWamW00eWmicZXWWWeWmicZXWWeWWWWWWWWWWWWWWeYWmWW",
  "WWeWWWWWaYWWeWmWceWeYWmeXaZWWuXWcWWWWWWWWaXWWeWmWWYWWWWYWWWWWWYWWeWmWWYWWW00j+l+y/////",
  "vkl+y/////vjw/xxztx/pz//klxz/lzxxt/zxzj/zy+Z+///d/xZz/lt+lycWXr/t/lZtkzxpz+lxp+y////o+",
  "z//k/tkz///p+y////o//VYXmXZWWWWWcnmXZWWWWWcobWaaYeaWiYWWnmaYWmYaaeWYaYoWYZXyXWWWuWayYW",
  "meXmZv/+gWeWmyenYaiYXmaiXZWWWWjXYWWnWenYWWWiXZWWWWjWW000E6402579"]
@[expose] def ext_full_elim_bve_m7 : List (SigEntry × Nat) :=
  [(("full_dense_prop_unit_m7", [i64, i32], [.bool]), 312),
   (("full_bve_heap_push_m7", [i64, i64, i32], [i64]), 104),
   (("full_bve_collect_nbrs_m7", [i64, i32], [i64]), 104),
   (("full_bve_var_m7", [i64, i32], [i64]), 1192)]

@[expose] def hint_full_has_elim_cands_fid : x64Isa.Hints := _decH #[
  "92011140A5A3G1A05073001500100381A4601530101481A460C50400000eylWL0XWYXWW00mnWmY00aXW00k",
  "kz+/xVXnYXWa00000"]
@[expose] def ext_full_has_elim_cands_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_eliminate_m6 : x64Isa.Hints := _decH #[
  "YD3E150105051511051105051B0318082107000B050500040401050431052011140A055A3G1A050705152A",
  "05150B03050D0D1G11190A0BA5000B1735073110000B01000B3A111401012A1G0G2A05E0015001003427E5",
  "D15301014427EO35D0400014427EO35D14401023427EO30300016427EO3XJ1XL4XH015601017427EO3XJ1X",
  "L4XH0XO50700063427EYJD0300005427EYJDYP9YN115501005427EYJDYP9YN115501005427EYJDYP9YN115",
  "50105442ZH5ZGD7E1040102542ZH5ZGD7EZR01150101442ZH5ZGD7E04000404026048Z8230A22210XH202A",
  "0uWpWfmWbWXmWbgriWgWYcWWWnu+WgmoWWWWaWom50YWWmYaWWWWYWWWWeYWaYWWWWWWWWWWWWa00YmaWYXXWW",
  "eXYWWWWfWmWWWXXYXWXWWWWWamWWWW00mXWWWaWWWWWWWWWeYWWWWWqWWWYWX00dzw/t/xzz//dzv////b+/ll",
  "/yzxz/z/////Y/+///VYbWeWaYYWWuYcWWWWwXWmmWZYaYWYWWWWWzWXWWW000144025"]
@[expose] def ext_full_eliminate_m6 : List (SigEntry × Nat) :=
  [(("f64u_nlogpown", [i64, i64], [i64]), 72),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("full_scale_delta", [i64, i64], [i64]), 40),
   (("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 792),
   (("full_forward_sub_m7", [i64, i64], [i64]), 552),
   (("full_elim_bve_m7", [i64, i64], [i64]), 1368),
   (("full_rebuild_watches_nosort_fid", [i64], [i64]), 728)]

@[expose] def hints : List x64Isa.Hints := [hint_full_bve_collect_m7,
    hint_full_bve_resolve_pair, hint_full_bve_weaken, hint_full_bve_commit_res,
    hint_full_bve_ext_need, hint_full_bve_weaken_unit_fid, hint_full_bve_var_m7,
    hint_full_bve_var_key_m7, hint_full_bve_heap_up_m7, hint_full_bve_heap_down_m7,
    hint_full_bve_heap_push_m7, hint_full_bve_heap_pop_m7, hint_full_bve_collect_nbrs_m7,
    hint_full_elim_bve_m7, hint_full_has_elim_cands_fid, hint_full_eliminate_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_extend_push_cl", [i64, i32, i32], [.bool]), 40),
   (("full_delete_binary", [i64, i32, i32], []), 24),
   (("full_watch_push_slow_m6", [i64, i32, i32, i32, i32], [.bool]), 216),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 296),
   (("full_add_unit", [i64, i32], [.bool]), 232),
   (("full_set_inactive", [i64, i32, i32], []), 72),
   (("full_bve_gates_m7", [i64, i32, i32, i32], []), 472),
   (("full_bve_gates_fid", [i64, i32, i32, i32], []), 888),
   (("full_wstack_defrag_m6", [i64], []), 136),
   (("full_dense_prop_unit_m7", [i64, i32], [.bool]), 312),
   (("f64u_nlogpown", [i64, i64], [i64]), 72),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("full_scale_delta", [i64, i64], [i64]), 40),
   (("full_enter_dense_ex_fid", [i64, .bool], [.bool]), 792),
   (("full_forward_sub_m7", [i64, i64], [i64]), 552),
   (("full_rebuild_watches_nosort_fid", [i64], [i64]), 728)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Eliminate
