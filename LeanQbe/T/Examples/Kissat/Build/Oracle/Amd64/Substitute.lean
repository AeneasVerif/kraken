module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Substitute

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.r14, Reg64.rcx, Reg64.rdx, Reg64.rsi, Reg64.rax, Reg64.rbx, Reg64.rbp, Reg64.r12,
  Reg64.r13, Reg64.r15, Reg64.rdi, Reg64.r8, Reg64.r9]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rbp), (.gpr Reg64.r9), (.gpr Reg64.r13), (.gpr Reg64.r15), (.gpr Reg64.rsi),
  (.gpr Reg64.r12), (.flag CondCode.nz), (.gpr Reg64.rbx), (.gpr Reg64.r8), (.flag CondCode.c),
  (.gpr Reg64.rdx), (.flag CondCode.z), (.gpr Reg64.rcx), (.flag CondCode.nc), (.gpr Reg64.rax),
  (.gpr Reg64.rdi), (.gpr Reg64.r14), (.slot 0 .w64), (.slot 1 .w64), (.slot 17 .w64),
  (.slot 8 .w64), (.slot 11 .w64), (.slot 15 .w64), (.slot 16 .w64), (.slot 6 .w64),
  (.slot 14 .w64), (.slot 12 .w64), (.slot 3 .w64), (.slot 9 .w64), (.slot 5 .w64),
  (.slot 10 .w64), (.slot 7 .w64), (.slot 4 .w64), (.slot 2 .w64), (.slot 13 .w64),
  (.flag CondCode.l)]

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

@[expose] def hint_full_tarjan_pop_scc : x64Isa.Hints := _decH #[
  "S501112131415260728090A0B272C094A0A3A0A3B062D0A195E090C195094FH4F37GB1D290J55H2E89e820",
  "0A4FH4F37GB1D290J55H6C2EAAu82022UE4F1720100BUI4FV8H4X3HF37GB1D290J527EBY0202CUI4FV8H4X",
  "3HF37GB1D290J5X6E17CY01040400101282303L4301314X222100XjoeWjnXmdYvmiWiXgL0mWaaYWWWWWWWm",
  "W00meWYYXeWWXWaWeW00mWWWmWWWmamWWaWW00//+/d/xxzl//z/n/l/VXWuWaaYmWWYWkWmW00026567809"]
@[expose] def ext_full_tarjan_pop_scc : List (SigEntry × Nat) := []

@[expose] def hint_full_tarjan_scc : x64Isa.Hints := _decH #[
  "aB21011C1A141E1G121F1810060D090E0F0D080D000D0E0D0E0E0D0E0E0D0E0DEE080D19791B3B000F4600",
  "0E0F184F4B000E230F1E0F380849032F260502020G0E0E0E26052F09080B23094F0F3F0F3B062D0F195509",
  "0F1956380839160E0F2F1B0E0F0F090808463B1F0339031875260E0610060E0D4B08383B08383B08383B08",
  "3E080D190E4B083E090E4EM001E00100DD4BA9C4771FJJ2JKHGHLPMNNLO1ED0100DD4BA9C4771FJJ2JKHGH",
  "LPMNNLO1ED010CD47FJD4BAJ2JKHGHLPM71NNLO9C2E0D020059CD4BA4771050002E47FJD4BAJ2JKHGHLPM7",
  "1NNLO9CY701EE0102G47FJD4BAJ2JKHGHLPM71Y70NNYNPLO9CYVQ3RS5G0302HZ0RZ6T47FJD4BAJKHGHLPM7",
  "1Y70NNYNPLO9CYVQ1SH0101OZ0RZ6T47FJD4BAJKHLPM71Y70NNYNPLOZ1Sa4UYVQa3VZVX0a12a2X1a0Ha5I9",
  "C2EGO0200PZ0RZ6T47FJD4BAJKHLPM71Y70NNYNPLOZ1Sa4UYVQa3VZVX0a12a2X1a0Ha5I9CZ932E8PmWWW02",
  "02IZ0RZ6T47FJD4BAJKHLPM71Y70NNYNPLO9CYVQZ1SaGE13I0100RZ0RZ6T47FJD4BAJKHLPM71Y70NNYNPLO",
  "9CYVQZ1SaGX2aHGa4Ua3VZVX0a12a2Ea2X1a0Ha5I235R0202SZ0RZ6T47FJD4BAJKHLPM71Y70NNYNPLO9CYV",
  "QZ1SaGX2aHGa4Ua3VZVX0a12a2Ea2X1a0Ha5IaL513S010BHZ1S47FJD4BAJ2JKHGHLPM71Y70NNYNPLO9CYVQ",
  "2R5H020659C4771D4BA1E5010059C4771D4BA1E5010059C4771D4BA1E5010269C4771dNED4BA06000169C4",
  "771dNED4BA06000169C4771dNED4BA06000169C4771dNED4BA06000369C4771f1ED4BA06000T0205AC23B0",
  "12388683F63GB36A3H4Z322BFD227H4A3CA3E43341B039BB2354422B65430B2B6942492AE1230822374023",
  "A406314320347622A0823D4422A0J42B72949424C2BAI224A7220B0620B141394J228802288422BGG224FP",
  "224H923390XhWbmdWWbmdbmdbmdbmdWWWWYximZokdmWbmWddWWjmmWxYZWkbpWWcWWZildauajoWZudYZrWXg",
  "rgriWWWWWWWWrgr90YWWmYaWWmWWmWWmWWmWWaYWWWWeWWmXWWWmmWeWWWXWWeeaWWWWWWeWWWWWWWWWWWWWWe",
  "mWmWWWWWWYYYYaefaWWW00XWWeXYWWeWWeWWeWWeYaYXWWWWaWmeWmeWeeWaWWXWmWaaYmWWYYWaWaWmWWWeWW",
  "WaWeaeWemWWWWWfXXXYaaoWWW00XWXWWXWWXWWXWWXWWWWWWaWWuWWuWWyWXpWWWmWWXWWWXWfWWYWWWYZYmWW",
  "WmWWeWWWWWeWWWWWWWWWWWWWWWW00//y//lzv//l//l//l//lvtxz////t+/l+/l/ll/t//z+l/ttw///xu/t/",
  "t+////l///t/ltl/kl/////k++avpoh///VZWWmYcWWmWWmWWmWWmceaYWWWWeXWmXWmWmmWeWWYXmWeebWWWa",
  "dWeWeXWWWWmWWWeWmemWnmWWWWWnXXxcijqWWW000I6567809"]
@[expose] def ext_full_tarjan_scc : List (SigEntry × Nat) := []

@[expose] def hint_full_subst_elim_vars : x64Isa.Hints := _decH #[
  "Y635063410091B26151G1266560E0E0F2A060C08040D0E0E2F08080F01030F0908083B2X31309040904210",
  "133030A0C0C0A0F040A090C0C3B2X3180C0F090F090F2E0E38080420099001E00100147010000347527510",
  "30105447M5OGQ21040101547M5OGQ2X20050003747M5OGQ2X20X9EXDA07Y0000B47M5OGQ2X20X9EXDAXFCX",
  "QFXNHXH418BY0106547M5OGQ2X20050000747M5OGQ2X20YQAX9E14701020408305AY6230A0ZWWkZWWZZmWW",
  "WdXmWcdWWXmWZWlX/gpWWc10YWWWWWWWWeXWWWWWWWWmYWWWWmXWWWWWWnW00XWWWWWamaaWmWWWWYeeeXWWWm",
  "eWmYWWaeeW40cXYWWWuWWWZWnWWXmWWuWXqXWWWWWWY00Zy/////o/tt+/////vlllz//+dl+/x//tld/NZWWW",
  "WWjWeeXWWWWWcmmmYWWXumXWaWWemuW80016567809"]
@[expose] def ext_full_subst_elim_vars : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 232),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_set_inactive", [i64, i32, i32], []), 72)]

@[expose] def hint_full_subst_rewrite_bins : x64Isa.Hints := _decH #[
  "a5361E0E1C1A17101415264E0E38080B2F0801096E0A1B0404092G1B0B041F0F1B090E060E0F0F2C04090E",
  "060E0E060E0914041B0904043239097E0C0129390E0D3A160A0A4A160A0A4A160A0A4A160A0A1C0A0D193E",
  "160E0E1C09060D34044404440444041A040D193E0E1A09090E0DAE0A0D193E090E0E1816341A0B1B0B161G",
  "090E090E09T001E001019AX1CVECEKG7I043M5KX01E90102CVEVTI0G7X98M543EKQHKX0AX1CV32F1C0300D",
  "G7X98CVAX1VTI043QHX8RXAOM5KX0EK42I1CDe0402JXC2XDIXJAG7X98CVAX1VTI043QHX8RXAOM5KX0EKXFC",
  "XIEXM41GJaYW0101EXJAG7X98CVAX1VTI043QHX8RXAOM5KX0EK32ICEm0300JXDIXFCXJAG7X98CVAX1VTI04",
  "3QHX8RXAOXC2XSGM5KX0EKXM40JYW0006IXDIXFCXJAG7X98CVAX1VTI043QHX8RXAOM5KX0EKXC2XSG0IYW00",
  "06FXC2XDIG7X98CVAX1VTI043QHX8RXAOM5KX0EK21CFXW0202EZN1X98ZL2I0M543ZMFEKQHVTG7KX0AX1CV0",
  "E0000EI0G7ZL2ZN1X98M543ZMFEKQHVTKX0AX1CV1CE0100EI0G7ZL2ZN1X98M543ZMFEKQHVTKX0AX1CV1CE0",
  "100EI0G7ZL2ZN1X98M543ZMFEKQHVTKX0AX1CV1CE0102FI0G7ZL2ZN1X98M543ZMFEKQHVTKX0AX1CVZRC0F0",
  "001FI0G7ZL2ZN1X98M543ZMFEKQHVTKX0AX1CVZRC0F0001FI0G7ZL2ZN1X98M543ZMFEKQHVTKX0AX1CVZRC0",
  "F0001FI0G7ZL2ZN1X98M543ZMFEKQHVTKX0AX1CVZRC0F0003FI0G7ZL2ZN1X98M543ZMFEKQHVTKX0AX1CVb4",
  "C0F0002EZN143ZL2ZMFX98EKQHVTG7M5KX0AX1CVI00E0000EZN1X98ZL2I0M543ZMFEKQHVTG7KX0AX1CV1AE",
  "0100EZN1X98ZL2I0M543ZMFEKQHVTG7KX0AX1CV1AE0100EZN1X98ZL2I0M543ZMFEKQHVTG7KX0AX1CV1AE01",
  "05E43M5KX0AX1CVEKQHZL2G7I0ZMFX98ZN1VT0E0000E43ZL2ZMFX98ZN1EKQHVTG7M5KX0AX1CVI01EE0100E",
  "43ZL2ZMFX98ZN1EKQHVTG7M5KX0AX1CVI01EE0100E43ZL2ZMFX98ZN1EKQHVTG7M5KX0AX1CVI01EE0106AAX",
  "1CVEKG7I043M5KX0QAQH0A0000A43M5KX0AX1CVEKQHZL2G7I01GA0101B43M5KX0AX1CVEKQHZL2G7I0dJG0B",
  "000G0209AL8343382371324523044222022354222373436C33A14180318E22A7122A3XG414131494141314",
  "54243234cK221514218220B22440mXiXeWiWXgrhWWXcWWpqzdfmWWmhWWaYymhoXkebmWWZzmWhWXaWWWWuWW",
  "amWuXcWiddXrgqJ0YWmmmWWWWWWaWnWWWWWemWemWWWWWWemXWaeWeWXWWaWWmWaeWWaeWXaXYWnWWXYWYeYWW",
  "WWWWWWWW00XWeeWXbaWeWYWemWWWYaeWaeWWWWWXaeWmYaWaWWmWYWWeXYaWWYaWWoWnWemWWneXaXYWaXWWYW",
  "WW40nWaWeWWXXWWoWafoipamWWeXWYYWeeXXWaaWmmWXimWWWWWWWWeeWWWWWeWYWaZYWWWW00Xy/dd/znt/l/",
  "v/kl///vtd/td/////ytd+/xp/t/+//x//lyxt//xt/+x+y/k//+zlztzx/tz//x///NZWuuWYkeWmWcWnmWWW",
  "ceuWeuWWWWWZeuXWaiWeWXWWaWWmZaeWWaeWXaXZWnWWXYmYeYaWeYWWaWWW80096567809"]
@[expose] def ext_full_subst_rewrite_bins : List (SigEntry × Nat) :=
  [(("full_add_bin_m6", [i64, i32, i32], [i64]), 296),
   (("full_add_unit", [i64, i32], [.bool]), 232)]

@[expose] def hint_full_subst_rewrite_ar : x64Isa.Hints := _decH #[
  "ZD361115171G0G2A062C0C0E340300030E0968080E09160E19360E090A0E0E0A0A1316093E0E09361E3E0E",
  "09360A092E3E0E2E0808260E2B08301A09360D1A3A0A1A0A3A0A1A0A3A0A1A0A3A0A1E0A0D191A3A0A1E09",
  "09094B0E04043E0E0E040E0B1B241B243A1B0B160A091A09K001E001017B5GG919I4F4HD72A2702007B5GG",
  "919I4F4HD71370101BB5GG919I4F4HOCD7T4M2PR13BXe0103DV0LAB5GG919IM2T4PR4F4HOCD71EDi0100DB",
  "5GG919I4F4HOCD7T4M2PRXGELA0DXe0004C919IM2T4OCPRD74F4HXU3B5GG0CX8000C919IM2T4OCPRD7B5GG",
  "XU34F4H1ACX8102D919IM2T4OCPRD7B5GGXU34F4HYCA0DX8003C919IM2T4OCPRD74F4HXU3B5GG280CX8200",
  "C919IM2T4OCPRD74F4HXU3B5GG2A0CX8201D919IM2T4OCPRD74F4HXU3B5GGYQA10DX8102EXU3B5GG919I4F",
  "4HM2ZN0ZM8T4OCPRD70EbW0000E919IM2T4OCPRZN0ZM8D74F4HXU3B5GG1EEX8100E919IM2T4OCPRZN0ZM8D",
  "74F4HXU3B5GG1EEX8100E919IM2T4OCPRZN0ZM8D74F4HXU3B5GG1EEX81058XU3B5GG919I4F4HD7080000EX",
  "U3B5GG919I4F4HD7M2ZN0ZM8T4OCPR0EgW0004BXU3B5GG919I4F4HD7M2ZN0ZM80B0002BXU3B5GG919I4F4H",
  "D7M2ZN0ZM80B000A0230A5231CN2334X92243aP2243X3232B262C12A02B2I22A0122C1222A01XU51eZsWXm",
  "YWWXuXkWWayWWpndYkayWeWkXnnpmWdWyZmkYWWXuWmluXuWvgJ0aXWWWWWmeaWWWWWaWeYWWemWWWWWWWXWmW",
  "aWWWWWWeWWaWWWWaYWWWWWWWWW00YWmWomWeWYWeWWWYWbXWWaeWWWWWWWameWYYWWWeeaWaYWqWWYXXaWYWWY",
  "WW40XoWWmWWmW+WcWWYkWafypvdokWWWdWeevuWXWkWmaWWaWeWXceWvWWW00Zx+/+u//l/x/l///x/ny//td/",
  "//////o/d/xx///ddt/px+t/pxzzmlv//x//NaXWXdWWmWaWmWWWaWkZWWeuWWWWWWWjWuWaaWWWuueWiaXeWi",
  "aYYlmcWWaWW80046567809"]
@[expose] def ext_full_subst_rewrite_ar : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 232),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 296)]

@[expose] def hint_full_substitute : x64Isa.Hints := _decH #[
  "H362B264B1B05261B1B26261B0B161B02095001E0010014701000300000001471210104247G20200020205",
  "AR20640mYXWaWeahci30aWWWmeXaWnWWW80YfbaYWemmemem4000X//vjntx/k+/k/k/NcokeaWnXWnWnW8000",
  "45678"]
@[expose] def ext_full_substitute : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_tarjan_scc", [i64], [i64]), 200),
   (("full_subst_elim_vars", [i64, i64], [.bool]), 760),
   (("full_subst_rewrite_bins", [i64], [.bool]), 424),
   (("full_subst_rewrite_ar", [i64], [.bool]), 392),
   (("full_arena_sweep_m6", [i64], [i64]), 504),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696)]

@[expose] def hints : List x64Isa.Hints := [hint_full_tarjan_pop_scc, hint_full_tarjan_scc,
    hint_full_subst_elim_vars, hint_full_subst_rewrite_bins, hint_full_subst_rewrite_ar,
    hint_full_substitute]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 232),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_set_inactive", [i64, i32, i32], []), 72),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 296),
   (("full_backtrack", [i64, i64], []), 168),
   (("full_arena_sweep_m6", [i64], [i64]), 504)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Substitute
