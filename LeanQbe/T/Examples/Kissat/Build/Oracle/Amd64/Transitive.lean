module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Transitive

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rsi, Reg64.rax, Reg64.rdx, Reg64.r8, Reg64.rcx, Reg64.r9, Reg64.rbx, Reg64.r13,
  Reg64.rbp, Reg64.r12, Reg64.r14, Reg64.r15, Reg64.rdi]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.gpr Reg64.rsi), (.gpr Reg64.rax), (.flag CondCode.nz), (.gpr Reg64.rcx), (.gpr Reg64.rdx),
  (.gpr Reg64.r12), (.gpr Reg64.r15), (.flag CondCode.z), (.gpr Reg64.r9), (.flag CondCode.c),
  (.gpr Reg64.rbx), (.gpr Reg64.r8), (.flag CondCode.nc), (.gpr Reg64.rbp), (.gpr Reg64.r14),
  (.gpr Reg64.r13), (.flag CondCode.l), (.slot 9 .w64), (.gpr Reg64.rdi), (.slot 0 .w64),
  (.slot 8 .w64), (.slot 6 .w64), (.slot 10 .w64), (.slot 7 .w64), (.slot 5 .w64),
  (.slot 3 .w64), (.slot 2 .w64), (.slot 1 .w64), (.slot 4 .w64)]

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

@[expose] def hint_full_trans_lit_m6 : x64Isa.Hints := _decH #[
  "b040012213141511013101360607080628492A022B170B0B0C0C220A0D2B59022B0E0B0B31013F0F0F0A09",
  "43071707070109010B120808070A030703092G071B090B0B1B490103120B0B070A09010901091321011101",
  "110901010C0E0331013B080708093A0D120901010A071919010C6B3B3B3B010B0C196B010931012331090B",
  "090B0922094B071203097308012801012919030CA1030C193109060606410C01S0011001027QHG4X264I5J",
  "EK9J2FA7G200DQHG4X264I5J6LX1MI5809JX5MLNEK2O1DG203FXBOQHG4X264I5J6LX1MI5809JX5MLNEKXC1",
  "0FX0003IXLP4IXBOXSD80I5QHX266LX1M9JX5M5JLNG4XCQEKXKP4FA1BIaW0400KXLP4IXBOY3BXSD80I5QHX",
  "266LX1M9JX5M5JLNG4Y0FXCQEKY1A0KeW0004MYAEEKI54IYNFYHR6LXCQ5JYBSG4XSD80LNXKPXLPXBOQHX26",
  "X1M9JX5M2A1Me0203PYAEXLP4IXBOXSD80I5QHX266LX1M9JX5M5JLNG4XCQEKXKPYNFYHRYBSYU3YQAYR10Pa",
  "WeW0004OZDAZ61YAEEKI54IYNFYHR6LXCQ5JYBSG4XSD80LNXKPXLPXBOQHX26X1M9JX5M0OXW0008IQHG4X26",
  "4I5J6LX1MI5809JX5MLNEKY0FXCQXBOXLPY3B0IG000JXLP4IXBOY3BXSD80I5QHX266LX1M9JX5M5JLNG4Y0F",
  "XCQEK11JeW0102GQHG4X264I5J6LX1MI5809JX5MLNEKY0FXC1XCQ13GG101GQHG4X264I5J6LX1MI5809JX5M",
  "LNEKY0FXCQXBO0GG002LQHX266L4IX1MI5809JX5M5JLNG4Y0FXCQXBOaUEXLPb9RaV3bB8EK1DLm0100MQHX2",
  "66L4IX1MI5809JX5M5B5JLNG4Y0FXCQXBOaUEXLPb9RaV3bB8EK11MXm0101MQHX266L4IX1MI5809JX5M5B5J",
  "LNG4Y0FXCQXBOaUEXLPb9RaV3bB8EK11MXm0103LQHG4X264I5J6LX1MI5809JX5MLNEKY0FXCQXBOaUEXLPb9",
  "RaV3bB80LG000LQHX266L4IX1MI5809JX5M5JLNG4Y0FXCQXBOaUEXLPb9RaV3bB8EK11Lm0100LQHX266L4IX",
  "1MI5809JX5M5JLNG4Y0FXCQXBOaUEXLPb9RaV3bB8EK11Lm0100LQHX266L4IX1MI5809JX5M5JLNG4Y0FXCQX",
  "BOaUEXLPb9RaV3bB8EK11Lm010A34I5JdHF03200194I5JdHFdIAEK9JX26QHG418921009G4X264I5JdHFdIA",
  "EK9JQH218982019G4X264I5JdHFdIAEK9JQH2189820484I5JdHFdIAEK9JX26QH08200094I5JdHFdIAEK9JX",
  "26QHG4119210094I5JdHFdIAEK9JX26QHG4119210094I5JdHFdIAEK9JX26QHG4119210R123000221032301",
  "323628437123074391384C63A5160356D43333218224A022502227AH234332218422486231182230B2231X",
  "E2241XK22134223332315YG22311224362212A2354J2219YM42182403ZT5l///////////VXE5l/////////",
  "//VY752ZmWtWWuWYrgsWWWcX+uYcWWWWWWuZXuX+WWkkklmWWWXcWZpmWWncWWWWXWWjoWecWWeWWaiWkkZWeZ",
  "WiWhWZxWkkgqP0aaWWeXYWWWWWnWWWWYWWXXWmWmWWWXWWemWWWWWaeWWWWWWWYeWWWWWWWWWWWYYmmWWWoWWW",
  "WWWfWWWWWWeWWWWWWW00YWWaWnWWWWaemWWWXamammeWeWWWWmWaeWWWWXYaeYWamWXWaWWXWaYWWaWWXXefWW",
  "affWeWWWamWWnemaaWYWWWX00cWeWmWWYYWWYWseWYWWWWWWWWauWsWacccbmmWWmYWXnWmWeoWWWWamWWnWWW",
  "WXaWWWaXcbXWWXWWWXWWaWcaWW00d//x//p+y////pk////ys/s+ld/d///+l/td////yxtch/s//z/t//z/pw",
  "p/t//zyliq/pjj/l///s//+yk/tt/x///zVaWWiXZWWWWinWWWWZfWfXmuWuWWWXmWeuWWWWZaevqWfWWYWeWW",
  "YWibiWeWWYZmphWiooWmWWWfWWXZnWeeWaWWWY000B66897AB"]
@[expose] def ext_full_trans_lit_m6 : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 232)]

@[expose] def hint_full_trans_sort_m6 : x64Isa.Hints := _decH #[
  "X8291A1E102D0301010C1B0B0912110F093505280805281C1I23032404032419070C1C3609010B0B02B000",
  "000015AEC0FD8A5J1B501006I15J8AAEC0FD1B601025AEC0FD8A5J1B501016AEC0FD8A5JQB0600007AEC0F",
  "DSFQB8A5J16701019U6AEC0FDSFQB8A5JX15189e01019AEC0FDSFQB8A5JU6X15119e0100AAEC0FD8A5JQBU",
  "6X15XB8SF11Aa0101DXD1AEC0FD8A5JQBU6X15XEISFXH3XB814DYe0102DXEIAEC0FD8A5JQBU6X15XB8SFXH",
  "3XD10DYe000212300922100XmaWXmuuXmuuWWWWwK0XWmXWYWWWWWWWWWXWWW00meWmfeWWWeWWWmemeW10mWW",
  "WuiWWuieaWWWW00+/d+/jl///l//+/kll/TXWuXWomWWWmWWXWnmmW200166897AB"]
@[expose] def ext_full_trans_sort_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_transitive_m6 : x64Isa.Hints := _decH #[
  "XD4215112707072D1E16024I0I07372I0013091C32221712200F4237002707171217002707121712204509",
  "210129A001D0010024A5F0200047CP4AKDIQMEO65F10701008O6MEKD4AA55FCPIQ203802019O6MEKD4AA55",
  "FCPIQR310901039CP4AKDIQMEO6XC0XCR5F0900012CP4A1D201007CP4AKDIQMEO6XCR15701048CP4AKDIQM",
  "EO6XCRXI50800009CP4AKDIQMEO6XCRXI5XR009e00070407006CJ233172321R2310X92300Y32213222130i",
  "mZuWcaemWaoWWkdpYaejWWXnucXgWcq30YWWWWnYWaWWWnWmWenWWYaWaYWWWWWW80mXWWWWenbWfaqWmeWaem",
  "mXYWYXWaWbeW40iWWWWWWWWWWYWnWWWWWWWmeYWWWWW00/+/y////kzn/jsd+/l/tk+/zv/xy/t/rl/NXWZWWW",
  "WnYkWofuXWmWenXWYcWaZWeWgmW800466897AB"]
@[expose] def ext_full_transitive_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 168),
   (("full_prioritize_binaries_m6", [i64], [.bool]), 56),
   (("full_trans_sort_m6", [i64, i64], []), 56),
   (("full_trans_lit_m6", [i64, i32, .bool], [.bool]), 376),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_wstack_defrag_m6", [i64], []), 136)]

@[expose] def hints : List x64Isa.Hints := [hint_full_trans_lit_m6, hint_full_trans_sort_m6,
    hint_full_transitive_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 232),
   (("full_backtrack", [i64, i64], []), 168),
   (("full_prioritize_binaries_m6", [i64], [.bool]), 56),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 696),
   (("full_wstack_defrag_m6", [i64], []), 136)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Transitive
