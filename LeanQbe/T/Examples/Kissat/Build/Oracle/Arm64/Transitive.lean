module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Transitive

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X23)),
  (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X26)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X0)), (XRegOrSp.reg (XReg.X27))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.flag LeanQbe.T.Arm64.ArmCond.ne),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X9))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.flag LeanQbe.T.Arm64.ArmCond.hi), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.flag LeanQbe.T.Arm64.ArmCond.cs), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X12))), (.gpr (XRegOrSp.reg (XReg.X11))),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X3))), (.gpr (XRegOrSp.reg (XReg.X15))),
  (.flag LeanQbe.T.Arm64.ArmCond.lt), (.gpr (XRegOrSp.reg (XReg.X14))),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X21))),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.slot 0 .w64), (.gpr (XRegOrSp.reg (XReg.X27)))]

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

@[expose] def hint_full_trans_lit_m6 : armIsa.Hints := _decH #[
  "bM400112031415161707020202080839090A0B097C2D032E1A0E0E0F0G12030D0H22420I032J0K0J0J0202",
  "020L0L3M0M0M0D0C4N0A1A0A0A0O0C0O0P1302020A0D0N0A0N0C1P0Q0A020P0I022222020C0O0N130P0P0A",
  "0D0C0O0C0O0I1N2O2O2O0I02020G0K0N0202020O0O3P0P0A0H0C3D0M130C0O0O0D0A1C1C020G6D3D3D3D0O",
  "0D0G1C6D0O0C3P0P02020O02021R0C0R0C0R0C230C420A130O0C720N0R2N0R0R2C1C020G12027O020G1C3O",
  "0C0909091202120F021202S001S001026Q8G5X294S51E42LT6G200CQ8G5X294S516UX1BI68091L7E42TRCY",
  "G203EXBTQ8G5X294S516UX1BI68091L7E4XCR0Eb0003HXLE4SXBTXSH80I6Q8X296UX1B9151L7G5XCRE4XKE",
  "4LDKMHYYm0400JXLE4SXBTY3MXSH80I6Q8X296UX1B9151L7G5Y0LXCRE4Y1D0JbW0004LYAKE4I64SYNMYHL6",
  "UXCR51YBJG5XSH80L7XKEXLEXBTQ8X29X1B912DOLmmu0203OYAKXLE4SXBTXSH80I6Q8X296UX1B9151L7G5X",
  "CRE4XKEYNMYHLYBJYUNYQDYRO0OZabW0004NZDDZ6OYAKE4I64SYNMYHL6UXCR51YBJG5XSH80L7XKEXLEXBTQ",
  "8X29X1B910NYYZW0008HQ8G5X294S516UX1BI68091L7E4Y0LXCRXBTXLEY3M0HYG000IXLE4SXBTY3MXSH80I",
  "6Q8X296UX1B9151L7G5Y0LXCRE41OIbW0102EQ8G5X294S516UX1BI68091L7E4Y0LXCR1OEYG101FQ8G5X294",
  "S516UX1BI68091L7E4Y0LXCRXBT0FYG002KQ8X296U4SX1BI6809151L7G5Y0LXCRXBTaUKXLEb9PaVNbBHE41",
  "MKeG100KQ8X296U4SX1BI6809151L7G5Y0LXCRXBTaUKXLEb9PaVNbBHE41OKeG101KQ8X296U4SX1BI680915",
  "1L7G5Y0LXCRXBTaUKXLEb9PaVNbBHE41OKeG103KQ8G5X294S516UX1BI68091L7E4Y0LXCRXBTaUKXLEb9PaV",
  "NbBH0KYG000KQ8X296U4SX1BI6809151L7G5Y0LXCRXBTaUKXLEb9PaVNbBHE41OKeG100KQ8X296U4SX1BI68",
  "09151L7G5Y0LXCRXBTaUKXLEb9PaVNbBHE41OKeG100KQ8X296U4SX1BI6809151L7G5Y0LXCRXBTaUKXLEb9P",
  "aVNbBHE41OKeG10A34S51dHL03200184S51dHLdITE4X29Q8G51N821008G5X294S51dHLdITE4Q82RN882018",
  "G5X294S51dHLdITE4Q82RN8820474S51dHLdITE4X29Q807200084S51dHLdITE4X29Q8G51O8210084S51dHL",
  "dITE4X29Q8G51O8210084S51dHLdITE4X29Q8G51O82101020010mWnWWuWYrgmWWWcX+uYcWWWWWWWWXuX+WW",
  "kkklmWWWXcWZmWWWvsWWWWXWWXpWWYWWeWWaiWkWZWWZWaWhWZ/WkWgq90aaWWeXYWWWWWnWWWWYWWXXWmWmWW",
  "WXWWemWWWWWaeWWWWWWWYeWWWWWWWWWWWYYmmWWWoWWWWWWfWWWWWWeWWWWWWW00YWWaWnWWWWaemWWWXamamm",
  "eWeWWWWmWaeWWWWXYaeYWamWXWaWWXWaYWWaWWXXefWWaffWeWWWamWWnemaaWYWWWX00cWeWmWWYYWWYWseWY",
  "WWWWWWWWauWsWacccbmmWWmYWXnWmWeoWWWWamWWnWWWWXaWWWaXcbXWWXWWWXWWaWcaWW00d//x//p+y////p",
  "k////ys/s+ld/d///+l/td////yxtch/s//z/t//z/pwp/t//zyliq/pjj/l///s//+yk/tt/x///zVaWWiXZW",
  "WWWinWWWWZfWfXmuWuWWWXmWeuWWWWZaevqWfWWYWeWWYWibiWeWWYZmphWiooWmWWWfWWXZnWeeWaWWWY0000",
  "823405678"]
@[expose] def ext_full_trans_lit_m6 : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 128)]

@[expose] def hint_full_trans_sort_m6 : armIsa.Hints := _decH #[
  "X52I101L1K1S0M020S0S0G1D0D0C131S060C353H0H3H1F1N223O0O3O1I0A0G1F390C0S0D0D03B000000015",
  "ALCKFM80511D501006IS5180ALCKFM1D601025ALCKFM80511D501016ALCKFM8051QD0600007ALCKFMS6QD8",
  "05119701019U9ALCKFMS6QD8051X151H9e01019ALCKFMS6QD8051U9X151S9e0100AALCKFM8051QDU9X15XB",
  "HS61SAa0101DXDSALCKFM8051QDU9X15XENS6XH2XBH1ODYe0102DXENALCKFM8051QDU9X15XBHS6XH2XDS0D",
  "Ye00000XmaWXuyuXuyuWWWWgK0XWmXWYWWWWWWWWWXWWW00meWmfeWWWeWWWmemeW10mWWWuiWWuieaWWWW00+",
  "/d+/jl///l//+/kll/TXWuXWomWWWmWWXWnmmW2aWWWWWWWWWWWWWWWYW0000"]
@[expose] def ext_full_trans_sort_m6 : List (SigEntry × Nat) := []

@[expose] def hint_full_transitive_m6 : armIsa.Hints := _decH #[
  "Y33S031T1S1S0A0A0A2E1714034N0N0A0N0N0N0A2N011O0C1G331O030O0A0O03210T2O130O0O0O0A0B2A0A",
  "0S0A0S030S0A0B2A0A0S030S0A0S030S0S3O0O0U0C2S0S110CA001E0010024J5U0200047CV4JKEIX0M7O45",
  "U18701008O4M7KE4JAT5UCVIX021O802019O4M7KE4JAT5UCVIX0RO11901038CV4JKEIX0M7O4XC85U080001",
  "2CV4J1E201007CV4JKEIX0M7O4XC81U701048CV4JKEIX0M7O4XC8XIU0800009CV4JKEIX0M7O4XC8XIUXR10",
  "9e00050400902AB230A820BAaG22A0222A00amWyWWWWWWWWWWWbpWWWjWWXmWcXgWYq10YWWWWnYWaWWWnWmW",
  "enWWYaWaYWWWWWW80mXWWWWenbWfaqWmeWaemmXYWYXWaWbeW40iWWWWWWWWWWYWnWWWWWWWmeYWWWWW00/+/y",
  "////kzn/jsd+/l/tk+/zv/xy/t/rl/NXWZWWWWnYkWofuXWmWenXWYcWaZWeWgmW8001923405678B"]
@[expose] def ext_full_transitive_m6 : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_prioritize_binaries_m6", [i64], [.bool]), 0),
   (("full_trans_sort_m6", [i64, i64], []), 0),
   (("full_trans_lit_m6", [i64, i32, .bool], [.bool]), 208),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_wstack_defrag_m6", [i64], []), 48)]

@[expose] def hints : List armIsa.Hints := [hint_full_trans_lit_m6, hint_full_trans_sort_m6,
    hint_full_transitive_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 128),
   (("full_backtrack", [i64, i64], []), 96),
   (("full_prioritize_binaries_m6", [i64], [.bool]), 0),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_wstack_defrag_m6", [i64], []), 48)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Transitive
