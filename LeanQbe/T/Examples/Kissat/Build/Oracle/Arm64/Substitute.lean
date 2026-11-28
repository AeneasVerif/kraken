module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Substitute

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X6)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X5)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X10)), (XRegOrSp.reg (XReg.X9)),
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)),
  (XRegOrSp.reg (XReg.X22)), (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24)),
  (XRegOrSp.reg (XReg.X25)), (XRegOrSp.reg (XReg.X26)), (XRegOrSp.reg (XReg.X27)),
  (XRegOrSp.reg (XReg.X28)), (XRegOrSp.reg (XReg.X29)), (XRegOrSp.reg (XReg.X0))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.gpr (XRegOrSp.reg (XReg.X13))), (.gpr (XRegOrSp.reg (XReg.X10))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X1))), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X4))),
  (.gpr (XRegOrSp.reg (XReg.X0))), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X14))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X26))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.gpr (XRegOrSp.reg (XReg.X29))), (.gpr (XRegOrSp.reg (XReg.X27))),
  (.gpr (XRegOrSp.reg (XReg.X20))), (.gpr (XRegOrSp.reg (XReg.X19))),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.gpr (XRegOrSp.reg (XReg.X25))),
  (.gpr (XRegOrSp.reg (XReg.X15))), (.slot 2 .w64), (.slot 0 .w64), (.slot 1 .w64),
  (.gpr (XRegOrSp.reg (XReg.X24))), (.gpr (XRegOrSp.reg (XReg.X28))),
  (.flag LeanQbe.T.Arm64.ArmCond.lt)]

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

@[expose] def hint_full_tarjan_pop_scc : armIsa.Hints := _decH #[
  "X2501112131415260728090A0B272C094A4A380B061A0D0A080E2A0A1F090C0A0E3C0C5094GH47HF3B1D29",
  "0J55C2IJ9e4220A4GH47HF3B1D290J55C6J2IAAu42222UI4G1720100BUI4GVJH4X3C7HF3B1D290J527FBXK",
  "202CUI4GVJH4X3C7HF3B1D290J5X6F17CXK101020010XXoWWXmWmZozmiWiXgL0mWaaYWWWWWWWmW00meWYYX",
  "eWWXWaWeW00mWWWmWWWmamWWaWW00//+/d/xxzl//z/n/l/VXWuWaaYmWWYWkWmW00000"]
@[expose] def ext_full_tarjan_pop_scc : List (SigEntry × Nat) := []

@[expose] def hint_full_tarjan_scc : armIsa.Hints := _decH #[
  "b727071A1H1F1C1K1L1M181J060N0E0C080D0J0D0C0D010N010C0N0C0C0N0C0N180C3C383J080N1979080B",
  "280B0J0828160J0O0P1C2C0C0P380B0J0Q200811080505050505380E3811060R03020I0S0T042605280901",
  "0B25094848300B06180D08000E28081C090C080E2C0C163C310E160105281B01080809013116210B18310E",
  "0U1121013C2601061J060G0N380B083J280B0J3J280B0J3J280B0J3C080N190G380B083C090G4JM001G001",
  "00BDFBH9A4G77FVJLHKPX0NX1LM1JB0100BDFBH9A4G77FVJLHKPX0NX1LM1JB010CB4GFVDFBHJLHKPX077NX",
  "1LM9A2UJB020059ADFBH4G77050002C4GFVDFBHJLHKPX077NX1LM9AY7J1UC0112E4GFVDFBHJLHKPX077Y7J",
  "NX1YNOLM9AYVP3UX2CEfW0312GZ0UZ6Q4GFVDFBHJLHKPX077Y7JNX1YNOLM9AYVP1X2GXaW1101OZ0UZ6Q4GF",
  "VDFBHJLHKPX077Y7JNX1YNOLMZ1X2a4TYVPZVRa3Sa12a2Ia03a549A2X31OcaW1220PZ0UZ6Q4GFVDFBHJLHK",
  "PX077Y7JNX1YNOLMZ1X2a4TYVPZVRa3Sa12a2Ia03a549AZ902C1PmcaW1222IZ0UZ6Q4GFVDFBHJLHKPX077Y",
  "7JNX1YNOLM9AYVPZ1X2aGX315IXaW1100QZ0UZ6Q4GFVDFBHJLHKPX077Y7JNX1YNOLM9AYVPZ1X2aGX3aH1a4",
  "TZVRa3Sa12a2Ia03a5425CQXfaW1202RZ0UZ6Q4GFVDFBHJLHKPX077Y7JNX1YNOLM9AYVPZ1X2aGX3aH1a4TZ",
  "VRa3Sa12a2Ia03a54aLC15RXfaW110BFZ1X24GFVDFBHJLHKPX077Y7JNX1YNOLM9AYVP2UCFoW021659A4G77",
  "DFBH1C5010059A4G77DFBH1C5010059A4G77DFBH1C5010269A4G77dNCDFBH06000169A4G77dNCDFBH06000",
  "169A4G77dNCDFBH06000169A4G77dNCDFBH06000369A4G77f1CDFBH060006M6300312323Z12230F2222aL2",
  "221E2240R22520XhWbmZWWbmZbmZbmZbmZWWWWYuimXwcbuWbmWZtWWXmWWZWXWdbxWWcWWXkdWauWXoWYuZWZ",
  "rWXgberWWWWWWWWWrgr90YWWmYaWWmWWmWWmWWmWWaYWWWWeWWmXWWWmmWeWWWXWWeeaWWWWWWeWWWWWWWWWWW",
  "WWWemWmWWWWWWYYYYaefaWWW00XWWeXYWWeWWeWWeWWeYaYXWWWWaWmeWmeWeeWaWWXWmWaaYmWWYYWaWaWmWW",
  "WeWWWaWeaeWemWWWWWfXXXYaaoWWW00XWXWWXWWXWWXWWXWWWWWWaWWuWWyWWyWXpWWWmWWXWWWXWfWWYWWWYZ",
  "YmWWWmWWiWWWWWeWWWWWWWWWWWWWWWW00//y//lzv//l//l//l//lvtxz////t+/l+/l/ll/t//z+l/ttw///x",
  "u/t/t+////l///t/ltl/kl/////k++avpoh///VZWWmYcWWmWWmWWmWWmceaYWWWWeXWmXWmWmmWeWWYXmWeeb",
  "WWWadWeWeXWWWWmWWWeWmemWnmWWWWWnXXxcijqWWW0003B6789ABCDEFG"]
@[expose] def ext_full_tarjan_scc : List (SigEntry × Nat) := []

@[expose] def hint_full_subst_elim_vars : armIsa.Hints := _decH #[
  "YA3M063C1Q091B1G061M1L1S663G160G0G3A060C0F0H0D0G3708080F010J0F0908380B180X41J090H090H2",
  "7073J0J0A0C0C0A0F0H0A090C3C0B1C0X4180C0F090F090F2G0G38080C0G0G0Q099001G0010014R0100003",
  "4R5S7M1Q3010544RMMOLQS1Q4010154RMMOLQSX2Q05000374RMMOLQSX2QX9GXDA07Z0000B4RMMOLQSX2QX9",
  "GXDAXFCXQFXN7XHH18Bx010654RMMOLQSX2Q05000074RMMOLQSX2QYQAX9G1H7Z01010409306H0kZWWXXuWW",
  "WdXmWYZmWXuWZmhX/gnWWc10YWWWWWWWWeXWWWWWWWWmYWWWWmXWWWWWWnW00XWWWWWamaaWmWWWWYeeeXWWWm",
  "eWmYWWaeeW40cXYWWWyWWWZWnWWXuWWuWXqXWWWWWWY00Zy/////o/tt+/////vlllz//+dl+/x//tld/NZWWW",
  "WWjWeeXWWWWWcmmmYWWXumXWaWWemuW800056789A"]
@[expose] def ext_full_subst_elim_vars : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 128),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_set_inactive", [i64, i32, i32], []), 0)]

@[expose] def hint_full_subst_rewrite_bins : armIsa.Hints := _decH #[
  "a42G061K0K1X31O1Q1R1P1M261G0G0G00003F0F0B210F05096A0G1B0H0H092J1B0B0H1J0J1B0E0A060A0J0",
  "J2C0H0E0A060A0A060J091A0A1B090A0A3S39097G0C08293E0G0N3H160H5H160H5H160H5H160H2C0H0N193",
  "A160A2C09060N3H5H5H5H2A0H0N193G2A09090G0N1C0C7A0H0N193A090G0G0G0F0G063C1A0B1B0B0G061L0",
  "90T090T09T001G001018AKCX3EOGQIR4X2MMKP1T80102BV0IRGQX9FMM4X2EOQTKPAKCX33S78B0300DGQX9F",
  "CX3AKV0IR4X2QTX81XA5MMKPEO4S78CDu0402JXCSXD7XJGGQX9FCX3AKV0IR4X2QTX81XA5MMKPEOXFCXIAXM",
  "H1JJicW0111EXJGGQX9FCX3AKV0IR4X2QTX81XA5MMKPEO3S7CEXm0300JXD7XFCXJGGQX9FCX3AKV0IR4X2QT",
  "X81XA5XCSXSJMMKPEOXMH0JesW0006IXD7XFCXJGGQX9FCX3AKV0IR4X2QTX81XA5MMKPEOXCSXSJ0IacW0006",
  "FXCSXD7GQX9FCX3AKV0IR4X2QTX81XA5MMKPEO28CFZW0202EZN8X9FZLSIRMM4X2ZM7EOQTV0GQKPAKCX30E0",
  "000EIRGQZLSZN8X9FMM4X2ZM7EOQTV0KPAKCX31CE0100EIRGQZLSZN8X9FMM4X2ZM7EOQTV0KPAKCX31CE010",
  "0EIRGQZLSZN8X9FMM4X2ZM7EOQTV0KPAKCX31CE0102FIRGQZLSZN8X9FMM4X2ZM7EOQTV0KPAKCX3ZRC0F000",
  "1FIRGQZLSZN8X9FMM4X2ZM7EOQTV0KPAKCX3ZRC0F0001FIRGQZLSZN8X9FMM4X2ZM7EOQTV0KPAKCX3ZRC0F0",
  "001FIRGQZLSZN8X9FMM4X2ZM7EOQTV0KPAKCX3ZRC0F0003FIRGQZLSZN8X9FMM4X2ZM7EOQTV0KPAKCX3b4C0",
  "F0002EZN84X2ZLSZM7X9FEOQTV0GQMMKPAKCX3IR0E0000EZN8X9FZLSIRMM4X2ZM7EOQTV0GQKPAKCX31AE01",
  "00EZN8X9FZLSIRMM4X2ZM7EOQTV0GQKPAKCX31AE0100EZN8X9FZLSIRMM4X2ZM7EOQTV0GQKPAKCX31AE0105",
  "E4X2MMKPAKCX3EOQTZLSGQIRZM7X9FZN8V00E0000E4X2ZLSZM7X9FZN8EOQTV0GQMMKPAKCX3IR1AE0100E4X",
  "2ZLSZM7X9FZN8EOQTV0GQMMKPAKCX3IR1AE0100E4X2ZLSZM7X9FZN8EOQTV0GQMMKPAKCX3IR1AE01069AKCX",
  "3EOGQIR4X2MMKPQT090000A4X2MMKPAKCX3EOQTZLSGQIR1LA0101B4X2MMKPAKCX3EOQTZLSGQIRdJL0B0001",
  "020BH0XiWWWiWXgreWWXsWWxsztjmWWuhWWcYyuhpXkibmWWZzmWhWXaWWWWuWWamWuXcWidWXrgqH0YWmmmWW",
  "WWWWaWnWWWWWemWemWWWWWWemXWaeWeWXWWaWWmWaeWWaeWXaXYWnWWXYWYeYWWWWWWWWWW00XWeeWXbaWeWYW",
  "emWWWYaeWaeWWWWWXaeWmYaWaWWmWYWWeXYaWWYaWWoWnWemWWneXaXYWaXWWYWWW40nWaWeWWXXWWoWafoipa",
  "mWWeXWYYWeeXXWaaWmmWXimWWWWWWWWeeWWWWWeWYWaZYWWWW00Xy/dd/znt/l/v/kl///vtd/td/////ytd+/",
  "xp/t/+//x//lyxt//xt/+x+y/k//+zlztzx/tz//x///NZWuuWYkeWmWcWnmWWWceuWeuWWWWWZeuXWaiWeWXW",
  "WaWWmZaeWWaeWXaXZWnWWXYmYeYaWeYWWaWWW8000B6789ABCDEFG"]
@[expose] def ext_full_subst_rewrite_bins : List (SigEntry × Nat) :=
  [(("full_add_bin_m6", [i64, i32, i32], [i64]), 192),
   (("full_add_unit", [i64, i32], [.bool]), 128)]

@[expose] def hint_full_subst_rewrite_ar : armIsa.Hints := _decH #[
  "Z92G061K1M1R1L0L2A062G0G0J3F0C0H0C080E273C0C0C0E160X21928060C090A0C0X20X20X21X2160E182",
  "C0C092A064C0C092H060A09085C3C0H2H062H0B3Q1A09280A060N4H2H3H2H3H2H3H2C0H0N194H2C090E094",
  "B0J0F083J0G0G0F0G0B1B2C1B2C3A1B0B0G060A0E1A0EK001G001015BMGL9K4TDR2AS502005BMGL9K4TDR1",
  "X2501019BMGL9K4TOGMSDRTFPJ1X29i0113BVHLABMGL9KMSOGTFPJ4TDR1CBi0100BBMGL9K4TOGMSDRTFPJX",
  "GCLA0Bi0004A9KTFOGPJMSDR4TXUX2BMGL0AA000B9KTFOGPJMSDRBMGLY38XUX24T1ABA102C9KTFOGPJMSDR",
  "BMGLY38XUX24TYDA0CA003A9KTFOGPJMSDR4TXUX2BMGL2PQAA200B9KTFOGPJMSDR4TXUX2BMGLYQ82AQBA20",
  "1C9KTFOGPJMSDR4TXUX2BMGLYQ8YRA1QCA102DXUX2BMGL9K4TMSZMQZLPTFOGPJDRZN80DXe0000E9KZN8TFO",
  "GPJMSZMQZLPDRZOA4TXUX2BMGL1CEK100E9KZN8TFOGPJMSZMQZLPDRZOA4TXUX2BMGL1CEK100E9KZN8TFOGP",
  "JMSZMQZLPDRZOA4TXUX2BMGL1CEK1056XUX2BMGL9K4TDR060000CXUX2BMGL9K4TDRMSZMQZLPTFOGPJ0CYm0",
  "0049XUX2BMGL9K4TDRMSZMQZLP0900029XUX2BMGL9K4TDRMSZMQZLP090001020CH0ZsWXmYWWXuXkWWcyWXt",
  "cyxpkWWWdWuvxmWZWyZWwYWWWuWmkuXuWvgH0aXWWWWWmeaWWWWWaWeYWWnWWWWWWWXWeWaWWWWWWeWWeWWWWa",
  "YWWWWWWWWW00YWmWomWeWYWeWWWYWbXWWemWWWWWWamaWYYWWWeeaWeaWqWWYXXaWYWWYWW40XoWWmWWmW+WcW",
  "WYiWepokfvcWWWZWeevmWXWiXWeWWaWeWXceWvWWW00Zx+/+u//l/x/l///x/ny//kl//////o/p/xx///dZt/",
  "Zt+t/pxzzmkv//x//NaXWXdWWmWaWmWWWaWkZWWnmWWWWWWjWiWaaWWWuyeWyeXeWiaYYlncWWaWW800096789",
  "ABCDE"]
@[expose] def ext_full_subst_rewrite_ar : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 128),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 192)]

@[expose] def hint_full_substitute : armIsa.Hints := _decH #[
  "R2G061G0B1G063G0B0G0B0M1G061B0G0B1G061G061B0B0G061B0S0E5001G0010014R010003000000014R1S",
  "1010424RGS0200020206HR207H0ZYa10aWWWmeXaWnWWW80YfbaYWemmemem4000X//vjntx/k+/k/k/Ncokea",
  "WnXWnWnW800046789"]
@[expose] def ext_full_substitute : List (SigEntry × Nat) :=
  [(("full_backtrack", [i64, i64], []), 96),
   (("full_tarjan_scc", [i64], [i64]), 128),
   (("full_subst_elim_vars", [i64, i64], [.bool]), 608),
   (("full_subst_rewrite_bins", [i64], [.bool]), 288),
   (("full_subst_rewrite_ar", [i64], [.bool]), 272),
   (("full_arena_sweep_m6", [i64], [i64]), 384),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560)]

@[expose] def hints : List armIsa.Hints := [hint_full_tarjan_pop_scc, hint_full_tarjan_scc,
    hint_full_subst_elim_vars, hint_full_subst_rewrite_bins, hint_full_subst_rewrite_ar,
    hint_full_substitute]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("full_add_unit", [i64, i32], [.bool]), 128),
   (("full_propagate_ignore_hot", [i64, i64], [i64]), 560),
   (("full_set_inactive", [i64, i32, i32], []), 0),
   (("full_add_bin_m6", [i64, i32, i32], [i64]), 192),
   (("full_backtrack", [i64, i64], []), 96),
   (("full_arena_sweep_m6", [i64], [i64]), 384)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Substitute
