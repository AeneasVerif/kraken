module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Limits

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X19)), (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X0)),
  (XRegOrSp.reg (XReg.X20)), (XRegOrSp.reg (XReg.X21)), (XRegOrSp.reg (XReg.X22)),
  (XRegOrSp.reg (XReg.X23)), (XRegOrSp.reg (XReg.X24)), (XRegOrSp.reg (XReg.X4)),
  (XRegOrSp.reg (XReg.X3))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.flag LeanQbe.T.Arm64.ArmCond.cc), (.gpr (XRegOrSp.reg (XReg.X1))),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.gpr (XRegOrSp.reg (XReg.X0))),
  (.flag LeanQbe.T.Arm64.ArmCond.eq), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.flag LeanQbe.T.Arm64.ArmCond.ls),
  (.gpr (XRegOrSp.reg (XReg.X5))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X6))), (.gpr (XRegOrSp.reg (XReg.X7))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.gpr (XRegOrSp.reg (XReg.X20))),
  (.gpr (XRegOrSp.reg (XReg.X21))), (.gpr (XRegOrSp.reg (XReg.X23))),
  (.gpr (XRegOrSp.reg (XReg.X22))), (.gpr (XRegOrSp.reg (XReg.X24))),
  (.gpr (XRegOrSp.reg (XReg.X8))), (.gpr (XRegOrSp.reg (XReg.X9)))]

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

@[expose] def hint_full_isqrt : armIsa.Hints := _decH #[
  "O1000110012030404050102060537030704080504010206054001500101145111010014511101020354100",
  "300000mWWWae00eWWmYa50XWW00XziXwuhtLYp+bdqeA0000"]
@[expose] def ext_full_isqrt : List (SigEntry × Nat) := []

@[expose] def hint_full_ilog10 : armIsa.Hints := _decH #[
  "9150404030320050109200150010117425110200000XXW80mn4000k+zNXXY81000"]
@[expose] def ext_full_ilog10 : List (SigEntry × Nat) := []

@[expose] def hint_full_tick_rel : armIsa.Hints := _decH #[
  "XD210611061402140204140217180604080604070808060807040703040A030804060804071A0B0C0D0102",
  "080401200000003245910200000YWWWWYnWaeH0XWW00aWnY40mWWWWW00X/+WlWoXolt+zxNX/m/j+jmeXYa8",
  "0000"]
@[expose] def ext_full_tick_rel : List (SigEntry × Nat) := []

@[expose] def hint_full_scale_delta_m5 : armIsa.Hints := _decH #[
  "YE261115040B05050305051005036301010403070801040307080104030708010403070801040301010400",
  "080708080E08080B0612070308010407240701010E040E01210004030505030404010505600150010115E1",
  "5101011R511101011R5247102004R5XN4XM1XQ704000301500101020010aWWWWWWWWWWWWK0XWWWWWWWWWWW",
  "W00XaWWWWeqWeWWWWWWYWW10jWWWmYWWXiXWWWWYWWYg00X/Wut//mlkd/immmmn/wvZT/deWWlmnuWpllllkW",
  "bcy200010"]
@[expose] def ext_full_scale_delta_m5 : List (SigEntry × Nat) :=
  [(("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_add", [i64, i64], [i64]), 0)]

@[expose] def hint_full_ema_update : armIsa.Hints := _decH #[
  "Y43502060305050403070805040307080504030708050403070805040305050400080708080108080B0612",
  "07030105040724070F050104010F2G1H1I1J037216050372160570000000114E1F1010214E2471020044EX",
  "54X45X8704000354EYAJY8IY2FY6H155010144EYAJY8IY2F04000124EYAJ1520101020020gqWWWWeWWWWWW",
  "WW10YWWWaWWWWWWWWYWWWWWWWW00XWWmYWXWWWWWWneWmWWWWWK0XWaWWYuYWWWWa00+z/+zx/z////W+yl+vX",
  "XXXWNXYWXYaWYWWWW/XZmXc++++/80006034567"]
@[expose] def ext_full_ema_update : List (SigEntry × Nat) :=
  [(("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_add", [i64, i64], [i64]), 0)]

@[expose] def hint_full_scale_delta : armIsa.Hints := _decH #[
  "YE261115040B05050305051005036301010403070801040307080104030708010403070801040301010400",
  "080708080E08080B0612070308010407240701010E040E01210004030505030404010505600150010115E1",
  "5101011R511101011R5247102004R5XN4XM1XQ704000301500101020010aWWWWWWWWWWWWK0XWWWWWWWWWWW",
  "W00XaWWWWeqWeWWWWWWYWW10jWWWmYWWXiXWWWWYWWYg00X/Wut//mlkd/immmmn/wvZT/deWWlmnuWpllllkW",
  "bcy200010"]
@[expose] def ext_full_scale_delta : List (SigEntry × Nat) :=
  [(("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_add", [i64, i64], [i64]), 0)]

@[expose] def hint_full_fill_u64_m7 : armIsa.Hints := _decH #[
  "C33D8031B0703C708031B370B60000000035164451A3010035164452A73020235164451730100351644517",
  "30100351644517301000iWXxtiWWdkzG0aWnWWWWXYWWW00YWemWWWenWWW10aWevpaaWZciG0Xv/kl///cy//",
  "/TcWnmWWWvZWWW20000"]
@[expose] def ext_full_fill_u64_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_u32 : armIsa.Hints := _decH #[
  "X221000603070404030318080B12140K0B3D0B0417032B0C27034L0B0408080201140B8000000022614518",
  "201013C46145183010326145182010136145L8030000445NKL8611L40101645NKL861PLSD146X0100645NK",
  "L861PLSD24A6X02000aWWiXZWWmuWWWWW00XWeaWaWWWWWWXWYY00maYWWeaYYWmemfXA0aWWWWWWaWWWW00Z+",
  "/tv//ltxx+/klbz3XWecWWmeaaXWnmwYSXWWWWWWWWWWWWe0000"]
@[expose] def ext_full_sort_u32 : List (SigEntry × Nat) := []

@[expose] def hint_full_max_u64 : armIsa.Hints := _decH #["22B0500000000000520000"]
@[expose] def ext_full_max_u64 : List (SigEntry × Nat) := []

@[expose] def hint_full_elim_dticks : armIsa.Hints := _decH #[
  "F34170B04040305111401150505030510015001000YgW500000eWX00j//iVYWWp00000"]
@[expose] def ext_full_elim_dticks : List (SigEntry × Nat) := []

@[expose] def hint_full_lcg_next_m7 : armIsa.Hints := _decH #[
  "4250505050102012010000000ZV00000"]
@[expose] def ext_full_lcg_next_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_m7_get64 : armIsa.Hints := _decH #[
  "8231524043505050510015001000XvK00010iuG0d//T20000"]
@[expose] def ext_full_m7_get64 : List (SigEntry × Nat) := []

@[expose] def hint_full_m7_set64 : armIsa.Hints := _decH #[
  "533152734041000000000XvK00010YuG0Z//T20000"]
@[expose] def ext_full_m7_set64 : List (SigEntry × Nat) := []

@[expose] def hint_full_m7_state_init : armIsa.Hints := _decH #[
  "YE211404170707040611020104071814040611041711011104171101110417110111041711010121212131",
  "04171101110417110111041711011104171101012121212131010417110101210514110120000000114501",
  "00000anefYqggggYfYfYfYfbbbbXanananamfWmX5000aWWXW00eWWmWWWWWWaWaWaWaWWWWWYWYWYWYWWmWWi",
  "00l//////////////////////////////t/xy/VeWaZW00000"]
@[expose] def ext_full_m7_state_init : List (SigEntry × Nat) := []

@[expose] def hint_full_ema_swap_m7 : armIsa.Hints := _decH #[
  "YT32070208160114031A2C34040A14031A2C34040A14031A2C34040A14031A2C34041411011A0A0A010707",
  "060108120354030454030454030451010328083A0A0A08180328083A0A0A08180328083A0A0A0818032808",
  "3101010815141101B0445A887D1040001445A887D1040001445A887D1040001345A8870300011451110101",
  "445YG7YJ8YI1040001445YG7YJ8YI1040001445YG7YJ8YI10400024YG745Y64YI118401014YG745Y64YI11",
  "8401014YG745Y64YI118401036630232831904282220022910YeWkiWZpWWyuWdcWkuXxWdiWzmXWXbWywaXv",
  "qeZpemdcnWG000XWWWeWWYWWWmWXWWaWWmWaYWWWWWWmWWXWWWYWWWaW00aWZcaWvnWcieXpYWceWvWZaWimWX",
  "iWXieWYumWbnWWhYWW00X////y///l//x//+//y//t/+//txt////+///z///x///tlLZWWWmWWaWWXWWZWWeW",
  "XWWeaeWWWWXWWWYWWWaWWWemA0030"]
@[expose] def ext_full_ema_swap_m7 : List (SigEntry × Nat) :=
  [(("full_m7_state_init", [i64], []), 0)]

@[expose] def hints : List armIsa.Hints := [hint_full_isqrt, hint_full_ilog10,
    hint_full_tick_rel, hint_full_scale_delta_m5, hint_full_ema_update, hint_full_scale_delta,
    hint_full_fill_u64_m7, hint_full_sort_u32, hint_full_max_u64, hint_full_elim_dticks,
    hint_full_lcg_next_m7, hint_full_m7_get64, hint_full_m7_set64, hint_full_m7_state_init,
    hint_full_ema_swap_m7]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_add", [i64, i64], [i64]), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Limits
