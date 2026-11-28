module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Limits

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rbx, Reg64.rsi, Reg64.rax, Reg64.rdi, Reg64.rbp, Reg64.r12, Reg64.r13, Reg64.r14,
  Reg64.r15, Reg64.rdx]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.flag CondCode.c), (.gpr Reg64.rcx), (.flag CondCode.nz), (.gpr Reg64.rax), (.gpr Reg64.rdx),
  (.gpr Reg64.rdi), (.flag CondCode.z), (.gpr Reg64.rsi), (.gpr Reg64.r8), (.flag CondCode.nc),
  (.gpr Reg64.r9), (.gpr Reg64.rbx), (.gpr Reg64.r12), (.gpr Reg64.r14), (.gpr Reg64.r13),
  (.gpr Reg64.r15), (.gpr Reg64.rbp)]

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

@[expose] def hint_full_isqrt : x64Isa.Hints := _decH #[
  "O1000110012030405030102060334070401080501030206034001300101145111010014511101020351300",
  "300000mWWWae00eWWmYa50XWW00Xzlzw/htLYmYbWqeA0000"]
@[expose] def ext_full_isqrt : List (SigEntry × Nat) := []

@[expose] def hint_full_ilog10 : x64Isa.Hints := _decH #[
  "9130404090920030109200130010117423110200000XXW80mn4000k+zNXXY80000"]
@[expose] def ext_full_ilog10 : List (SigEntry × Nat) := []

@[expose] def hint_full_tick_rel : x64Isa.Hints := _decH #[
  "X936130622110201221417060107060104070707080401040901080907010607010420080A030207010320",
  "0000003245930200000cWWWWYpWauJ0XWW00aWnY40mWWWWW00X/+WlWpzolt+zxNX/m/iYjmeXYa80000"]
@[expose] def ext_full_tick_rel : List (SigEntry × Nat) := []

@[expose] def hint_full_scale_delta_m5 : x64Isa.Hints := _decH #[
  "YE261311040403030903031003096401010407050801040705080104070508010407050801040901010400",
  "050705050B0505000612070508010407240707010B040B04210004090303040707010303600130010115B1",
  "7101011R317101011R3247102004R3XN4XM1XQ70400030130010302001I2012120122B5AX651aWWWWWWWWW",
  "WWWK0XWWWWWWWWWWWW00XaWWWWeqWeWWWWWWYWW10bWWWmYWWXiXWWWWWWWYg00X//ut///lkd/i//////wvxT",
  "deWWWmnuWpWWWWWWbca200010"]
@[expose] def ext_full_scale_delta_m5 : List (SigEntry × Nat) :=
  [(("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_add", [i64, i64], [i64]), 0)]

@[expose] def hint_full_ema_update : x64Isa.Hints := _decH #[
  "Y3420601030301040508030104050803010405080301040508030109030301000504050507050500061204",
  "070503010421040103070107012C1D1E1F097216030972160370000000114B1G1010214B2141020044BX51",
  "X43X8404000354BYAFY8EY2GY6D135010144BYAFY8EY2G04000124BYAF1320101020031V51gqWWWWeWWWWW",
  "WWW30YWWWaWWWWWWWWYWWWWWWWW00XWWmYWXWWWWWWneWmWWWWWK0XWaWWYuYWWWWW00+z/+zx/z////++yl+v",
  "////yNXYWXYaWYWWWWXXZmXcWWWWZ80006045678"]
@[expose] def ext_full_ema_update : List (SigEntry × Nat) :=
  [(("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_add", [i64, i64], [i64]), 0)]

@[expose] def hint_full_scale_delta : x64Isa.Hints := _decH #[
  "YE261311040403030903031003096401010407050801040705080104070508010407050801040901010400",
  "050705050B0505000612070508010407240707010B040B04210004090303040707010303600130010115B1",
  "7101011R317101011R3247102004R3XN4XM1XQ70400030130010302001I2012120122B5AX651aWWWWWWWWW",
  "WWWK0XWWWWWWWWWWWW00XaWWWWeqWeWWWWWWYWW10bWWWmYWWXiXWWWWWWWYg00X//ut///lkd/i//////wvxT",
  "deWWWmnuWpWWWWWWbca200010"]
@[expose] def ext_full_scale_delta : List (SigEntry × Nat) :=
  [(("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_add", [i64, i64], [i64]), 0)]

@[expose] def hint_full_fill_u64_m7 : x64Isa.Hints := _decH #[
  "C39D109100309C301091033006000000003576445183010035764452833020235764451330100357644513",
  "30100357644513301000iWXxtiWWdkzG0aWnWWWWXYWWW00YWemWWWenWWW10aWevpaaWZciG0Xv/kl///cy//",
  "/TcWnmWWWvZWWW20000"]
@[expose] def ext_full_fill_u64_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_sort_u32 : x64Isa.Hints := _decH #[
  "X22C000609010303090914040012130B003700031109200A21094G000304040203110080000000226C4514",
  "201013C36C45143010326C45142010136C45L4030000445NBL46C1G40101645NBL46CPGS7136X0100645NB",
  "L46CPGS72386X0201020510aWWiXZWWmuWWWWW00XWeaWaWWWWWWXWYY00maYWWeaYYWmemfXA0aWWWWWWaWWW",
  "W00Z+/tv//ltxx+/klbz3XWecWWmeaaXWnmwYS0003045"]
@[expose] def ext_full_sort_u32 : List (SigEntry × Nat) := []

@[expose] def hint_full_max_u64 : x64Isa.Hints := _decH #["2200700000000000520000"]
@[expose] def ext_full_max_u64 : List (SigEntry × Nat) := []

@[expose] def hint_full_elim_dticks : x64Isa.Hints := _decH #[
  "F33110403030903131103110303090310013001000YgW500000eWX00j//lVYWWm00000"]
@[expose] def ext_full_elim_dticks : List (SigEntry × Nat) := []

@[expose] def hint_full_lcg_next_m7 : x64Isa.Hints := _decH #["42303030300010000000ZV00000"]
@[expose] def ext_full_lcg_next_m7 : List (SigEntry × Nat) := []

@[expose] def hint_full_m7_get64 : x64Isa.Hints := _decH #[
  "8291321013303030310013001000XvK00010iuG0d//T20000"]
@[expose] def ext_full_m7_get64 : List (SigEntry × Nat) := []

@[expose] def hint_full_m7_set64 : x64Isa.Hints := _decH #[
  "539132134041000000000XvK00010uG0Z//T20000"]
@[expose] def ext_full_m7_set64 : List (SigEntry × Nat) := []

@[expose] def hint_full_m7_state_init : x64Isa.Hints := _decH #[
  "YD231101140404010622030104171101061301141303130114130313011413031301141303032323233301",
  "14130313011413031301141303130114130303232323233303011413030323011413032000000011450100",
  "000anefYqggggYfYfYfYfbbbbXanananamfXmX5000aWWXW00i00l//////////////////////////////t/x",
  "y/VeWaZW00000"]
@[expose] def ext_full_m7_state_init : List (SigEntry × Nat) := []

@[expose] def hint_full_ema_swap_m7 : x64Isa.Hints := _decH #[
  "YT3207020416031109182A3101081109182A3101081109182A3101081109182A3101111303180808030707",
  "06030412095109015109015109015303092404380808041409240438080804140924043808080414092404",
  "3303030411141303B0445A487D3040001445A487D3040001445A487D3040001345A4870300011451310101",
  "445YG7YJ4YI3040001445YG7YJ4YI3040001445YG7YJ4YI30400024YG745Y61YI314401014YG745Y61YI31",
  "4401014YG745Y61YI314401036630332931104292230022110YeWkiWZpWWyuWdcWkuXxWdiWzmXWXbWywaXv",
  "qeZpemdcnWG000XWWWeWWYWWWmWXWWaWWmWaYWWWWWWmWWXWWWYWWWaW00ZcaWvnWcieXpYWceWvWZaWimWXiW",
  "WieWWumWXnWWZYWW00X////y///l//x//+//y//t/+//txt////+///z///x///tlLZWWWmWWaWWXWWZWWeWXW",
  "WeaeWWWWXWWWYWWWaWWWemA0030"]
@[expose] def ext_full_ema_swap_m7 : List (SigEntry × Nat) :=
  [(("full_m7_state_init", [i64], []), 0)]

@[expose] def hints : List x64Isa.Hints := [hint_full_isqrt, hint_full_ilog10,
    hint_full_tick_rel, hint_full_scale_delta_m5, hint_full_ema_update, hint_full_scale_delta,
    hint_full_fill_u64_m7, hint_full_sort_u32, hint_full_max_u64, hint_full_elim_dticks,
    hint_full_lcg_next_m7, hint_full_m7_get64, hint_full_m7_set64, hint_full_m7_state_init,
    hint_full_ema_swap_m7]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_add", [i64, i64], [i64]), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Limits
