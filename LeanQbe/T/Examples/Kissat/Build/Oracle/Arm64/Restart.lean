module

public import LeanQbe.T.Main
public import LeanQbe.T.Arm64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Restart

open LeanQbe.T LeanQbe.T.Arm64

@[expose] def _regs : Array armIsa.Reg := #[
  (XRegOrSp.reg (XReg.X4)), (XRegOrSp.reg (XReg.X3)), (XRegOrSp.reg (XReg.X0)),
  (XRegOrSp.reg (XReg.X1)), (XRegOrSp.reg (XReg.X2)), (XRegOrSp.reg (XReg.X19)),
  (XRegOrSp.reg (XReg.X5)), (XRegOrSp.reg (XReg.X6)), (XRegOrSp.reg (XReg.X10)),
  (XRegOrSp.reg (XReg.X12))]
@[expose] def _vregs : Array armIsa.VReg := #[]
@[expose] def _conds : Array armIsa.Cond := #[]
@[expose] def _locs : Array (Loc armIsa.Reg armIsa.VReg armIsa.Cond) := #[
  (.gpr (XRegOrSp.reg (XReg.X1))), (.flag LeanQbe.T.Arm64.ArmCond.eq),
  (.gpr (XRegOrSp.reg (XReg.X2))), (.flag LeanQbe.T.Arm64.ArmCond.cc),
  (.flag LeanQbe.T.Arm64.ArmCond.ne), (.gpr (XRegOrSp.reg (XReg.X3))),
  (.gpr (XRegOrSp.reg (XReg.X4))), (.flag LeanQbe.T.Arm64.ArmCond.cs),
  (.flag LeanQbe.T.Arm64.ArmCond.ls), (.gpr (XRegOrSp.reg (XReg.X0))), (.slot 0 .w64),
  (.slot 3 .w64), (.slot 4 .w64), (.gpr (XRegOrSp.reg (XReg.X5))),
  (.gpr (XRegOrSp.reg (XReg.X7))), (.gpr (XRegOrSp.reg (XReg.X6))),
  (.gpr (XRegOrSp.reg (XReg.X19))), (.flag LeanQbe.T.Arm64.ArmCond.hi),
  (.gpr (XRegOrSp.reg (XReg.X11))), (.gpr (XRegOrSp.reg (XReg.X13))),
  (.gpr (XRegOrSp.reg (XReg.X9))), (.gpr (XRegOrSp.reg (XReg.X8))),
  (.gpr (XRegOrSp.reg (XReg.X10))), (.gpr (XRegOrSp.reg (XReg.X12))),
  (.gpr (XRegOrSp.reg (XReg.X15))), (.gpr (XRegOrSp.reg (XReg.X14))), (.slot 2 .w64),
  (.slot 1 .w64)]

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

@[expose] def hint_full_restart_due : armIsa.Hints := _decH #[
  "XA200110120310041012151601011701212101382003000000100305070202070505000200110002001004",
  "600190010314A1010100549LBNCJ2H005000244ALBNCJ2104010144ALBU0NC124010414A101010FN434033",
  "142302040322233430232404032242023022231304042231543243130201202312040322216222052042I2",
  "2200mWWWWWmWWWWWXgnYH0aWWWWWWaWWWWWeWeW00YWWWXaWWWgYYXaWae40jWWaWWWWWWWWWW00lx/lWutp/l",
  "hxwzt/tlNaWm/deiWmqabYeWem80050"]
@[expose] def ext_full_restart_due : List (SigEntry × Nat) :=
  [(("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_log10_u64", [i64], [i64]), 0)]

@[expose] def hint_full_restart : armIsa.Hints := _decH #[
  "XA290911360315041D10041E29100000072007130F2202020722071E29100000072007130F220202072207",
  "50000000014G191010114G101010364GR9OED6JDG5106210564GXM9XJED6JDG51060101020520cXmWiYwWu",
  "cWXmheqYXW10YWWWWWWWeWWWWWmeY00mmXXXWWYYWaaaWYWeaX00YamWaeeWeoWWnXWWWWW00Z++/zzz//xx/t",
  "tt/x/ltzVXXWYYYWWaaWeeeWaWmeY000015"]
@[expose] def ext_full_restart : List (SigEntry × Nat) :=
  [(("full_randec_var_lvl_fid", [i64, i64], [i64]), 48),
   (("full_next_dec_var", [i64], [i64]), 48),
   (("full_backtrack", [i64, i64], []), 96)]

@[expose] def hint_full_switch_mode_m7 : armIsa.Hints := _decH #[
  "g429011910031909091003020709090702020009091910091929200310290929100319100H00000029100H",
  "020409591I1J1500000400062124321102160407060H2F0D010F2K0K0H240K0H26070F0L0M12020D070H26",
  "042N041D0D36060E072E08544E0702060O1D0L0D08032604260D0F06086D0D082M0N0H2F0F0H2P03060D0M",
  "375D0D0F0608400H040710007200071H320H16000004002430140F0F020706052004000702003207060E0L",
  "100005070H22042M04150532020D072D08544K0H3909190909090409000004000000000909090909091900",
  "00020202020219040939011904030909090202070704092304090900080409200929120215050502150516",
  "06060503000H02000202021902151909010912021000000200050505070202220305070909070505020902",
  "130210030507090907050500090019151202090900121909U0000000014G2021020214G191010454GYE9YK",
  "5YIJYGI165010134GYGIYE90300015YK5YE94GYIJYGI10501016YK5YE94GYIJYGIZ00060005AZLK4GZ86YK",
  "5YIJZB6YE9YGIZ00ZGD0An50038YK5YE94GYIJYGIZ00ZRKZLK08a0004AYK5YE94GYIJYGIZ00ZRKZLKa2La1",
  "F12Aa0110CYK5YE94GYIJYGIZ00ZRKZLKa2La1FaGNa3M12Ca0118BYK5YE94GYIJYGIZ00bDNbDQZRKZLKbC2",
  "1ABm0110EYK5YE94GYIJYGIZ00bDQZRKZLKbC2bEObAEbHLbRB4RF6AEe0482Gc3AYK5YE94GYIJYGIZ00bDQZ",
  "RKZLKbC2bEObAEbHLc0RbRB36DMGm132544GYGIYE9YQ604000054GYE9YQ6YK5YGI125010054GYE9YQ6YK5Y",
  "GI125010054GYE9YQ6YK5YGI125010634GYGIYE91K3010144GYGIYE9eDK04000884GYGIYE9eDKf7EeKFeJF",
  "f66108Y0110A4GYGIYE9eDKf7EeKFeJFf66fLMf8L10AY011514G01000014G010002000000114G191010124",
  "Gi422902020414G101010224GkBA122010224GkRR102010E02052dS2320A23302431630602306S22733228",
  "134280292643163060230652200gE4032303J2314J22410YeYeWWWWWWWWWWoWfWWWXaaraWWWWWXWyeWeWWW",
  "WWWaeWWZmZkcXuXnmYWdWXmWhXmWeZWWgrgWWWWkWWzmXmiZXmXnmYWWdWcyiZmZZWaWuWZWiWuWWehXoWYrgq",
  "YoXegawYramWWWYYH0eWWWYWWWWWaXWYWeeWWWWWWWWXWWWmWWWmWWWWWWWWWWWWWXWWWWXWaeWWWWaeWWWWWW",
  "WaXWWWWWWWWWWXWWWWWWWWWWXXWeWWWWWXWWWWWWWWWWWWWWWmWWWWWWWW80oWWWoWWWWaWWWXWWWWWYWmfWaa",
  "WWWWWWWaWmWWeWWWeWmmWaabWYWXaXWmYWeWmYaWWWWoaWWXWWaWYWmeXWabWYWWWmXXWWeegWaWmmaWaWmnWm",
  "YaXWWWWWWWXWWWeWWWWXaWe40aWaWcmWWcmWYacWWmWnWiXmWWWWWWaWWiWmWWWYYWWWWWWXmXcYWwWmmWWZWW",
  "WWXWWWWXWYWWWeWWWcWWimWmaXWmWmmWWWZWYiaXqXXWWWWWXWaWeWWWWWWWWWWWWWeWWWeWWWWjWWeW00d///",
  "/mihtmihv///t//yj/////huzbyttz//////t+///d///l++//ttn/x/ztz+/x/l+lxp///+hp//y//sdx+/ly",
  "/tn/x//+/zz//llZ/t+Y/t/t+cj+/xtz///yl/dz///l///Wut/lNlpqelpqcWWWeWWZoWWWWWqdYwZeeYWWWW",
  "WWeXWWWuWWWmXXWWeekWaWYeYXWaWmXmaiWWWXqiWWZWWfuaXWmZWekWaWWXWYYWWmmyWeXzWeWeXvoXWaeYWW",
  "WZmWuYWWWmWWW/deWm8eWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW",
  "WWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWWW00415"]
@[expose] def ext_full_switch_mode_m7 : List (SigEntry × Nat) :=
  [(("f64u_nlogpown", [i64, i64], [i64]), 48),
   (("full_ema_swap_m7", [i64, i64, i64], []), 32),
   (("m6_hdr_init", [i64], []), 0),
   (("f64u_log10_u64", [i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 0)]

@[expose] def hints : List armIsa.Hints := [hint_full_restart_due, hint_full_restart,
    hint_full_switch_mode_m7]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_mul", [i64, i64], [i64]), 0),
   (("f64u_sub", [i64, i64], [i64]), 0),
   (("f64u_log10_u64", [i64], [i64]), 0),
   (("full_randec_var_lvl_fid", [i64, i64], [i64]), 48),
   (("full_next_dec_var", [i64], [i64]), 48),
   (("full_backtrack", [i64, i64], []), 96),
   (("f64u_nlogpown", [i64, i64], [i64]), 48),
   (("full_ema_swap_m7", [i64, i64, i64], []), 32),
   (("m6_hdr_init", [i64], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.Restart
