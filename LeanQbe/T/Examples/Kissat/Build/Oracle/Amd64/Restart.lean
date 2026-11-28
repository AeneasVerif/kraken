module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Restart

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rdx, Reg64.rax, Reg64.rdi, Reg64.rcx, Reg64.rsi, Reg64.rbp, Reg64.rbx, Reg64.r8,
  Reg64.r9, Reg64.r12, Reg64.r13, Reg64.r14, Reg64.r15]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.flag CondCode.z), (.gpr Reg64.rax), (.flag CondCode.c), (.flag CondCode.nz),
  (.gpr Reg64.rsi), (.gpr Reg64.rcx), (.gpr Reg64.rdx), (.flag CondCode.nc), (.slot 0 .w64),
  (.gpr Reg64.rdi), (.slot 3 .w64), (.slot 4 .w64), (.gpr Reg64.r8), (.gpr Reg64.r9),
  (.gpr Reg64.rbx), (.gpr Reg64.rbp), (.gpr Reg64.r15), (.gpr Reg64.r13), (.gpr Reg64.r12),
  (.gpr Reg64.r14), (.slot 1 .w64), (.slot 7 .w64), (.slot 5 .w64), (.slot 8 .w64),
  (.slot 6 .w64)]

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

@[expose] def hint_full_restart_due : x64Isa.Hints := _decH #[
  "X6303102231415111600001700202000372102010101150206070101060404050101100105012360011001",
  "031481710100549LANBJ5H4050002448LANBJ51140101448LAU1NB1440104148111010CN43403314230244",
  "3023230223202302223110404121154324311020310231172220O22201XP51XmWWWWWmWWWWWXgpZJ0aWWWW",
  "WWaWWWWWeWeW00YWWWXaWWWgYYXaWae40bWWaWWWWWWWWWW00lx/l/utpxlhxwzt/tlNaWmWdeiamqabYeWem8",
  "0050"]
@[expose] def ext_full_restart_due : List (SigEntry × Nat) :=
  [(("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_log10_u64", [i64], [i64]), 8)]

@[expose] def hint_full_restart : x64Isa.Hints := _decH #[
  "X350360215031C231D291101010737120E21010107371D291101010737120E210101073750000000014F11",
  "1010114F141010364FODR9D6JCG5146410564FXJDXM9D6JCG51460101020520kXmWyYwXucWZmhfqYXW70YW",
  "WWWWWWeWWWWWmeY00mmXXXWWYYWaaaWYWeaX00YWmWaWeWeYWWmXWWWWW00Z++/zzz//xx/ttt/x/ltzVXXWYY",
  "YWWaaWeeeWaWmeY0000265"]
@[expose] def ext_full_restart : List (SigEntry × Nat) :=
  [(("full_randec_var_lvl_fid", [i64, i64], [i64]), 72),
   (("full_next_dec_var", [i64], [i64]), 104),
   (("full_backtrack", [i64, i64], []), 168)]

@[expose] def hint_full_switch_mode_m7 : x64Isa.Hints := _decH #[
  "f4303102190909150206070101060404050101111501112132152101410211150605050521150206030154",
  "1115152319202350061F03070F0239000C2G0G02230G022C07090H0D1I0I1702332J031I0I0I2F0F17370C",
  "431C2H0706090C1C0J0C0702332F0C0I09076F0F072C0C022I0I022C02090F0C372F2C0D0I090719210203",
  "07A1060712310219233353050I06070C0933010706010126070F0H0C11011702332G031606062505173709",
  "43162J02A31101030101010181010505050505230540110302010101060607070301220301010507030125",
  "01211606140404061404190909040205040605060606110614110100011909150505090506060607090925",
  "0206070101060404050105120I15020607010106040405010511161I0I010105161101U0000000014E2461",
  "020214E111010454EYE4YK5YIAYGK195010134EYGKYE40300015YK5YE44EYIAYGK11501016YK5YE44EYIAY",
  "GKZ01060005BZLG4EZ8FYK5YIDYIAZBFYE4YGKZ01ZG90B50038YK5YE44EYIAYGKZ01ZRGZLG08a0004AYK5Y",
  "E44EYIAYGKZ01ZRGZLGa2Ha1916Aa0100CYK5YE44EYIAYGKZ01ZRGZLGa2Ha19a3DaGJ16Ca0108AYK5YE44E",
  "YIAYGKZ01bDLZRGZLGbC61CAe0100FYK5YE44EYIAYGKZ01bDLZRGZLGbC6bEDbEMbAHbHJbRN4OI9BFe0402H",
  "c3BYK5YE44EYIAYGKZ01bDLZRGZLGbC6bEDbEMbAHbHJc0ObRN3IFCHm030544EYGKYE4YQ904000054EYE4YQ",
  "9YK5YGK115010054EYE4YQ9YK5YGK115010054EYE4YQ9YK5YGK115010644EYGDYGKYE41J4010154EYGDYGK",
  "YE4eDJ05000894EYGDYGKYE4eDJf7HeKIeJ5f6F1190100B4EYGDYGKYE4eDJf7HeKIeJ8f6Ff8CfLG11B0105",
  "14E01000014E010002000000114E111010124Ei462152020414E151010224EkBF152010224EkRI152010P0",
  "2062Z5233332311H2201M227362283YS235752372722854238504367347A2307C232702280022821228052",
  "226342742276436834772207ZS2303O22301223002230bK20511qB5AYeYeWWWWWWWWWWoWfWWWXaaraWWWWW",
  "XYyuWurgmWmizuWWZWZikfmXpmoWcWZmWlXnceZWWgrguWWWiWWvmXmiZXmXpmYWWcWcuypWZdXaWuWZWiXuWW",
  "elXoawrgqYoXekawcramWWWYZJ0eWWWYWWWWWaXWYWeeWWWWWWWWXWWWmWWWmWWWWWWWWWWWWWXWWWWXWaeWWW",
  "WaeWWWWWWWaXWWWWWWWWWWXWWWWWWWWWWXXWeWWWWWXWWWWWWWWWWWWWWWmWWWWWWWW80oWWWoWWWWaWWWXWWW",
  "WWYWmfWaaWWWWWWWaWmWWeWWWeWmmWaabWYWXaXWmYWeWmYaWWWWoaWWXWWaWYWmeXWabWYWWWmXXWWeegWaWm",
  "maWaWmnWmYaXWWWWWWWXWWWeWWWWXaWe40YmWWYmWYWcWWWWXWiXmWWWWWWaWWiWmWWWYWWWWWWWXmXcYWwWmm",
  "WWZWWWWXWWWWXWYWWWeWWWcWWimWmaXWmWmmWWWZWYiaXqXXWWWWWXWaWeWWWWWWWWWWWWWeWWWeWWWWbWWWW0",
  "0d/////yht/yhv///t///j/////huzbyttz//////t+///d///l++//ttn/x/ztz+/x/l+lxp///+hp//y//sd",
  "x+/ly/tn/x//+/zz//llZ/t+Y/t/t+cj+/xtz///yl//z///l////ut/lNZqeWZqcWWWeWWWoWWWWWqdYwZeeY",
  "WWWWWWeXWWWuWWWmXXWWeekWaWYeYXWaWmXmaiWWWXqiWWZWWfuaXWmZWekWaWWXWYYWWmmyWeXzWeWeXvoXWa",
  "eYWWWZmWWYWWWmWWWWdeWm80096659ABC"]
@[expose] def ext_full_switch_mode_m7 : List (SigEntry × Nat) :=
  [(("f64u_nlogpown", [i64, i64], [i64]), 72),
   (("full_ema_swap_m7", [i64, i64, i64], []), 32),
   (("m6_hdr_init", [i64], []), 0),
   (("f64u_log10_u64", [i64], [i64]), 8),
   (("f64u_mul", [i64, i64], [i64]), 24)]

@[expose] def hints : List x64Isa.Hints := [hint_full_restart_due, hint_full_restart,
    hint_full_switch_mode_m7]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_mul", [i64, i64], [i64]), 24),
   (("f64u_sub", [i64, i64], [i64]), 8),
   (("f64u_log10_u64", [i64], [i64]), 8),
   (("full_randec_var_lvl_fid", [i64, i64], [i64]), 72),
   (("full_next_dec_var", [i64], [i64]), 104),
   (("full_backtrack", [i64, i64], []), 168),
   (("f64u_nlogpown", [i64, i64], [i64]), 72),
   (("full_ema_swap_m7", [i64, i64, i64], []), 32),
   (("m6_hdr_init", [i64], []), 0)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Restart
