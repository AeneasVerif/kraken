module

public import LeanQbe.T.Main
public import LeanQbe.T.Amd64.Isa

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Reorder

open LeanQbe.T LeanQbe.T.Amd64

@[expose] def _regs : Array x64Isa.Reg := #[
  Reg64.rdx, Reg64.rax, Reg64.rbx, Reg64.rbp, Reg64.r12, Reg64.r13, Reg64.r14, Reg64.r15,
  Reg64.r8, Reg64.r9, Reg64.rsi, Reg64.rcx, Reg64.rdi]
@[expose] def _vregs : Array x64Isa.VReg := #[]
@[expose] def _conds : Array x64Isa.Cond := #[]
@[expose] def _locs : Array (Loc x64Isa.Reg x64Isa.VReg x64Isa.Cond) := #[
  (.flag CondCode.z), (.flag CondCode.nc), (.flag CondCode.c), (.gpr Reg64.r8),
  (.gpr Reg64.r13), (.gpr Reg64.r15), (.gpr Reg64.r14), (.gpr Reg64.rbx), (.gpr Reg64.rdi),
  (.gpr Reg64.rax), (.gpr Reg64.rbp), (.gpr Reg64.r12), (.gpr Reg64.rcx), (.gpr Reg64.r9),
  (.gpr Reg64.rdx), (.slot 0 .w64), (.gpr Reg64.rsi), (.flag CondCode.nz), (.flag CondCode.g),
  (.slot 2 .w64), (.slot 4 .w64), (.slot 13 .w64), (.slot 12 .w64), (.slot 15 .w64),
  (.slot 14 .w64), (.slot 11 .w64), (.slot 6 .w64), (.slot 10 .w64), (.slot 8 .w64),
  (.slot 3 .w64), (.slot 5 .w64), (.slot 9 .w64), (.slot 7 .w64), (.slot 1 .w64)]

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

@[expose] def hint_full_reorder_sift_fid : x64Isa.Hints := _decH #[
  "XH3001221314150607015808292A2B0B2C2D020E0E0E0E000E0E0E0A02070B0C0D09022A0A620D06000D0B",
  "02090A2026070140000000300000005F4H5D36E6F367G503017F4H5D36E6FQ8NG29A7X020BH2300O231002",
  "32002330143402010431020204320203043302041221102212022130iWWlvmWWWjpjpWbfG0aWWWWWWWWWW0",
  "0aWmWWWYWWWWWWWYWY50aWWYemWWWananWWW00Z/p+ua//xWXX////v/vHiXdxWWa/++WWWWcWcE0056234567"]
@[expose] def ext_full_reorder_sift_fid : List (SigEntry × Nat) := []

@[expose] def hint_full_reorder_queue_m7 : x64Isa.Hints := _decH #[
  "jM230D191C1E1G171A1B1B141615171A0H0102090C01090109010901A90C011212090208084G0G1009010H",
  "2909022I000E115C0C022I000C0E190211010E09090H4909020E10092E192E1C020G0E0C0G090268080902",
  "1H09123H09020C0C0C0C0C1C010H1C4H203C0C39090H020E01090E323E1009090202080G4H200008182028",
  "381C0209020C0209020H381E015C022H0H6H2E0C1902110C0H190112070E0G0E0A015D0D2E2929092G2902",
  "09090908000909090802090E0G0G0E022A0A620G0G00090G020E0A202G0A010H190E2G0012070C0E025D0D",
  "2E2929092G290209090908000909090802090E0G0G0E022A0A620G0G00090G020E0A202G0A01010H01020C",
  "0E010G010C010D010D0C010C0C010C01EC0E0112000H5E0E2H3G2G022G2C0G300D07022C0C4C0C210D0DDC",
  "1A0H6H2E0C1902110C0H190905015E0E23162D0D2G1402000208080808000808030802060D03044G022505",
  "520002030900030D020G05202905010H190E2G025E0E23162D0D2G1402000208080808000808030802060D",
  "03044G022505520002030900030D020G0520290501013H192606281G1E010304052C0C11023H190H1G0G0G",
  "2E0E11310D4H1E2H39XV001900100IX1AV7636F7D7JDKHL9MBNJOFP4QLRNBR6P4T519I0100IX1AV7636F7D",
  "7JDKHL9MBNJOFP4QLRNBR6P4T519I0109GBNJODKFP636F7D7JV7X1ALR4QNBR6P4T50G0000IBNJODKFP636F",
  "7D7JV7X1ALR4QNBR6P4T5HL9M1CI0102KBNJODKFP636F7D7JV7X1ALR4QNBR6P4T5HL9MXTCXTS0K0002NV7X",
  "1A7D7JY28Y2T4QXTSY8UDKHL9MBNJOFP636FLRNBR6P4T5Y7U1ENaWWW0100NBNJODKFP636F7D7JV7X1ALR4Q",
  "NBR6P4T5HL9MXTSY28Y2TY7UY8U2E9NYWWW0201OBNJODKFP636F7D7JV7X1ALR4QNBR6P4T5HL9MXTSY28Y2T",
  "Y7GY7UY8U1EOcWWW0103OBNJODKFP636F7D7JV7X1ALR4QNBR6P4T5HL9MXTSY28Y2TY7UY8UYR91EOYWWW010",
  "4NV7ZGVX1A7D7JY28Y2T4QXTSY8UDKHL9MBNJOFP636FLRNBR6P4T51CN0101OV7ZGVX1A7D7JY28Y2T4QXTSY",
  "8UDKHL9MBNJOFP636FLRNBR6P4T5ZIC0O0003JBNJODKFP636F7D7JV7X1ALR4QNBR6P4T5HL9MXTS1CJ0103L",
  "a9EaAC7D7JDKHL9MXTSBNJOFP636F4QV7X1ALRNBR6P4T519L0100LBNJODKFP636F7D7JV7X1ALR4QNBR6P4T",
  "5HL9MXTSaR9aAC0L0003BX1AV7636F4QNBFPR6P4T5DK0B0000GBNJODKFP636F7D7JV7X1ALR4QNBR6P4T519",
  "G0101HBNJODKFP636F7D7JV7X1ALR4QNBR6P4T5bC90H0005KBNJODKFP636F7D7JbCUc4X0V7bDVX1Ac5MLR4",
  "QNBR6P4T51CK0102LBNJODKFP636F7D7JbCUc4X0V7bDVX1Ac5MLR4QNBR6P4T5cAC0L0004MBNJODKFP6F7Jb",
  "CUc4X0V7bDVX1Ac5MLR4QNBR6P4T5cAX1cLGcLScDT0MYWWW0006ANBFP636FV74QR6P4T5DK0A0000BX1AV76",
  "36F4QNBFPR6P4T5DK1CB0101BX1AV76F4QNBFPR6P4T5DKdMX119B010384QNB636FR6P4T5DK1C80100ANBFG",
  "FP636F4QR6P4T5DK2C9A0201BNBFGFP636F4QR6P4T5DKe991CB01029T5R6P44QeMR636FNBDK0900019eMR4",
  "QNB636FR6P4T5DK0900009eMR4QNB636FR6P4T5DK1O90101AeRCeMR4QNB636FR6P4T5DK0A0002FeROeM9eM",
  "R4QNB636FR6P4T5DKf0Uf1Gf1SeV73EACF0301HeROeM9eMR4QNB636FR6P4T5DKf0Uf1Gf1SeV7fADf7C2EAH",
  "XWW020494QNB636FR6P4T5eMRDK1C90100AhA94QNB636FR6P4T5eMRDK0A0002FhA9hAV4QNB636FR6P4T5eM",
  "RDKhJUhKEhKShI73GACF0301GhA9hAV4QNB636FR6P4T5eMRDKhJUhKShI7hRDhOC2EAGmW02049T5R6P44QeM",
  "R636FNBDK1C901009T5R6P44QeMR636FNBDK1C9010D5eMRNB636F4Q2D7502009NBeMR636F4QDKT5R6P43D7",
  "C90301DNBeMR636F4Ql47l9El3DDKT5l5CR6P41GD0101DNBeMRP4636F4Ql47l9El3DDKT5l5CR61GD01024e",
  "M9eMR484Q2D7402014n1AV7NB4Q1C401008NBFGFP636Fn1AV74Q2C9802019NBFGFP636Fn1AV74Qn491C901",
  "026nHCnHX14Qn1AV7NB0600015nHX1NBn1AV74Q0500005nHX1n1AV7NB4Q1U501016nMCnHX1n1AV7NB4Q060",
  "0006nMUnHX1n1AV7NB4Q395C603019nMUnHX1n1AV7NB4QnVEnSCnQ946D349Y04028nMUnHX1n1AV7NB4QnVE",
  "nSC2G58Y02065NBnHX1n1AV74Q1C501006q49NBnHX1n1AV74Q0600006q4FNBnHX1n1AV74Q395C603019q4F",
  "NBnHX1n1AV74QqFEqCCqA946D349Y04028q4FNBnHX1n1AV74QqFEqCC2G58Y020654Qn1AV7NBnHX11C50101",
  "6sOF4Qn1AV7NBnHX1060004AsOF4Qn1AV7NBnHX1t64sS6sR6t531CAe0100DsOF484Qn1AV7NBnHX1t64sS6s",
  "R6t53t75tK91CDm010aF2230802329E23A4723D2123E31A3BA3403FB3C136CXK238B5220D0233C7235A122",
  "BC82218622B4J22A4J2391I431B37104001217082922C32802B14431B37104001217082922C32802B1622C",
  "6XP220B422A45439B2CE423517220F943C03714221AD238A322CB422C4422190431B330022B9022A802219",
  "0431B330022B9022A812203522A8062802922B1422A8062802922B1U431B3302431B32C222B112280522C6",
  "O23AB523EB0221E342C62BA423502438A3E1843702C55231102321522C8022C102331043912C2023B1063C",
  "12C3211122190439121B043B121C043C1211122190420223B0223C0431A233043202C7D22C81433A2C2063",
  "7A2C52A1022A3042A72C20637A2C52A112217J23EBB22C65638035B391822C52221822311023212237A222",
  "C8022C102331043B12C2023C1063D12C32111221B043B121C043C121D043D12111221B0420223C0223D043",
  "1A233043202C7D22C81433A2C20637A2C52A1022A3042A72C20637A2C52A112217a42214922C63221AH22C",
  "6K22C602280M231B5235B0221502351U230C0232C0233C1434C2C00430C2C20432C2C3022C41226002272X",
  "H235B92301R232C0233C0234C1435C2C20432C2C30433C2C4022C51226202273Y32301122C62aB51YM51hW",
  "WiWjnvcWayauWhcXuWXmWWW/cWWWWWhcsiWuWWcWWWZyuWWWWXiwvmWWWWu+XXhbgomYpqWdYcYdZcWWXgrgri",
  "WWWWWWWWWWZWWZ+iWWWZixiuWecWWWiWWlvmWWWjpjpWWeWWWcdmcWWXiWWWWWuimWXnyWWsZmWWyyilWWWWWy",
  "WedyWWXmieZmWWWXmkWXmiWYlWWWYrgsWWWWWbgrgr90aWWYWWWWWWWWWWWWWXWWWWWeWWmWWWeWWWWWWaWWWW",
  "XWWYWWWXWWWWWWXYWYWWWWWWWWmWWaWWWmWeWWmWWWWWWWWWYaefaeWWWWWWXWWWWWWWWWWWXWWWWWWWaWWWWW",
  "WWWWWWemWmWWeWWWXXYYWWWWWaaWfWWWXYeWXXWWWWWYXWWWWWaWWWXWWWnWWaWeWaXaeWWfWWWWWXXYYfWWWW",
  "W00YWWXWYYWWnXeWeWWYWmmYWWbWWeWWWbWWWWeWYYWeWWqWXWWWWqWWWXWenWXWaWWWWWWeWWYWWWeWaWbemW",
  "WWWWfXXXYaaoaXWaWWWWmWWWWWWWmoWWmaWmWWWYWWWWWWWYWoYaeWeXeaWaWemnXWWXWWoYWanWaWnaWWmmXX",
  "WWXWmoWXWYWWWmmXWemYYWaYYWoaWYanWWWWamnXamWWWW00cWaueZeWaWeWWYWWWWmWWWWoWWWWWWoXaWeWWY",
  "WWWWYeWWWWWYeamWWWWeYWWWWWWWWXmWXWYWZWYWWeWWWWWWWWWWWWWWWXWWWoaWWWXafaeWWYWWWaWWYemWWW",
  "ananWWWWWWYWmWWWWWWWWmWeaWWWWaWWYWWeWieWXWWWYWaWWpaWWWucWfmeWWmWcWWWaXWceWWmWWWWWWWWWW",
  "WWW00d/x//z/xx/+zyl/l//x++lxmfn//lWXXn////l/xv/kXcd/zyWacd///y/ky/z/t//////l//wl//d/t/",
  "rkl/////k++avpohty/sXd/+uWel///++h/+/p+ua//xWXX////v+hxtd/lzlp/t/kkay//z/+xx/oz/t+jt/+",
  "+/zz/vz++udy/v//++/zvkkZx/tZx+vt/usy////tYiyo/////VaWWYWaaWXYZmWmWWaXXmalskWWm/++kWWWW",
  "mWacWn+vuWYZ/xvuWWWZWnZWYWeWWWWWWmWWbmWWuWeWgnmWWWWWnXXxcijqeZWf+uWXd/tmWWWXXqWXWiXdxW",
  "Wa/++WWWWcXqaeuWmYmiWeWnnxZWWYWXaaWjYWeXoeWXXWYYWcYXXduZWcWWXXWYcnnyaWeyaXceWdfZWWWWez",
  "pZjWWWWW000G6234567"]
@[expose] def ext_full_reorder_queue_m7 : List (SigEntry × Nat) :=
  [(("f64u_add", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("full_rescale_m6", [i64], []), 88)]

@[expose] def hint_full_reorder_m6 : x64Isa.Hints := _decH #["14H1001900100030004000dN80000"]
@[expose] def ext_full_reorder_m6 : List (SigEntry × Nat) :=
  [(("full_reorder_queue_m7", [i64], [i64]), 280)]

@[expose] def hints : List x64Isa.Hints := [hint_full_reorder_sift_fid,
    hint_full_reorder_queue_m7, hint_full_reorder_m6]

@[expose] def ext : List (SigEntry × Nat) :=
  [(("f64u_add", [i64, i64], [i64]), 0),
   (("f64u_mul", [i64, i64], [i64]), 24),
   (("full_rescale_m6", [i64], []), 88)]

end LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.Reorder
