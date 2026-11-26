module

public import LeanQbe.T.FlatDirect
public import LeanQbe.T.Rega

/-!
# First-Order `TFlat` Register-Allocation Lowering (`RegaFlat`)

Direct `TFlat` lowering (`Rega.lowerFlatExpr`, `Rega.lowerFlatBlocks`, `Rega.lowerFlatFn`)
reusing all `Rega` backend state transitions (`stepPre`, `lowerOp`, `lowerLoad`, `lowerStore`,
`lowerTail`, `bindAbiParams`, `buildEntryBase`, `bindBlockParams`, `shuffle`) while maintaining
decoupled lexical environments `(vDepth : Nat, vEnv : Trie Nat, lEnv : List Nat)` alongside
the sequentially threaded fresh counters `(nv, nl, ip)`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Rega

/-! ## 1. Lexical Level Environments and First-Order Projection -/

/-- Resolve de Bruijn variable index `idx` to its `Rega` level under `(vDepth, vEnv)`. -/
def flatVar (vDepth : Nat) (vEnv : Trie Nat) (idx : Nat) : Nat :=
  vEnv.getD (vDepth - 1 - idx) 0

/-- Insert `n` consecutive fresh `Rega` levels `[nv, ..., nv + n - 1]` into `vEnv` at trie
keys `[vd, ..., vd + n - 1]`. -/
def insertVLevels : Nat → Nat → Nat → Trie Nat → Trie Nat
  | 0, _, _, env => env
  | n + 1, vd, nv, env => insertVLevels n (vd + 1) (nv + 1) (env.insert vd nv)

/-- Push fresh label levels for group signature `sig` starting at `nl` onto `lEnv`
(`0` = newest label, matching `pushTup (Tup.levels sig nl)`). -/
def pushLLevels : List (List Ty) → Nat → List Nat → List Nat
  | [], _, lEnv => lEnv
  | _ :: sig, nl, lEnv => pushLLevels sig (nl + 1) (nl :: lEnv)

/-- Resolve de Bruijn label index `j` to its `Rega` label level under `lEnv`. -/
def flatLabel (lEnv : List Nat) (j : Nat) : Nat :=
  (listGet? lEnv j).getD 0

/-- Project a first-order `Arg K t` to `Arg VNat t`. -/
def flatArg (vDepth : Nat) (vEnv : Trie Nat) {t : Ty} : Arg K t → Arg VNat t
  | .var idx => .var (flatVar vDepth vEnv idx)
  | .imm c => .imm c

/-- Project a first-order argument tuple to `Tup (Arg VNat) ts`. -/
def flatArgs (vDepth : Nat) (vEnv : Trie Nat) :
    {ts : List Ty} → Tup (Arg K) ts → Tup (Arg VNat) ts
  | [], () => ()
  | _ :: _, (a, as) => (flatArg vDepth vEnv a, flatArgs vDepth vEnv as)

/-- Project a first-order `Op K ts` to `Op VNat ts`. -/
def flatOp (vDepth : Nat) (vEnv : Trie Nat) {ts : List Ty} (op : Op K ts) : Op VNat ts :=
  ⟨op.code, flatArgs vDepth vEnv op.args⟩

/-! ## 2. Jump Threading, Branch Selection, and Lookaheads on `TFlat` -/

def zeroMoveJump?Flat {rs : List Ty} (I : Isa) (h : I.Hints) (ip : Nat) (st : SymState I)
    (vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat) : TFlat rs → Option Nat
  | .jump j args =>
    if !preEmpty h ip then none
    else
      let jLvl := flatLabel lEnv j
      (h.entry.find? jLvl).bind fun en =>
        (jumpTargets I (flatArgs vDepth vEnv args) en.ploc).bind fun argTgts =>
          if (en.live ++ argTgts).all
              (fun (sa, loc) => jumpLocOk I h.nslots loc && holdsLoc I st sa loc) then
            some jLvl
          else none
  | _ => none

def firstNonFwdFlat {rs : List Ty} (fwd : Trie Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Option Nat → Option Nat
  | _, .nil, _, ft => ft
  | _, .cons _ bs, lid, ft =>
    if (fwd.find? lid).isSome then firstNonFwdFlat fwd bs (lid + 1) ft else some lid

def jnzModeFlat {rs : List Ty} (I : Isa) (h : I.Hints) (ipT ipE : Nat) (st : SymState I)
    (canInv : Bool) (vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat) (t e : TFlat rs)
    (ft : Option Nat) (fwd : Trie Nat := .empty) : Bool × Option Nat :=
  let jt? := zeroMoveJump?Flat I h ipT st vDepth vEnv lEnv t
  let je? := if canInv then zeroMoveJump?Flat I h ipE st vDepth vEnv lEnv e else none
  match jt?, je? with
  | some jt, some je =>
    if ft == some (tgtLab fwd jt) then (true, some je) else (false, some jt)
  | some jt, none => (false, some jt)
  | none, some je => (true, some je)
  | none, none => (canInv && h.invertJnz.getD (ipE - 1) false, none)

def gprThread?Flat {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (ipT : Nat)
    (st1 : SymState I) (r : I.Reg) (vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat)
    (arm : TFlat rs) (fwd : Trie Nat := .empty) : Option Nat :=
  match arm with
  | .jump j args =>
    let jLvl := flatLabel lEnv j
    let cl := (I.gpr.jnzGpr r (lname fn (tgtLab fwd jLvl))).2
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] cl st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
      flags := killFlags I cl st1.flags }
    zeroMoveJump?Flat (rs := rs) I h ipT stB vDepth vEnv lEnv (.jump j args)
  | _ => none

def threadFusedArmFlat {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (ipA : Nat)
    (st1 : SymState I) (emit : Sym → Option (List I.Directive × FlagMask))
    (vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat) (arm : TFlat rs)
    (fwd : Trie Nat := .empty) : Option (Nat × List I.Directive × SymState I) :=
  match arm with
  | .jump j _ =>
    let jLvl := flatLabel lEnv j
    (emit (lname fn (tgtLab fwd jLvl))).bind fun (br, cl) =>
      let stB := { st1 with
        regs := killRegs I I.frame.scratch [] cl st1.regs
        zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
        flags := killFlags I cl st1.flags }
      if zeroMoveJump?Flat I h ipA stB vDepth vEnv lEnv arm == some jLvl then
        some (jLvl, br, stB)
      else none
  | _ => none

def fuseJnzChoiceFlat {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : SymState I) (vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat) (t e : TFlat rs)
    (ft : Option Nat) (emit : Bool → Sym → Option (List I.Directive × FlagMask))
    (fwd : Trie Nat := .empty) : Option (Bool × Option Nat × List I.Directive × SymState I) :=
  let invChoice := h.invertJnz.getD (ipE - 1) false
  (emit invChoice (lname fn nl)).map fun (brNl, clNl) =>
    let stNl := { st1 with
      regs := killRegs I I.frame.scratch [] clNl st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
      flags := killFlags I clNl st1.flags }
    let fwd? := threadFusedArmFlat I h fn ipT st1 (emit false) vDepth vEnv lEnv t fwd
    let inv? := threadFusedArmFlat I h fn ipE st1 (emit true) vDepth vEnv lEnv e fwd
    match fwd?, inv? with
    | some (jt, brF, stF), some (je, brI, stI) =>
      if ft == some (tgtLab fwd jt) then (true, some je, brI, stI) else (false, some jt, brF, stF)
    | some (jt, brF, stF), none => (false, some jt, brF, stF)
    | none, some (je, brI, stI) => (true, some je, brI, stI)
    | none, none => (invChoice, none, brNl, stNl)

def finishCmpJnzFlat {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : SymState I) (vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat) (t e : TFlat rs)
    (ft : Option Nat) (fwd : Trie Nat) (cc : I.Cond) (cmpCode : List I.Directive)
    (cl : FlagMask) (fl : Option FlagFact) :
    Bool × Option Nat × List I.Directive × SymState I :=
  let stCmp := { st1 with
    regs := killRegs I I.frame.scratch [] cl st1.regs
    zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
    flags := fl }
  let stB := { stCmp with
    regs := killRegs I I.frame.scratch [] FlagMask.none stCmp.regs
    zeroExt32 := killZeroExt I.frame.scratch stCmp.zeroExt32
    flags := killFlags I FlagMask.none stCmp.flags }
  let p := jnzModeFlat I h ipT ipE stB true vDepth vEnv lEnv t e ft fwd
  let sym := lname fn (match p.2 with | some j => tgtLab fwd j | none => nl)
  (p.1, p.2, cmpCode ++ I.gpr.jcc (if p.1 then I.gpr.negCond cc else cc) sym, stB)

def jnzSetupFlat {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym) (nl ipT ipE : Nat)
    (st1 : SymState I) (vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat) (t e : TFlat rs)
    (ft : Option Nat) (cond : JnzCond I) (fwd : Trie Nat := .empty) :
    Option (Bool × Option Nat × List I.Directive × SymState I) :=
  match cond with
  | .flag cc =>
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] FlagMask.none st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
      flags := killFlags I FlagMask.none st1.flags }
    let p := jnzModeFlat I h ipT ipE stB true vDepth vEnv lEnv t e ft fwd
    let sym := lname fn (match p.2 with | some j => tgtLab fwd j | none => nl)
    some (p.1, p.2, I.gpr.jcc (if p.1 then I.gpr.negCond cc else cc) sym, stB)
  | .gpr r =>
    match I.gpr.jnzGprInv? with
    | some jnzFn =>
      fuseJnzChoiceFlat I h fn nl ipT ipE st1 vDepth vEnv lEnv t e ft
        (fun inv l => some (jnzFn r inv l)) fwd
    | none =>
      let tg := gprThread?Flat I h fn ipT st1 r vDepth vEnv lEnv t fwd
      let p := I.gpr.jnzGpr r (lname fn (match tg with | some j => tgtLab fwd j | none => nl))
      let stB := { st1 with
        regs := killRegs I I.frame.scratch [] p.2 st1.regs
        zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
        flags := killFlags I p.2 st1.flags }
      some (false, tg, p.1, stB)
  | .slot idx =>
    let stB := { st1 with
      regs := killRegs I I.frame.scratch [] FlagMask.all st1.regs
      zeroExt32 := killZeroExt I.frame.scratch st1.zeroExt32
      flags := killFlags I FlagMask.all st1.flags }
    let p := jnzModeFlat I h ipT ipE stB true vDepth vEnv lEnv t e ft fwd
    let sym := lname fn (match p.2 with | some j => tgtLab fwd j | none => nl)
    (I.gpr.jnzMem (spAddr I idx) p.1 sym).bind fun (br, cl) =>
      if cl == FlagMask.all then some (p.1, p.2, br, stB) else none
  | .cmpZero co w r =>
    fuseJnzChoiceFlat I h fn nl ipT ipE st1 vDepth vEnv lEnv t e ft (fun inv l =>
      I.gpr.cmpZeroJcc (if inv then co.neg else co) w r l) fwd
  | .cmpZeroMem co w x aa cc =>
    (I.gpr.cmpMem co w aa (.imm 0#w) (.flag cc)).map fun (cmpCode, cl) =>
      let fl := (cmpMemRes I st1 co w (.var x) (.immBits w 0#64) (.flag cc) cmpCode cl).2.2.1
      finishCmpJnzFlat I h fn nl ipT ipE st1 vDepth vEnv lEnv t e ft fwd cc cmpCode cl fl
  | .cmpZeroFlag co w x r cc =>
    (I.gpr.op (.cmp co (.bits w)) (.gpr r, .imm 0#w, ()) (.flag cc, ()) .default).map
      fun (cmpCode, cl) =>
        let fl := if Nat.ble w 64 then
          match I.gpr.cmpFlagsOut? co w (.gpr r) (.imm 0#w) (.flag cc) with
          | some lf => some (.cmp w (if lf then .var x else .immBits w 0#64)
                                     (if lf then .immBits w 0#64 else .var x) false)
          | none => killFlags I cl st1.flags
        else killFlags I cl st1.flags
        finishCmpJnzFlat I h fn nl ipT ipE st1 vDepth vEnv lEnv t e ft fwd cc cmpCode cl fl
  | .testImm neg w r mask =>
    fuseJnzChoiceFlat I h fn nl ipT ipE st1 vDepth vEnv lEnv t e ft (fun inv l =>
      I.gpr.testJcc (if inv then !neg else neg) w r mask l) fwd

def finishJnzBranchFlat {rs : List Ty} (I : Isa) (fn : Sym) (lEnv : List Nat) (nl : Nat)
    (tgt? : Option Nat) (b_taken : TFlat rs) (br c_ft c_taken : List I.Directive)
    (nv2 nl2 ip2 : Nat) : Res I :=
  match tgt? with
  | some j => match b_taken with
    | .jump j' _ =>
      if Nat.beq (flatLabel lEnv j') j && c_taken.isEmpty then
        .ok (br ++ c_ft, nv2, nl2, ip2)
      else .error "jnz: bad thread"
    | _ => .error "jnz: not jump"
  | none => .ok (br ++ c_ft ++ [I.frame.label (lname fn nl)] ++ c_taken, nv2, nl2, ip2)

def jumpAvoidsFlat {rs : List Ty} {I : Isa} (h : I.Hints) (x vDepth : Nat) (vEnv : Trie Nat)
    (lEnv : List Nat) : TFlat rs → Bool
  | .jump j args => !argsHaveVar (flatArgs vDepth vEnv args) x &&
    match h.entry.find? (flatLabel lEnv j) with
    | some en => en.live.all fun (sa, _) => !symArgEq sa (.var x)
    | none => false
  | _ => false

def loadSextNextFlat {rs : List Ty} (I : Isa) (h : I.Hints) (vDepth : Nat) (vEnv : Trie Nat)
    (lEnv : List Nat) (nv ip : Nat) (st : SymState I) (t : Ty) (a : Arg VNat i64)
    (e : TFlat rs) : Bool :=
  let st' := { st with memDefs := st.memDefs.insert nv (t, a) }
  let sextAt : Nat → Trie Nat → Nat → Nat → TFlat rs → Bool := fun vd' ve' ip' nv' e' =>
    match e' with
    | .let_ op _ =>
      let op' := flatOp vd' ve' op
      match sextVar? op'.code op'.args with
      | some (_, _, x) =>
        Nat.beq x nv && h.dest.find? nv' == h.dest.find? nv && fusesLoad I h st' nv' ip' op'
      | none => false
    | _ => false
  isGprTy I t && (sextAt vDepth vEnv (ip + 1) (nv + 1) e ||
    match e with
    | .let_ (ts := ts) op k =>
      let op' := flatOp vDepth vEnv op
      cmpVarImm? op'.code op'.args == some nv &&
        (match h.dest.find? (nv + 1) with | some (.flag _) => true | _ => false) &&
        fusesLoad I h st' (nv + 1) (ip + 1) op' &&
        let vd2 := vDepth + ts.length
        let ve2 := insertVLevels ts.length vDepth (nv + 1) vEnv
        match k with
        | .jnz (.var cx) tt ee =>
          Nat.beq (flatVar vd2 ve2 cx) (nv + 1) && (h.pre.find? (ip + 2)).isNone &&
            ((jumpAvoidsFlat h nv vd2 ve2 lEnv tt && sextAt vd2 ve2 (ip + 3) (nv + 2) ee) ||
              (jumpAvoidsFlat h nv vd2 ve2 lEnv ee && sextAt vd2 ve2 (ip + 4) (nv + 2) tt))
        | _ => false
    | _ => false)

mutual
/-- Instruction-pointer count consumed by `lowerFlatExpr` on `tf` starting at `(nv, nl)`. -/
def exprIpCountFlat {rs : List Ty} : TFlat rs → Nat → Nat → Nat × Nat × Nat
  | .let_ (ts := ts) _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCountFlat k (nv + ts.length) nl
    (nv1, nl1, d + 1)
  | .load _ _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCountFlat k (nv + 1) nl
    (nv1, nl1, d + 1)
  | .store _ _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCountFlat k nv nl
    (nv1, nl1, d + 1)
  | .call _ bs _ k, nv, nl =>
    let (nv1, nl1, d) := exprIpCountFlat k (nv + bs.length) nl
    (nv1, nl1, d + 1)
  | .jnz (.imm b) t e, nv, nl =>
    let (nv1, nl1, d) := if b then exprIpCountFlat t nv nl else exprIpCountFlat e nv nl
    (nv1, nl1, d + 1)
  | .jnz (.var _) t e, nv, nl =>
    let (nv1, nl1, de) := exprIpCountFlat e nv (nl + 1)
    let (nv2, nl2, dt) := exprIpCountFlat t nv1 nl1
    (nv2, nl2, de + dt + 1)
  | .jump _ _, nv, nl | .ret _, nv, nl | .exit _ _, nv, nl | .hlt, nv, nl => (nv, nl, 1)
  | .group (sig := sig) bodies k, nv, nl =>
    let (nv1, nl1, dk) := exprIpCountFlat k nv (nl + sig.length)
    let (nv2, nl2, db) := blocksIpCountFlat bodies nv1 nl1
    (nv2, nl2, dk + db)

def blocksIpCountFlat {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Nat → Nat × Nat × Nat
  | _, .nil, nv, nl => (nv, nl, 0)
  | _, .cons (ts := ts) b bs, nv, nl =>
    let (nv1, nl1, db) := exprIpCountFlat b (nv + ts.length) nl
    let (nv2, nl2, dbs) := blocksIpCountFlat bs nv1 nl1
    (nv2, nl2, db + dbs)
end

def jnzIpTFlat {rs : List Ty} (nv nl ip : Nat) (t e : TFlat rs) : Nat :=
  match t with
  | .jump _ _ => ip + 1 + (exprIpCountFlat e nv (nl + 1)).2.2
  | _ => ip + 1

def deferJnzNextFlat {rs : List Ty} (I : Isa) (h : I.Hints) (fn : Sym)
    (vd' : Nat) (ve' : Trie Nat) (nv nl ip : Nat) (st1 : SymState I)
    {ts : List Ty} (op : Op VNat ts) (k : TFlat rs) : Bool :=
  match ts, k with
  | [.bool], .jnz (.var cx) _ _ =>
    Nat.beq (flatVar vd' ve' cx) nv && h.deferJnz.getD ip false &&
      match lowerOp I h nv ip st1 op true with
      | some (_, st2) =>
        match stepPre I h (ip + 1) st2 with
        | some (_, stAfter) =>
          match findJnzCond I h.nslots stAfter nv with
          | some (.flag _) => true
          | some (.cmpZero co w r) => (I.gpr.cmpZeroJcc co w r (lname fn nl)).isSome
          | some (.cmpZeroMem _ _ _ _ cc)
          | some (.cmpZeroFlag _ _ _ _ cc) => h.dest.find? nv != some (.flag cc)
          | some (.testImm neg w r mask) => (I.gpr.testJcc neg w r mask (lname fn nl)).isSome
          | _ => false
        | none => false
      | none => false
  | _, _ => false

def deferLeaNextFlat {rs : List Ty} (I : Isa) (h : I.Hints) (vd' : Nat) (ve' : Trie Nat)
    (nv ip : Nat) (st1 : SymState I) {ts : List Ty} (op : Op VNat ts) (k : TFlat rs) : Bool :=
  if !isLeaDeferCand op.code then false
  else
    match ts, k with
    | [_], .let_ (ts := ts2) op2 _ =>
      let op2' := flatOp vd' ve' op2
      match recordDef st1.defs op.code op.args with
      | some df =>
        match stepPre I h (ip + 1) { st1 with defs := st1.defs.insert nv df } with
        | some (_, stAfter) =>
          match resolveDsts I h ts2 (nv + 1) with
          | some dsts2 =>
            (tryLeaArith I stAfter op2'.code op2'.args dsts2).isSome &&
              h.deferLea.getD ip false
          | none => false
        | none => false
      | none => false
    | _, _ => false

def blockTrampoline?Flat {rs : List Ty} (I : Isa) (h : I.Hints) (defs : Trie DefFact)
    (vw : Trie SlotWidth) (lid vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat)
    (nv ip : Nat) (ts : List Ty) (b : TFlat rs) : Option Nat :=
  match h.entry.find? lid with
  | none => none
  | some en =>
    if !entryScopeOk nv en then none
    else match buildEntryBase I h.nslots vw en.live
        { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
      | none => none
      | some baseSt =>
        match bindBlockParams I h.nslots ts en.ploc nv baseSt with
        | none => none
        | some initSt =>
          match b with
          | .jump j' args' =>
            let jLvl' := flatLabel lEnv j'
            let argsV := flatArgs (vDepth + ts.length)
              (insertVLevels ts.length vDepth nv vEnv) args'
            match stepPre I h ip initSt, h.entry.find? jLvl' with
            | some ([], st1), some en' =>
              match jumpTargets I argsV en'.ploc with
              | none => none
              | some argTgts =>
                let tgts := en'.live ++ argTgts
                if !(tgts.all fun (_, loc) => jumpLocOk I h.nslots loc) then none
                else match shuffle I h.nslots h.saved st1 tgts with
                  | some ([], _) => some jLvl'
                  | _ => none
            | _, _ => none
          | _ => none

def collectRawFwdsFlat {rs : List Ty} (I : Isa) (h : I.Hints) (defs : Trie DefFact)
    (vw : Trie SlotWidth) (fwd : Trie Nat) (fwdTgts : Trie Bool)
    (vDepth : Nat) (vEnv : Trie Nat) (lEnv : List Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Nat → Nat → Nat →
    Trie Nat → List Nat → Trie Nat × List Nat
  | _, .nil, _, _, _, _, raw, lids => (raw, lids)
  | _, .cons (ts := ts) b bs, lid, nv, nl, ip, raw, lids =>
    let raw1_lids :=
      if (fwd.find? lid).isNone && !(fwdTgts.getD lid false) then
        match blockTrampoline?Flat I h defs vw lid vDepth vEnv lEnv nv ip ts b with
        | some j' => (raw.insert lid j', lid :: lids)
        | none => (raw, lids)
      else (raw, lids)
    let (nv1, nl1, d) := exprIpCountFlat b (nv + ts.length) nl
    collectRawFwdsFlat I h defs vw fwd fwdTgts vDepth vEnv lEnv bs
      (lid + 1) nv1 nl1 (ip + d) raw1_lids.1 raw1_lids.2

def findGroupFwdsFlat {rs : List Ty} (I : Isa) (h : I.Hints) (st : SymState I)
    (vDepth : Nat) (vEnv : Trie Nat) (lEnv' : List Nat)
    {sig : List (List Ty)} (bodies : TBlocks rs sig) (k : TFlat rs)
    (nv nl ip : Nat) (fwd : Trie Nat) (fwdTgts : Trie Bool) : Trie Nat × Trie Bool :=
  let (nv1, nl1, d) := exprIpCountFlat k nv (nl + sig.length)
  let (raw, lids) :=
    collectRawFwdsFlat I h st.defs st.vecWidths fwd fwdTgts vDepth vEnv lEnv' bodies
      nl nv1 nl1 (ip + d) .empty []
  lids.foldl
    (fun (f, ft) lid =>
      match resolveTrampoline raw fwd (sig.length + 1) lid with
      | some m =>
        if (raw.find? m).isNone && (fwd.find? m).isNone && m != lid then
          (f.insert lid m, ft.insert m true)
        else (f, ft)
      | none => (f, ft))
    (fwd, fwdTgts)

/-! ## 3. Core First-Order `lowerFlatExpr`, `lowerFlatBlocks`, `lowerFlatFn` -/

mutual
/-- First-order register-allocation lowering over `TFlat rs`, maintaining lexical
`(vDepth, vEnv, lEnv)` decoupled from sequential counters `(nv, nl, ip)`. -/
def lowerFlatExpr (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    TFlat rs → Nat → Trie Nat → List Nat → Nat → Nat → Nat → SymState I → Option Nat →
    (fwd : Trie Nat := .empty) → (fwdTgts : Trie Bool := .empty) → Res I
  | .let_ (ts := ts) op k, vDepth, vEnv, lEnv, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "let: pre"
    | some (mc, st1) =>
      let op' := flatOp vDepth vEnv op
      let vd' := vDepth + ts.length
      let ve' := insertVLevels ts.length vDepth nv vEnv
      let df := deferJnzNextFlat I h fn vd' ve' nv nl ip st1 op' k ||
        deferLeaNextFlat I h vd' ve' nv ip st1 op' k
      match lowerOp I h nv ip st1 op' df with
      | none => .error "let: op"
      | some (c, st2) =>
        prepend (mc ++ c)
          (lowerFlatExpr I h E fn k vd' ve' lEnv (nv + ts.length) nl (ip + 1) st2 ft fwd fwdTgts)
  | .load t a k, vDepth, vEnv, lEnv, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "load: pre"
    | some (mc, st1) =>
      let a' := flatArg vDepth vEnv a
      let vd' := vDepth + 1
      let ve' := vEnv.insert vDepth nv
      match lowerLoad I h nv ip st1 t a' (loadSextNextFlat I h vd' ve' lEnv nv ip st1 t a' k) with
      | none => .error "load: dst/addr"
      | some (c, st2) =>
        prepend (mc ++ c)
          (lowerFlatExpr I h E fn k vd' ve' lEnv (nv + 1) nl (ip + 1) st2 ft fwd fwdTgts)
  | .store (t := t) v a k, vDepth, vEnv, lEnv, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "store: pre"
    | some (mc, st1) =>
      let v' := flatArg vDepth vEnv v
      let a' := flatArg vDepth vEnv a
      match lowerStore I st1 (h.variant.getD ip .default) t v' a' with
      | none => .error "store: op/addr"
      | some (c, st2) =>
        prepend (mc ++ c)
          (lowerFlatExpr I h E fn k vDepth vEnv lEnv nv nl (ip + 1) st2 ft fwd fwdTgts)
  | .call f (as := as) bs args k, vDepth, vEnv, lEnv, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "call: pre"
    | some (mc, st1) =>
      if !calleeAllowed E f as bs then .error "call: callee"
      else match I.assignArgs as, I.assignRets bs with
        | some argLocs, some retLocs =>
          let args' := flatArgs vDepth vEnv args
          match abiTargets I args' argLocs with
          | none => .error "call: imm"
          | some tgts => match shuffle I h.nslots h.saved st1 tgts (h.deadFlags.getD ip false) with
            | none => .error "call: shuffle"
            | some (sc, st2) => match bindAbiParams I retLocs nv (afterCallState I h.saved st2) with
              | none => .error "call: ret bind"
              | some st4 =>
                let vd' := vDepth + bs.length
                let ve' := insertVLevels bs.length vDepth nv vEnv
                prepend (mc ++ sc ++
                    canonAbiCode I argLocs (abiSkips I st2.regs st2.zeroExt32 args' argLocs) ++
                    I.frame.call f)
                  (lowerFlatExpr I h E fn k vd' ve' lEnv (nv + bs.length) nl (ip + 1) st4 ft
                    fwd fwdTgts)
        | _, _ => .error "call: abi"
  | .jnz (.imm b) t e, vDepth, vEnv, lEnv, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "jnz: pre"
    | some (mc, st1) =>
      prepend mc (if b then
        lowerFlatExpr I h E fn t vDepth vEnv lEnv nv nl (ip + 1) st1 ft fwd fwdTgts
      else
        lowerFlatExpr I h E fn e vDepth vEnv lEnv nv nl (ip + 1) st1 ft fwd fwdTgts)
  | .jnz (.var cx) t e, vDepth, vEnv, lEnv, nv, nl, ip, st, ft, fwd, fwdTgts =>
    match stepPre I h ip st with
    | none => .error "jnz: pre"
    | some (mc, st1) =>
      let cx' := flatVar vDepth vEnv cx
      match findJnzCond I h.nslots st1 cx' with
      | none => .error "jnz: cond"
      | some cond =>
        match jnzSetupFlat I h fn nl (jnzIpTFlat nv nl ip t e) (ip + 1) st1
            vDepth vEnv lEnv t e ft cond fwd with
        | none => .error "jnz: setup"
        | some (inv, tgt?, br, stBr) =>
          let ftT := match tgt? with | some j => some (tgtLab fwd j) | none => ft
          let ftF := match tgt? with | some _ => ft | none => none
          match lowerFlatExpr I h E fn e vDepth vEnv lEnv nv (nl + 1) (ip + 1) stBr
              (if inv then ftT else ftF) fwd fwdTgts with
          | .error err => .error err
          | .ok (ce, nv1, nl1, ip1) =>
            match lowerFlatExpr I h E fn t vDepth vEnv lEnv nv1 nl1 ip1 stBr
                (if inv then ftF else ftT) fwd fwdTgts with
            | .error err => .error err
            | .ok (ct, nv2, nl2, ip2) =>
              prepend mc (if inv then
                finishJnzBranchFlat I fn lEnv nl tgt? e br ct ce nv2 nl2 ip2
              else
                finishJnzBranchFlat I fn lEnv nl tgt? t br ce ct nv2 nl2 ip2)
  | .jump j args, vDepth, vEnv, lEnv, nv, nl, ip, st, ft, fwd, _ =>
    let jLvl := flatLabel lEnv j
    match stepPre I h ip st, h.entry.find? jLvl with
    | some (mc, st1), some en =>
      let args' := flatArgs vDepth vEnv args
      match jumpTargets I args' en.ploc with
      | none => .error "jump: arity"
      | some argTgts =>
        let tgts := en.live ++ argTgts
        if !(tgts.all fun (_, loc) => jumpLocOk I h.nslots loc) then .error "jump: loc"
        else match shuffle I h.nslots h.saved st1 tgts (h.deadFlags.getD ip false) with
          | none => .error "jump: shuffle"
          | some (sc, _) =>
            let jt := tgtLab fwd jLvl
            .ok (mc ++ sc ++ (if ft == some jt then [] else I.gpr.jmp (lname fn jt)),
                 nv, nl, ip + 1)
    | _, _ => .error "jump: pre/entry"
  | .ret vs, vDepth, vEnv, _, nv, nl, ip, st, _, _, _ =>
    match stepPre I h ip st, I.assignRets rs with
    | some (mc, st1), some retLocs =>
      lowerTail I h E st1 mc I.frame.ret (flatArgs vDepth vEnv vs) retLocs nv nl ip
    | _, _ => .error "ret: pre/abi"
  | .exit f (as := as) args, vDepth, vEnv, _, nv, nl, ip, st, _, _, _ =>
    match stepPre I h ip st, I.assignArgs as with
    | some (mc, st1), some argLocs =>
      if !E.exits.contains f then .error "exit: target"
      else lowerTail I h E st1 mc (I.frame.exitJmp f) (flatArgs vDepth vEnv args) argLocs nv nl ip
    | _, _ => .error "exit: pre/abi"
  | .hlt, _, _, _, nv, nl, ip, _, _, _, _ => .ok ([], nv, nl, ip + 1)
  | .group (sig := sig) bodies k, vDepth, vEnv, lEnv, nv, nl, ip, st, ft, fwd, fwdTgts =>
    let lEnv' := pushLLevels sig nl lEnv
    let (fwd', tgts') :=
      findGroupFwdsFlat I h st vDepth vEnv lEnv' bodies k nv nl ip fwd fwdTgts
    let ftK := firstNonFwdFlat fwd' bodies nl ft
    match lowerFlatExpr I h E fn k vDepth vEnv lEnv' nv (nl + sig.length) ip st
        ftK fwd' tgts' with
    | .error err => .error err
    | .ok (ck, nv1, nl1, ip1) =>
      prepend ck
        (lowerFlatBlocks I h E fn bodies nl vDepth vEnv lEnv' nv1 nl1 ip1
          st.defs st.vecWidths ft fwd' tgts')

/-- Mutual companion to `lowerFlatExpr` over `TBlocks rs sig`. -/
def lowerFlatBlocks (I : Isa) (h : I.Hints) (E : Ext) (fn : Sym) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Nat → Nat → Trie Nat → List Nat →
    Nat → Nat → Nat → Trie DefFact → Trie SlotWidth → Option Nat →
    (fwd : Trie Nat := .empty) → (fwdTgts : Trie Bool := .empty) → Res I
  | _, .nil, _, _, _, _, nv, nl, ip, _, _, _, _, _ => .ok ([], nv, nl, ip)
  | _, .cons (ts := ts) b bs, lid, vDepth, vEnv, lEnv, nv, nl, ip, defs, vw, ft, fwd, fwdTgts =>
    match fwd.find? lid with
    | some fwdTgt =>
      match blockTrampoline?Flat I h defs vw lid vDepth vEnv lEnv nv ip ts b with
      | some j' =>
        if !(Nat.beq (tgtLab fwd j') fwdTgt && (fwd.find? fwdTgt).isNone) then .error "block: fwd"
        else lowerFlatBlocks I h E fn bs (lid + 1) vDepth vEnv lEnv
          (nv + ts.length) nl (ip + 1) defs vw ft fwd fwdTgts
      | none => .error "block: fwd"
    | none =>
      match h.entry.find? lid with
      | none => .error "block: entry"
      | some en =>
        if !entryScopeOk nv en then .error "block: scope"
        else match buildEntryBase I h.nslots vw en.live
            { regs := [], slots := .empty, defs := defs, vecWidths := vw } with
          | none => .error "block: live"
          | some baseSt => match bindBlockParams I h.nslots ts en.ploc nv baseSt with
            | none => .error "block: plocs"
            | some initSt =>
              let ftB := firstNonFwdFlat fwd bs (lid + 1) ft
              let vd' := vDepth + ts.length
              let ve' := insertVLevels ts.length vDepth nv vEnv
              match lowerFlatExpr I h E fn b vd' ve' lEnv (nv + ts.length) nl ip initSt ftB
                  fwd fwdTgts with
              | .error err => .error err
              | .ok (cb, nv1, nl1, ip1) =>
                prepend (I.frame.label (lname fn lid) :: cb)
                  (lowerFlatBlocks I h E fn bs (lid + 1) vDepth vEnv lEnv nv1 nl1 ip1
                    defs vw ft fwd fwdTgts)
end

/-- Direct `TFlatFn` entry point for `Rega` lowering, matching `Rega.lowerFn`. -/
def lowerFlatFn (I : Isa) (h : I.Hints) (E : Ext) (f : TFlatFn) :
    Except String (List I.Directive) :=
  if !(listNodup h.saved && h.saved.all (I.frame.calleeSaved.contains ·)) then .error "fn: saved"
  else match I.assignArgs f.as, I.assignRets f.rs with
    | some argLocs, some _ =>
      match bindAbiParams I argLocs 0
        { regs := [], slots := .empty, defs := .empty, vecWidths := .empty } with
      | none => .error "fn: abi bind"
      | some st0 =>
        let vEnv0 := insertVLevels f.as.length 0 0 .empty
        match lowerFlatExpr I h E f.name f.body f.as.length vEnv0 [] f.as.length 0 0 st0 none with
        | .ok (c, _, _, _) =>
          .ok (I.frame.label f.name :: (fnPrologue I h E ++ saveCs I h.nslots h.saved ++ c))
        | .error e => .error e
    | _, _ => .error "fn: abi"

end Rega
end LeanQbe.T
