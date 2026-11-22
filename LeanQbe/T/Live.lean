module

public import LeanQbe.T.Rega

/-!
# Typed Liveness Analysis (`T7a`, untrusted, reusing `Arg.vars`/`tupVars`/`Op.vars`)

First-order structural mirror `Tree`/`TreeBlocks` of `Expr VNat LNat rs` / `Blocks VNat LNat rs sig`
matching the exact `(nv, nl, ip)` numbering of `Rega.lowerExpr` / `Rega.lowerBlocks`, together with
join-point liveness fixpoint (`liveLabels`), bottom-up `fillLive`, `acrossCalls`, and `loopBlocks`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Live

open Rega

inductive Bank where
  | gpr | vec (w : SlotWidth)
  deriving DecidableEq, Repr, Inhabited

def bankOf (I : Isa) (t : Ty) : Bank :=
  match vecWidth? I t with | some w => .vec w | none => .gpr

def Bank.isVec : Bank → Bool | .vec _ => true | .gpr => false
def Bank.slots : Bank → Nat | .gpr => 1 | .vec w => w.slots
def Bank.slotWidth : Bank → SlotWidth | .gpr => .w64 | .vec w => w

/-! ## Small `Nat` Set Operations (backed by `Trie Unit`) -/

def trieOfList (xs : List Nat) : Trie Unit :=
  xs.foldl (fun t x => t.insert x ()) .empty

def trieMem (t : Trie Unit) (x : Nat) : Bool :=
  (t.find? x).isSome

def natMem (x : Nat) : List Nat → Bool
  | [] => false | y :: ys => if Nat.beq x y then true else natMem x ys

def erase (x : Nat) (xs : List Nat) : List Nat :=
  xs.filter (!Nat.beq · x)

def eraseMany (xs : List Nat) (ys : List Nat) : List Nat :=
  if xs.isEmpty then ys
  else
    let s := trieOfList xs
    ys.filter (!trieMem s ·)

def union (a b : List Nat) : List Nat :=
  if b.isEmpty then a
  else
    let seen := trieOfList a
    let base := if a.isEmpty then [] else a.reverse
    (b.foldl (fun (acc, s) x =>
      if trieMem s x then (acc, s) else (x :: acc, s.insert x ())) (base, seen)).1.reverse

def dedup (xs : List Nat) : List Nat :=
  if xs.isEmpty then []
  else
    (xs.foldl (fun (acc, s) x =>
      if trieMem s x then (acc, s) else (x :: acc, s.insert x ())) ([], .empty)).1.reverse

/-- Variable IDs reusing `Ops.lean`'s `Arg.vars`, `tupVars`, and `Op.vars` (`B4`). -/
def argVarIds {t : Ty} (a : Arg VNat t) : List Nat := a.vars.map (·.2)
def tupVarIds {ts : List Ty} (as : Tup (Arg VNat) ts) : List Nat := dedup ((tupVars as).map (·.2))
def opVarIds {ts : List Ty} (op : Op VNat ts) : List Nat := dedup (op.vars.map (·.2))

def storeVarIds (addrDeps rmwDeps : Trie (List Nat)) (ip : Nat) {t : Ty}
    (v : Arg VNat t) (a : Arg VNat i64) : List Nat :=
  rmwDeps.getD ip (dedup (argVarIds v ++ addrDeps.getD ip (argVarIds a)))

def levelTypes (nv : Nat) : List Ty → List (Nat × Ty)
  | [] => [] | t :: ts => (nv, t) :: levelTypes (nv + 1) ts

def recordTypes (ps : List (Nat × Ty)) (tys : Trie Ty) : Trie Ty :=
  ps.foldl (fun acc (x, t) => acc.insert x t) tys

/-! ## First-Order Tree Mirroring `Rega.lowerExpr` / `Rega.lowerBlocks` -/

mutual
inductive Tree where
  | let_ (lv : List Nat) (ip nv0 : Nat) (ts : List Ty) (op : Op VNat ts) (k : Tree)
  | load (lv : List Nat) (ip x : Nat) (t : Ty) (a : Arg VNat i64) (k : Tree)
  | store (lv : List Nat) (ip : Nat) (t : Ty) (v : Arg VNat t) (a : Arg VNat i64) (k : Tree)
  | call (lv : List Nat) (ip nv0 : Nat) (g : Sym) (as bs : List Ty) (args : Tup (Arg VNat) as) (k : Tree)
  | jnz (lv : List Nat) (ip c l : Nat) (t e : Tree)
  | skip (lv : List Nat) (ip : Nat) (k : Tree)
  | jump (lv : List Nat) (ip j : Nat) (ts : List Ty) (args : Tup (Arg VNat) ts)
  | ret (lv : List Nat) (ip : Nat) (rs : List Ty) (vs : Tup (Arg VNat) rs)
  | exit (lv : List Nat) (ip : Nat) (g : Sym) (as : List Ty) (args : Tup (Arg VNat) as)
  | stop (ip : Nat)
  | group (lv : List Nat) (bs : TreeBlocks) (k : Tree)

inductive TreeBlocks where
  | nil
  | cons (l : Nat) (ps : List (Nat × Ty)) (b : Tree) (bs : TreeBlocks)
end

instance : Inhabited Tree := ⟨.stop 0⟩

def Tree.lv : Tree → List Nat
  | .let_ lv .. | .load lv .. | .store lv .. | .call lv .. | .jnz lv ..
  | .skip lv .. | .jump lv .. | .ret lv .. | .exit lv .. | .group lv .. => lv
  | .stop _ => []

mutual
def toTreeExpr {rs : List Ty} :
    Expr VNat LNat rs → Nat → Nat → Nat → Trie Ty → Tree × Nat × Nat × Nat × Trie Ty
  | .let_ (ts := ts) op k, nv, nl, ip, tys =>
    let (tk, r) := toTreeExpr (k (Tup.levels ts nv)) (nv + ts.length) nl (ip + 1) (recordTypes (levelTypes nv ts) tys)
    (.let_ [] ip nv ts op tk, r)
  | .load t a k, nv, nl, ip, tys =>
    let (tk, r) := toTreeExpr (k nv) (nv + 1) nl (ip + 1) (tys.insert nv t)
    (.load [] ip nv t a tk, r)
  | .store (t := t) v a k, nv, nl, ip, tys =>
    let (tk, r) := toTreeExpr k nv nl (ip + 1) tys
    (.store [] ip t v a tk, r)
  | .call g (as := as) (bs := bs) args k, nv, nl, ip, tys =>
    let (tk, r) := toTreeExpr (k (Tup.levels bs nv)) (nv + bs.length) nl (ip + 1) (recordTypes (levelTypes nv bs) tys)
    (.call [] ip nv g as bs args tk, r)
  | .jnz (.imm b) t e, nv, nl, ip, tys =>
    let (tk, r) := if b then toTreeExpr t nv nl (ip + 1) tys else toTreeExpr e nv nl (ip + 1) tys
    (.skip [] ip tk, r)
  | .jnz (.var x) t e, nv, nl, ip, tys =>
    let (te, nv1, nl1, ip1, tys1) := toTreeExpr e nv (nl + 1) (ip + 1) tys
    let (tt, r) := toTreeExpr t nv1 nl1 ip1 tys1
    (.jnz [] ip x nl tt te, r)
  | .jump (ts := ts) j args, nv, nl, ip, tys => (.jump [] ip j ts args, nv, nl, ip + 1, tys)
  | .ret vs, nv, nl, ip, tys => (.ret [] ip rs vs, nv, nl, ip + 1, tys)
  | .exit g (as := as) args, nv, nl, ip, tys => (.exit [] ip g as args, nv, nl, ip + 1, tys)
  | .hlt, nv, nl, ip, tys => (.stop ip, nv, nl, ip + 1, tys)
  | .group (sig := sig) bodies k, nv, nl, ip, tys =>
    let ls := Tup.levels sig nl
    let (tk, nv1, nl1, ip1, tys1) := toTreeExpr (k ls) nv (nl + sig.length) ip tys
    let (bs, nv2, nl2, ip2, tys2) := toTreeBlocks (bodies ls) nl nv1 nl1 ip1 tys1
    (.group [] bs tk, nv2, nl2, ip2, tys2)

def toTreeBlocks {rs : List Ty} :
    {sig : List (List Ty)} → Blocks VNat LNat rs sig →
    Nat → Nat → Nat → Nat → Trie Ty → TreeBlocks × Nat × Nat × Nat × Trie Ty
  | _, .nil, _, nv, nl, ip, tys => (.nil, nv, nl, ip, tys)
  | _, .cons (ts := ts) b bs, lid, nv, nl, ip, tys =>
    let ps := levelTypes nv ts
    let (tb, nv1, nl1, ip1, tys2) := toTreeExpr (b (Tup.levels ts nv)) (nv + ts.length) nl ip (recordTypes ps tys)
    let (rest, r) := toTreeBlocks bs (lid + 1) nv1 nl1 ip1 tys2
    (.cons lid ps tb rest, r)
end

/-- Convert `f : Fn` to `Tree`, returning `(tree, fnParams, nv, nl, nip, varTypes)`. -/
def Tree.ofFn (f : Fn) : Tree × List (Nat × Ty) × Nat × Nat × Nat × Trie Ty :=
  let ps := levelTypes 0 f.as
  let (t, nv, nl, nip, tys) := toTreeExpr (f.body VNat LNat (Tup.levels f.as 0)) f.as.length 0 0 (recordTypes ps .empty)
  (t, ps, nv, nl, nip, tys)

/-! ## Address-Arithmetic Elision (`[base + idx*scale + disp]`, Stage 1b, untrusted) -/

structure ElideCand where
  x : Nat
  ip : Nat
  opVars : List Nat
  df : DefFact

structure ElideScan where
  cands : List ElideCand := []
  addrUses : Trie (List Ty) := .empty
  badVars : Trie Bool := .empty

def markBad (xs : List Nat) (st : ElideScan) : ElideScan :=
  { st with badVars := xs.foldl (fun b x => b.insert x true) st.badVars }

def addAddrUse (t : Ty) (a : Arg VNat i64) (st : ElideScan) : ElideScan :=
  match a with
  | .var x => { st with addrUses := st.addrUses.insert x (t :: st.addrUses.getD x []) }
  | .imm _ => st

mutual
def scanElideTree (defs : Trie DefFact) (st : ElideScan) : Tree → ElideScan
  | .let_ _ ip nv0 ts op k =>
    let df? := if ts == [i64] then
      match recordDef defs op.code op.args with
      | some df => if df.isAddr then some df else none
      | none => none
    else none
    let st1 := match df? with
      | some df => { st with cands := ⟨nv0, ip, opVarIds op, df⟩ :: st.cands }
      | none => markBad (opVarIds op) st
    let defs1 := match df? with
      | some df => defs.insert nv0 df
      | none => defs
    scanElideTree defs1 st1 k
  | .load _ _ _ t a k => scanElideTree defs (addAddrUse t a st) k
  | .store _ _ t v a k => scanElideTree defs (addAddrUse t a (markBad (argVarIds v) st)) k
  | .call _ _ _ _ _ _ args k => scanElideTree defs (markBad (tupVarIds args) st) k
  | .jnz _ _ c _ t e => scanElideTree defs (scanElideTree defs (markBad [c] st) t) e
  | .skip _ _ k => scanElideTree defs st k
  | .jump _ _ _ _ args => markBad (tupVarIds args) st
  | .ret _ _ _ vs => markBad (tupVarIds vs) st
  | .exit _ _ _ _ args => markBad (tupVarIds args) st
  | .stop _ => st
  | .group _ bs k => scanElideTree defs (scanElideBlocks defs st bs) k

def scanElideBlocks (defs : Trie DefFact) (st : ElideScan) : TreeBlocks → ElideScan
  | .nil => st
  | .cons _ _ b bs => scanElideBlocks defs (scanElideTree defs st b) bs
end

def defFactRoots : DefFact → List Nat
  | .imm64 _ => []
  | .addImm64 b _ => [b]
  | .scaleOff i _ _ => [i]
  | .addrSum b i _ _ => if Nat.beq b i then [b] else [b, i]
  | _ => []

def supportsDefFact (I : Isa) (df : DefFact) (ts : List Ty) : Bool :=
  match df with
  | .addImm64 _ disp => ts.all (I.supportsAddrDisp · disp)
  | .addrSum _ _ sh disp =>
    match AddrScale.ofShift? sh with
    | some sc => ts.all (I.supportsAddrIdx · sc disp)
    | none => false
  | _ => false

mutual
def collectElideTree (eb : Trie (List Nat)) (eip : Trie Bool) :
    Tree → Trie (List Nat) → Tree × Trie (List Nat)
  | .let_ lv ip nv0 ts op k, deps =>
    let (k', deps') := collectElideTree eb eip k deps
    (if eip.getD ip false then .skip lv ip k' else .let_ lv ip nv0 ts op k', deps')
  | .load lv ip x t (.var a) k, deps =>
    let (k', deps') := collectElideTree eb eip k deps
    let deps'' := match eb.find? a with | some ds => deps'.insert ip ds | none => deps'
    (.load lv ip x t (.var a) k', deps'')
  | .load lv ip x t a k, deps =>
    let (k', deps') := collectElideTree eb eip k deps
    (.load lv ip x t a k', deps')
  | .store lv ip t v (.var a) k, deps =>
    let (k', deps') := collectElideTree eb eip k deps
    let deps'' := match eb.find? a with | some ds => deps'.insert ip ds | none => deps'
    (.store lv ip t v (.var a) k', deps'')
  | .store lv ip t v a k, deps =>
    let (k', deps') := collectElideTree eb eip k deps
    (.store lv ip t v a k', deps')
  | .call lv ip nv0 g as bs args k, deps =>
    let (k', deps') := collectElideTree eb eip k deps
    (.call lv ip nv0 g as bs args k', deps')
  | .jnz lv ip c l t e, deps =>
    let (t', deps1) := collectElideTree eb eip t deps
    let (e', deps2) := collectElideTree eb eip e deps1
    (.jnz lv ip c l t' e', deps2)
  | .skip lv ip k, deps =>
    let (k', deps') := collectElideTree eb eip k deps
    (.skip lv ip k', deps')
  | .group lv bs k, deps =>
    let (bs', deps1) := collectElideBlocks eb eip bs deps
    let (k', deps2) := collectElideTree eb eip k deps1
    (.group lv bs' k', deps2)
  | t, deps => (t, deps)

def collectElideBlocks (eb : Trie (List Nat)) (eip : Trie Bool) :
    TreeBlocks → Trie (List Nat) → TreeBlocks × Trie (List Nat)
  | .nil, deps => (.nil, deps)
  | .cons l ps b bs, deps =>
    let (b', deps1) := collectElideTree eb eip b deps
    let (bs', deps2) := collectElideBlocks eb eip bs deps1
    (.cons l ps b' bs', deps2)
end

/-- Elide address-only `add64`/`sub64`/`shl64` chains whose uses are all valid `[base + disp]` or
SIB `[base + idx*scale + disp]` load/store addresses per `I.supportsAddrDisp`/`I.supportsAddrIdx`,
returning `(rewrittenTree, elideIps, addrDepsByMemIp)`. -/
def elideAddrTreeDeps (I : Isa) (t : Tree) : Tree × Trie Bool × Trie (List Nat) :=
  let st := scanElideTree .empty {} t
  let (_, _, eb, eip) := st.cands.foldl
    (fun (bad, used, eb, eip) c =>
      let ts := st.addrUses.getD c.x []
      let okUses := if ts.isEmpty then used.getD c.x false else supportsDefFact I c.df ts
      if !bad.getD c.x false && okUses then
        let roots := defFactRoots c.df
        let bad' := roots.foldl (fun b r => b.insert r true) bad
        let used' := c.opVars.foldl (fun u v =>
          if natMem v roots then u else u.insert v true) used
        (bad', used', eb.insert c.x roots, eip.insert c.ip true)
      else
        let bad' := c.opVars.foldl (fun b v => b.insert v true) bad
        (bad', used, eb, eip))
    (st.badVars, (.empty : Trie Bool), (.empty : Trie (List Nat)), (.empty : Trie Bool))
  let (t', deps) := collectElideTree eb eip t .empty
  (t', eip, deps)

/-- Backward-compatible wrapper returning `(rewrittenTree, elideIps)`. -/
def elideAddrTree (I : Isa) (t : Tree) : Tree × Trie Bool :=
  let (t', eip, _) := elideAddrTreeDeps I t
  (t', eip)

/-! ## Compare/Test/Memory-Operand Elision (`test`/`cmpb`/`testl [mem]`, untrusted) -/

inductive CmpElideOp where
  | andVarVar (ip w x y : Nat)
  | andVarImm (ip w x : Nat)
  | sext (ip m n x : Nat)
  | zext (ip m n x : Nat)

def bumpUses (xs : List Nat) (cnt : Trie Nat) : Trie Nat :=
  xs.foldl (fun c x => c.insert x (c.getD x 0 + 1)) cnt

mutual
def countRawUses (addrDeps : Trie (List Nat)) : Tree → Trie Nat → Trie Nat
  | .let_ _ _ _ _ op k, cnt =>
    countRawUses addrDeps k (bumpUses (op.vars.map (·.2)) cnt)
  | .load _ ip _ _ a k, cnt =>
    countRawUses addrDeps k (bumpUses (addrDeps.getD ip (argVarIds a)) cnt)
  | .store _ ip _ v a k, cnt =>
    let aUses := addrDeps.getD ip (argVarIds a)
    countRawUses addrDeps k (bumpUses (argVarIds v ++ aUses) cnt)
  | .call _ _ _ _ _ _ args k, cnt =>
    countRawUses addrDeps k (bumpUses ((tupVars args).map (·.2)) cnt)
  | .jnz _ _ c _ t e, cnt =>
    countRawUses addrDeps e (countRawUses addrDeps t (bumpUses [c] cnt))
  | .skip _ _ k, cnt => countRawUses addrDeps k cnt
  | .jump _ _ _ _ args, cnt => bumpUses ((tupVars args).map (·.2)) cnt
  | .ret _ _ _ vs, cnt => bumpUses ((tupVars vs).map (·.2)) cnt
  | .exit _ _ _ _ args, cnt => bumpUses ((tupVars args).map (·.2)) cnt
  | .stop _, cnt => cnt
  | .group _ bs k, cnt => countRawUses addrDeps k (countRawUsesB addrDeps bs cnt)

def countRawUsesB (addrDeps : Trie (List Nat)) : TreeBlocks → Trie Nat → Trie Nat
  | .nil, cnt => cnt
  | .cons _ _ b bs, cnt => countRawUsesB addrDeps bs (countRawUses addrDeps b cnt)
end

def matchCmpFuse (I : Isa) (availLoad : Trie (Nat × Nat × List Nat))
    (availOp : Trie CmpElideOp) {ts : List Ty} (op : Op VNat ts) :
    Option (List Nat × List Nat) :=
  let { sig := _, code, args } := op
  match code, args with
  | .cmp co (.bits n) .bool _, (a, b, ()) =>
    if !(Nat.ble n 64 && I.frame.bitWidths.contains n) then none
    else
      let tryTest (t : Nat) : Option (List Nat × List Nat) :=
        if !I.supportsTestFuse then none
        else match availOp.find? t with
          | some (.andVarImm ipA w x) =>
            if !Nat.beq w n then none
            else match availLoad.find? x with
              | some (ipL, lw, ldeps) =>
                if Nat.beq lw n && I.supportsTestMem (.bits n) then
                  some ([ipA, ipL], dedup ldeps)
                else some ([ipA], [x])
              | none => some ([ipA], [x])
          | some (.andVarVar ipA w x y) =>
            if !Nat.beq w n then none
            else
              let xMem := match availLoad.find? x with
                | some (ipL, lw, ldeps) =>
                  if Nat.beq lw n && I.supportsTestMem (.bits n) then
                    some ([ipA, ipL], dedup (ldeps ++ [y]))
                  else none
                | none => none
              let yMem := match availLoad.find? y with
                | some (ipL, lw, ldeps) =>
                  if Nat.beq lw n && I.supportsTestMem (.bits n) then
                    some ([ipA, ipL], dedup (ldeps ++ [x]))
                  else none
                | none => none
              xMem <|> yMem <|> some ([ipA], dedup [x, y])
          | _ => none
      let tryExt (co' : CmpOp) (t : Nat) (c : BitVec n) : Option (List Nat × List Nat) :=
        match availOp.find? t with
        | some (.sext ipE m n' x) =>
          if !(Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && I.frame.bitWidths.contains m &&
               cmpIsSignedOrEq co' && (c.truncate m).signExtend n == c) then none
          else match availLoad.find? x with
            | some (ipL, lw, ldeps) =>
              if Nat.beq lw m && I.supportsCmpMem (.bits m) then
                some ([ipE, ipL], dedup ldeps)
              else if I.supportsTestFuse then some ([ipE], [x]) else none
            | none => if I.supportsTestFuse then some ([ipE], [x]) else none
        | some (.zext ipE m n' x) =>
          if !(Nat.beq n' n && Nat.blt 0 m && Nat.blt m n && I.frame.bitWidths.contains m &&
               cmpIsUnsignedOrEq co' && (c.truncate m).zeroExtend n == c) then none
          else match availLoad.find? x with
            | some (ipL, lw, ldeps) =>
              if Nat.beq lw m && I.supportsCmpMem (.bits m) then
                some ([ipE, ipL], dedup ldeps)
              else if I.supportsTestFuse then some ([ipE], [x]) else none
            | none => if I.supportsTestFuse then some ([ipE], [x]) else none
        | _ => none
      let tryMem (x : Nat) (other : Arg VNat (.bits n)) : Option (List Nat × List Nat) :=
        if !I.supportsCmpMem (.bits n) then none
        else match availLoad.find? x with
          | some (ipL, lw, ldeps) =>
            if Nat.beq lw n then some ([ipL], dedup (ldeps ++ argVarIds other)) else none
          | none => none
      let tFuse :=
        if co == .eq || co == .ne then
          match a, b with
          | .var t, .imm c => if c == 0#n then tryTest t else none
          | .imm c, .var t => if c == 0#n then tryTest t else none
          | _, _ => none
        else none
      let eFuse := match a, b with
        | .var t, .imm c => tryExt co t c
        | .imm c, .var t => tryExt co.swap t c
        | _, _ => none
      let mFuse :=
        (match a with | .var x => tryMem x b | _ => none) <|>
        (match b with | .var y => tryMem y a | _ => none)
      tFuse <|> eFuse <|> mFuse
  | _, _ => none

def recordCmpCand (I : Isa) (ip : Nat) {ts : List Ty} (op : Op VNat ts) :
    Option CmpElideOp :=
  let { sig := _, code, args } := op
  match code, args with
  | .and (.bits n), (a, b, ()) =>
    if !(I.supportsTestFuse && Nat.ble n 64 && I.frame.bitWidths.contains n) then none
    else match a, b with
      | .var x, .var y => some (.andVarVar ip n x y)
      | .var x, .imm _ | .imm _, .var x => some (.andVarImm ip n x)
      | _, _ => none
  | .sext m n, (.var x, ()) =>
    if Nat.blt 0 m && Nat.blt m n && Nat.ble n 64 && I.frame.bitWidths.contains m &&
       (I.supportsTestFuse || I.supportsCmpMem (.bits m)) then
      some (.sext ip m n x)
    else none
  | .zext m n, (.var x, ()) =>
    if Nat.blt 0 m && Nat.blt m n && Nat.ble n 64 && I.frame.bitWidths.contains m &&
       (I.supportsTestFuse || I.supportsCmpMem (.bits m)) then
      some (.zext ip m n x)
    else none
  | _, _ => none

mutual
def scanCmpElide (I : Isa) (useCnt : Trie Nat) (addrDeps : Trie (List Nat))
    (availLoad : Trie (Nat × Nat × List Nat)) (availOp : Trie CmpElideOp) :
    Tree → Trie Bool × Trie (List Nat) → Trie Bool × Trie (List Nat)
  | .let_ _ ip nv0 _ op k, (eip, deps) =>
    match matchCmpFuse I availLoad availOp op with
    | some (ips, newDeps) =>
      let eip' := ips.foldl (fun e i => e.insert i true) eip
      let deps' := deps.insert ip newDeps
      scanCmpElide I useCnt addrDeps availLoad availOp k (eip', deps')
    | none =>
      let availOp' :=
        if Nat.beq (useCnt.getD nv0 0) 1 then
          match recordCmpCand I ip op with
          | some cand => availOp.insert nv0 cand
          | none => availOp
        else availOp
      scanCmpElide I useCnt addrDeps availLoad availOp' k (eip, deps)
  | .load _ ip x t a k, acc =>
    let availLoad' :=
      if Nat.beq (useCnt.getD x 0) 1 then
        match t with
        | .bits w =>
          if I.supportsCmpMem (.bits w) || I.supportsTestMem (.bits w) then
            availLoad.insert x (ip, w, addrDeps.getD ip (argVarIds a))
          else availLoad
        | _ => availLoad
      else availLoad
    scanCmpElide I useCnt addrDeps availLoad' availOp k acc
  | .store _ _ _ _ _ k, acc =>
    scanCmpElide I useCnt addrDeps .empty availOp k acc
  | .call _ _ _ _ _ _ _ k, acc =>
    scanCmpElide I useCnt addrDeps .empty availOp k acc
  | .jnz _ _ _ _ t e, acc =>
    let acc1 := scanCmpElide I useCnt addrDeps availLoad availOp t acc
    scanCmpElide I useCnt addrDeps availLoad availOp e acc1
  | .skip _ _ k, acc =>
    scanCmpElide I useCnt addrDeps availLoad availOp k acc
  | .group _ bs k, acc =>
    let acc1 := scanCmpElideB I useCnt addrDeps bs acc
    scanCmpElide I useCnt addrDeps availLoad availOp k acc1
  | _, acc => acc

def scanCmpElideB (I : Isa) (useCnt : Trie Nat) (addrDeps : Trie (List Nat)) :
    TreeBlocks → Trie Bool × Trie (List Nat) → Trie Bool × Trie (List Nat)
  | .nil, acc => acc
  | .cons _ _ b bs, acc =>
    let acc1 := scanCmpElide I useCnt addrDeps .empty .empty b acc
    scanCmpElideB I useCnt addrDeps bs acc1
end

mutual
def rewriteCmpElide (eip : Trie Bool) : Tree → Tree
  | .let_ lv ip nv0 ts op k =>
    let k' := rewriteCmpElide eip k
    if eip.getD ip false then .skip lv ip k' else .let_ lv ip nv0 ts op k'
  | .load lv ip x t a k =>
    let k' := rewriteCmpElide eip k
    if eip.getD ip false then .skip lv ip k' else .load lv ip x t a k'
  | .store lv ip t v a k => .store lv ip t v a (rewriteCmpElide eip k)
  | .call lv ip nv0 g as bs args k => .call lv ip nv0 g as bs args (rewriteCmpElide eip k)
  | .jnz lv ip c l t e => .jnz lv ip c l (rewriteCmpElide eip t) (rewriteCmpElide eip e)
  | .skip lv ip k => .skip lv ip (rewriteCmpElide eip k)
  | .group lv bs k => .group lv (rewriteCmpElideB eip bs) (rewriteCmpElide eip k)
  | t => t

def rewriteCmpElideB (eip : Trie Bool) : TreeBlocks → TreeBlocks
  | .nil => .nil
  | .cons l ps b bs => .cons l ps (rewriteCmpElide eip b) (rewriteCmpElideB eip bs)
end

/-- Elide single-use `and` (into `test`), `sext`/`zext` (into narrow `cmp`), and straight-line
single-use `load` (into memory-operand `cmp`/`test`) when supported by `I`. -/
def elideCmpTreeDeps (I : Isa) (t : Tree) (elideIps : Trie Bool)
    (addrDeps : Trie (List Nat)) : Tree × Trie Bool × Trie (List Nat) :=
  let enabled := I.supportsTestFuse ||
    I.frame.bitWidths.any fun w => I.supportsCmpMem (.bits w) || I.supportsTestMem (.bits w)
  if !enabled then (t, elideIps, addrDeps)
  else
    let useCnt := countRawUses addrDeps t .empty
    let (newEip, newDeps) := scanCmpElide I useCnt addrDeps .empty .empty t (elideIps, addrDeps)
    (rewriteCmpElide newEip t, newEip, newDeps)

/-! ## Memory Read-Modify-Write Elision (`load; alu; store -> rmwMem`, untrusted) -/

structure RmwCand where
  ipL : Nat
  ipA : Nat
  w : Nat
  x : Nat
  aL : Arg VNat i64
  ldeps : List Nat
  rhsVars : List Nat

mutual
def scanRmwElide (I : Isa) (useCnt : Trie Nat) (addrDeps : Trie (List Nat))
    (defs : Trie DefFact) (elidedVars : Trie Bool)
    (availLoad : Trie (Nat × Nat × Arg VNat i64 × List Nat)) (availRmw : Trie RmwCand) :
    Tree → Trie Bool × Trie (List Nat) → Trie Bool × Trie (List Nat)
  | .let_ _ ip nv0 ts op k, acc =>
    let { sig := _, code, args } := op
    let df? := recordDef defs code args
    let defs' := match df? with | some df => defs.insert nv0 df | none => defs
    if acc.1.getD ip false then
      scanRmwElide I useCnt addrDeps defs' (elidedVars.insert nv0 true) availLoad availRmw k acc
    else
      let r0? := I.frame.allocatable.head?
      let rmwOk (w : Nat) (rop : RmwOp) (isVar : Bool) : Bool :=
        match (if isVar then r0?.map .gpr else some (.imm 0#w)) with
        | some pb => (I.gpr.rmwMem w (rop.toOpCode w) (.baseDisp I.frame.sp 0) pb).isSome
        | none => false
      let cand? : Option RmwCand :=
        if !(Nat.beq (useCnt.getD nv0 0) 1) then none
        else match ts, df? with
          | [.bits w], some df =>
            if !(Nat.ble w 64 && I.frame.bitWidths.contains w) then none
            else (rmwFact w df).bind fun (rop, a1, rhs) =>
              let trySide (x : Nat) (rhsVars : List Nat) : Option RmwCand :=
                match availLoad.find? x with
                | some (ipL, lw, aL, ldeps) =>
                  if Nat.beq lw w && !(rhsVars.any (elidedVars.getD · false)) &&
                     rmwOk w rop !rhsVars.isEmpty then
                    some ⟨ipL, ip, w, x, aL, ldeps, rhsVars⟩
                  else none
                | none => none
              let rv1 := match rhs with | .var z => [z] | .imm _ => []
              trySide a1 rv1 <|>
                if rop.isComm then
                  match rhs with | .var a2 => trySide a2 [a1] | .imm _ => none
                else none
          | _, _ => none
      let availRmw' := match cand? with
        | some c => availRmw.insert nv0 c
        | none => availRmw
      scanRmwElide I useCnt addrDeps defs' elidedVars availLoad availRmw' k acc
  | .load _ ip x t a k, acc =>
    if acc.1.getD ip false then
      scanRmwElide I useCnt addrDeps defs (elidedVars.insert x true) availLoad availRmw k acc
    else
      let availLoad' :=
        if Nat.beq (useCnt.getD x 0) 1 then
          match t with
          | .bits w =>
            if Nat.ble w 64 && I.frame.bitWidths.contains w then
              availLoad.insert x (ip, w, a, addrDeps.getD ip (argVarIds a))
            else availLoad
          | _ => availLoad
        else availLoad
      scanRmwElide I useCnt addrDeps defs elidedVars availLoad' availRmw k acc
  | .store _ ip t v a k, (eip, rdeps) =>
    let (eip', rdeps') := match t, v with
      | .bits wS, .var y =>
        match availRmw.find? y with
        | some c =>
          let sameAddr := c.aL == a ||
            (match c.aL, a with
             | .var pL, .var pS =>
               elidedVars.getD pL false && elidedVars.getD pS false &&
                 defs.find? pL == defs.find? pS && (defs.find? pL).isSome
             | _, _ => false)
          if Nat.beq c.w wS && sameAddr then
            let newEip := (eip.insert c.ipL true).insert c.ipA true
            let newDeps := dedup (c.ldeps ++ c.rhsVars ++ addrDeps.getD ip (argVarIds a))
            (newEip, rdeps.insert ip newDeps)
          else (eip, rdeps)
        | none => (eip, rdeps)
      | _, _ => (eip, rdeps)
    scanRmwElide I useCnt addrDeps defs elidedVars .empty .empty k (eip', rdeps')
  | .call _ _ _ _ _ _ _ k, acc =>
    scanRmwElide I useCnt addrDeps defs elidedVars .empty .empty k acc
  | .jnz _ _ _ _ t e, acc =>
    let acc1 := scanRmwElide I useCnt addrDeps defs elidedVars .empty .empty t acc
    scanRmwElide I useCnt addrDeps defs elidedVars .empty .empty e acc1
  | .skip _ _ k, acc =>
    scanRmwElide I useCnt addrDeps defs elidedVars availLoad availRmw k acc
  | .group _ bs k, acc =>
    let acc1 := scanRmwElideB I useCnt addrDeps defs elidedVars bs acc
    scanRmwElide I useCnt addrDeps defs elidedVars .empty .empty k acc1
  | _, acc => acc

def scanRmwElideB (I : Isa) (useCnt : Trie Nat) (addrDeps : Trie (List Nat))
    (defs : Trie DefFact) (elidedVars : Trie Bool) :
    TreeBlocks → Trie Bool × Trie (List Nat) → Trie Bool × Trie (List Nat)
  | .nil, acc => acc
  | .cons _ _ b bs, acc =>
    let acc1 := scanRmwElide I useCnt addrDeps defs elidedVars .empty .empty b acc
    scanRmwElideB I useCnt addrDeps defs elidedVars bs acc1
end

/-- Elide straight-line `load; alu; store` at the same address when `I.gpr.rmwMem` handles it. -/
def elideRmwTreeDeps (I : Isa) (t : Tree) (elideIps : Trie Bool)
    (addrDeps : Trie (List Nat)) : Tree × Trie Bool × Trie (List Nat) :=
  let enabled := I.frame.bitWidths.any fun w =>
    (I.gpr.rmwMem w (.add (.bits w)) (.baseDisp I.frame.sp 0) (.imm 0#w)).isSome
  if !enabled then (t, elideIps, .empty)
  else
    let useCnt := countRawUses addrDeps t .empty
    let (newEip, rmwDeps) :=
      scanRmwElide I useCnt addrDeps .empty .empty .empty .empty t (elideIps, .empty)
    (rewriteCmpElide newEip t, newEip, rmwDeps)

/-! ## Join-Point Liveness Fixpoint, `acrossCalls`, and `loopBlocks` -/

mutual
def Tree.blocks : Tree → List (Nat × List (Nat × Ty) × Tree)
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .call _ _ _ _ _ _ _ k | .skip _ _ k => k.blocks
  | .jnz _ _ _ _ t e => t.blocks ++ e.blocks
  | .group _ bs k => bs.blocks ++ k.blocks
  | .jump .. | .ret .. | .exit .. | .stop _ => []

def TreeBlocks.blocks : TreeBlocks → List (Nat × List (Nat × Ty) × Tree)
  | .nil => []
  | .cons l ps b bs => (l, ps, b) :: b.blocks ++ bs.blocks
end

mutual
def allJumps : Tree → List Nat
  | .jump _ _ j _ _ => [j]
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .call _ _ _ _ _ _ _ k | .skip _ _ k => allJumps k
  | .jnz _ _ _ _ t e => union (allJumps t) (allJumps e)
  | .group _ bs k => union (allJumpsB bs) (allJumps k)
  | .ret .. | .exit .. | .stop _ => []

def allJumpsB : TreeBlocks → List Nat
  | .nil => []
  | .cons _ _ b bs => union (allJumps b) (allJumpsB bs)
end

mutual
def fillLive (lTrie : Trie (List Nat)) (addrDeps : Trie (List Nat) := .empty)
    (rmwDeps : Trie (List Nat) := .empty) : Tree → List Nat × Tree
  | .let_ _ ip nv0 ts op k =>
    let (klv, k) := fillLive lTrie addrDeps rmwDeps k
    let ops := addrDeps.getD ip (opVarIds op)
    let lv := union (eraseMany ((List.range ts.length).map (nv0 + ·)) klv) ops
    (lv, .let_ lv ip nv0 ts op k)
  | .load _ ip x t a k =>
    let (klv, k) := fillLive lTrie addrDeps rmwDeps k
    let aUses := addrDeps.getD ip (argVarIds a)
    let lv := union (erase x klv) aUses
    (lv, .load lv ip x t a k)
  | .store _ ip t v a k =>
    let (klv, k) := fillLive lTrie addrDeps rmwDeps k
    let lv := union klv (storeVarIds addrDeps rmwDeps ip v a)
    (lv, .store lv ip t v a k)
  | .call _ ip nv0 g as bs args k =>
    let (klv, k) := fillLive lTrie addrDeps rmwDeps k
    let lv := union (eraseMany ((List.range bs.length).map (nv0 + ·)) klv) (tupVarIds args)
    (lv, .call lv ip nv0 g as bs args k)
  | .jnz _ ip c l t e =>
    let (tlv, t) := fillLive lTrie addrDeps rmwDeps t
    let (elv, e) := fillLive lTrie addrDeps rmwDeps e
    let lv := union (union tlv elv) [c]
    (lv, .jnz lv ip c l t e)
  | .skip _ ip k =>
    let (klv, k) := fillLive lTrie addrDeps rmwDeps k
    (klv, .skip klv ip k)
  | .jump _ ip j ts args => let lv := union (tupVarIds args) (lTrie.getD j []); (lv, .jump lv ip j ts args)
  | .ret _ ip rs vs => let lv := tupVarIds vs; (lv, .ret lv ip rs vs)
  | .exit _ ip g as args => let lv := tupVarIds args; (lv, .exit lv ip g as args)
  | .stop ip => ([], .stop ip)
  | .group _ bs k =>
    let (klv, k) := fillLive lTrie addrDeps rmwDeps k
    (klv, .group klv (fillLiveB lTrie addrDeps rmwDeps bs) k)

def fillLiveB (lTrie : Trie (List Nat)) (addrDeps : Trie (List Nat) := .empty)
    (rmwDeps : Trie (List Nat) := .empty) : TreeBlocks → TreeBlocks
  | .nil => .nil
  | .cons l ps b bs =>
    .cons l ps (fillLive lTrie addrDeps rmwDeps b).2 (fillLiveB lTrie addrDeps rmwDeps bs)
end

/-- Live-in variables (excluding own parameters) for every block label, by fixpoint iteration. -/
def liveLabels (bs0 : List (Nat × List (Nat × Ty) × Tree))
    (addrDeps : Trie (List Nat) := .empty) (rmwDeps : Trie (List Nat) := .empty) :
    Trie (List Nat) :=
  let bs := bs0.map fun (l, ps, tb) => (l, ps.map Prod.fst, tb, allJumps tb)
  let rec go : Nat → Bool → Trie (List Nat) → Trie Bool → Trie (List Nat)
    | 0, _, lt, _ => lt
    | fuel + 1, first, lt, prevCh =>
      let (lt', nextCh, ch) := bs.foldl (fun (lt, nch, ch) (l, pvars, tb, js) =>
        if !(first || js.any (fun j => prevCh.getD j false)) then (lt, nch, ch)
        else
          let lv := eraseMany pvars (fillLive lt addrDeps rmwDeps tb).1
          if Nat.beq lv.length (lt.getD l []).length then (lt, nch, ch)
          else (lt.insert l lv, nch.insert l true, true))
        (lt, .empty, false)
      if ch then go fuel false lt' nextCh else lt
  go (8 * bs.length + 8) true .empty .empty

mutual
def acrossCalls : Tree → List Nat
  | .call _ _ nv0 _ _ bs _ k => union (eraseMany ((List.range bs.length).map (nv0 + ·)) k.lv) (acrossCalls k)
  | .let_ _ _ _ _ _ k | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .skip _ _ k => acrossCalls k
  | .jnz _ _ _ _ t e => union (acrossCalls t) (acrossCalls e)
  | .group _ bs k => union (acrossCallsB bs) (acrossCalls k)
  | .jump .. | .ret .. | .exit .. | .stop _ => []

def acrossCallsB : TreeBlocks → List Nat
  | .nil => []
  | .cons _ _ b bs => union (acrossCalls b) (acrossCallsB bs)
end

def loopBlocks (bs : List (Nat × List (Nat × Ty) × Tree)) : Trie Bool :=
  let adj := bs.foldl (fun a (l, _, tb) => a.insert l (allJumps tb)) (.empty : Trie (List Nat))
  let maxFuel := bs.length * bs.length + bs.length + 1
  let canReach (src target : Nat) : Bool :=
    let rec dfs : Nat → List Nat → Trie Unit → Bool
      | 0, _, _ | _, [], _ => false
      | fuel + 1, x :: xs, vis =>
        if Nat.beq x target then true
        else if trieMem vis x then dfs fuel xs vis
        else dfs fuel (adj.getD x [] ++ xs) (vis.insert x ())
    dfs maxFuel (adj.getD src []) .empty
  bs.foldl (fun acc (l, _, _) => if canReach l l then acc.insert l true else acc) .empty

end Live
end LeanQbe.T
