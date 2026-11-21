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

/-! ## Address-Arithmetic Elision (`[base + disp]`, Stage 1a, untrusted) -/

structure ElideScan where
  cands : List (Nat × Nat × Nat × BitVec 64) := []
  addrUses : Trie (List Ty) := .empty
  badVars : Trie Bool := .empty

def markBad (xs : List Nat) (st : ElideScan) : ElideScan :=
  { st with badVars := xs.foldl (fun b x => b.insert x true) st.badVars }

def addAddrUse (t : Ty) (a : Arg VNat i64) (st : ElideScan) : ElideScan :=
  match a with
  | .var x => { st with addrUses := st.addrUses.insert x (t :: st.addrUses.getD x []) }
  | .imm _ => st

mutual
def scanElideTree (st : ElideScan) : Tree → ElideScan
  | .let_ _ ip nv0 ts op k =>
    let st1 := match ts, recordDef op.code op.args with
      | [.bits 64], some (.addImm64 base disp) =>
        { st with cands := (nv0, ip, base, disp) :: st.cands }
      | _, _ => st
    scanElideTree (markBad (opVarIds op) st1) k
  | .load _ _ _ t a k => scanElideTree (addAddrUse t a st) k
  | .store _ _ t v a k => scanElideTree (addAddrUse t a (markBad (argVarIds v) st)) k
  | .call _ _ _ _ _ _ args k => scanElideTree (markBad (tupVarIds args) st) k
  | .jnz _ _ c _ t e => scanElideTree (scanElideTree (markBad [c] st) t) e
  | .skip _ _ k => scanElideTree st k
  | .jump _ _ _ _ args => markBad (tupVarIds args) st
  | .ret _ _ _ vs => markBad (tupVarIds vs) st
  | .exit _ _ _ _ args => markBad (tupVarIds args) st
  | .stop _ => st
  | .group _ bs k => scanElideTree (scanElideBlocks st bs) k

def scanElideBlocks (st : ElideScan) : TreeBlocks → ElideScan
  | .nil => st
  | .cons _ _ b bs => scanElideBlocks (scanElideTree st b) bs
end

mutual
def rewriteElideTree (eb : Trie Nat) (eip : Trie Bool) : Tree → Tree
  | .let_ lv ip nv0 ts op k =>
    let k' := rewriteElideTree eb eip k
    if eip.getD ip false then .skip lv ip k' else .let_ lv ip nv0 ts op k'
  | .load lv ip x t (.var a) k =>
    .load lv ip x t (.var (eb.getD a a)) (rewriteElideTree eb eip k)
  | .load lv ip x t a k => .load lv ip x t a (rewriteElideTree eb eip k)
  | .store lv ip t v (.var a) k =>
    .store lv ip t v (.var (eb.getD a a)) (rewriteElideTree eb eip k)
  | .store lv ip t v a k => .store lv ip t v a (rewriteElideTree eb eip k)
  | .call lv ip nv0 g as bs args k => .call lv ip nv0 g as bs args (rewriteElideTree eb eip k)
  | .jnz lv ip c l t e =>
    .jnz lv ip c l (rewriteElideTree eb eip t) (rewriteElideTree eb eip e)
  | .skip lv ip k => .skip lv ip (rewriteElideTree eb eip k)
  | .group lv bs k => .group lv (rewriteElideBlocks eb eip bs) (rewriteElideTree eb eip k)
  | t => t

def rewriteElideBlocks (eb : Trie Nat) (eip : Trie Bool) : TreeBlocks → TreeBlocks
  | .nil => .nil
  | .cons l ps b bs => .cons l ps (rewriteElideTree eb eip b) (rewriteElideBlocks eb eip bs)
end

/-- Elide address-only `add64`/`sub64` definitions whose uses are all valid `[base + disp]`
load/store addresses per `I.supportsAddrDisp`, rewiring address uses in `Tree` to `base` so
liveness and register allocation keep `base` live instead of the elided def. -/
def elideAddrTree (I : Isa) (t : Tree) : Tree × Trie Bool :=
  let st := scanElideTree {} t
  let (eb, eip) := st.cands.foldl (fun (eb, eip) (x, ip, base, disp) =>
    let ts := st.addrUses.getD x []
    if !st.badVars.getD x false && !ts.isEmpty && ts.all (I.supportsAddrDisp · disp) then
      (eb.insert x base, eip.insert ip true)
    else (eb, eip)) ((.empty : Trie Nat), (.empty : Trie Bool))
  (rewriteElideTree eb eip t, eip)

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
def fillLive (lTrie : Trie (List Nat)) : Tree → List Nat × Tree
  | .let_ _ ip nv0 ts op k =>
    let (klv, k) := fillLive lTrie k
    let lv := union (eraseMany ((List.range ts.length).map (nv0 + ·)) klv) (opVarIds op)
    (lv, .let_ lv ip nv0 ts op k)
  | .load _ ip x t a k =>
    let (klv, k) := fillLive lTrie k
    let lv := union (erase x klv) (argVarIds a)
    (lv, .load lv ip x t a k)
  | .store _ ip t v a k =>
    let (klv, k) := fillLive lTrie k
    let lv := union klv (dedup (argVarIds v ++ argVarIds a))
    (lv, .store lv ip t v a k)
  | .call _ ip nv0 g as bs args k =>
    let (klv, k) := fillLive lTrie k
    let lv := union (eraseMany ((List.range bs.length).map (nv0 + ·)) klv) (tupVarIds args)
    (lv, .call lv ip nv0 g as bs args k)
  | .jnz _ ip c l t e =>
    let (tlv, t) := fillLive lTrie t
    let (elv, e) := fillLive lTrie e
    let lv := union (union tlv elv) [c]
    (lv, .jnz lv ip c l t e)
  | .skip _ ip k => let (klv, k) := fillLive lTrie k; (klv, .skip klv ip k)
  | .jump _ ip j ts args => let lv := union (tupVarIds args) (lTrie.getD j []); (lv, .jump lv ip j ts args)
  | .ret _ ip rs vs => let lv := tupVarIds vs; (lv, .ret lv ip rs vs)
  | .exit _ ip g as args => let lv := tupVarIds args; (lv, .exit lv ip g as args)
  | .stop ip => ([], .stop ip)
  | .group _ bs k =>
    let (klv, k) := fillLive lTrie k
    (klv, .group klv (fillLiveB lTrie bs) k)

def fillLiveB (lTrie : Trie (List Nat)) : TreeBlocks → TreeBlocks
  | .nil => .nil
  | .cons l ps b bs => .cons l ps (fillLive lTrie b).2 (fillLiveB lTrie bs)
end

/-- Live-in variables (excluding own parameters) for every block label, by fixpoint iteration. -/
def liveLabels (bs0 : List (Nat × List (Nat × Ty) × Tree)) : Trie (List Nat) :=
  let bs := bs0.map fun (l, ps, tb) => (l, ps.map Prod.fst, tb, allJumps tb)
  let rec go : Nat → Bool → Trie (List Nat) → Trie Bool → Trie (List Nat)
    | 0, _, lt, _ => lt
    | fuel + 1, first, lt, prevCh =>
      let (lt', nextCh, ch) := bs.foldl (fun (lt, nch, ch) (l, pvars, tb, js) =>
        if !(first || js.any (fun j => prevCh.getD j false)) then (lt, nch, ch)
        else
          let lv := eraseMany pvars (fillLive lt tb).1
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
