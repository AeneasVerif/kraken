module

/-!
# ART v1 checker — pure Lean, designed for kernel reduction (`decide +kernel`)

`checkArt signed aigN aigLen artN artLen : Bool` decides whether the ART v1 trace
proves that the binary AIGER circuit is a (signed/unsigned) multiplier.

Inputs are the raw files, each as ONE little-endian `Nat` literal plus its byte length (elaborates
instantly; decoded in the kernel by divide-and-conquer splitting with GMP `shiftRight`/`land`).

Kernel-reduction design (cf. `Init/Grind/Ring/CommSolver.lean`, `*_k` definitions):
* only structural recursion through the recursors `Nat.rec`/`List.rec`/`Poly.rec`/`Tree.rec`/
  `Bool.rec`/`Option.rec` (no well-founded recursion, no `Array`, no `HashMap`, no `Decidable`
  `if`);
* all arithmetic on `Nat` literals uses kernel-accelerated GMP primitives
  (`Nat.add/sub/mul/mod/pow/land/lor/xor/shiftLeft/shiftRight/beq/ble`);
* monomials are bitsets (`Nat`): bit `sym` set ⇔ symbol in the monomial; product = `lor`,
  `x·x = x` for free, membership = `land` with `2^s`;
* polynomials are lists sorted by DEcreasing monomial value, so all terms that can contain `s`
  (value `≥ 2^s`) form a prefix: SUBST splits that prefix and shares the rest untouched. If nets
  are numbered by elimination rank (eliminated symbol = leading variable) SUBST costs
  O(#terms containing s + products·log) instead of O(|P|);
* maps (bind, rules, HA partners, AIG ANDs) are binary tries keyed by the bits of the key, leaves
  store the full key (so aliasing can only lose entries, which is sound).

Everything here is `noncomputable` (the code generator does not support recursors); the checker
is executed only by the kernel.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace LeanQbe.T.Examples.Arisca

/-! ## Polynomials -/

/-- `cons c m p` is the term `c · Π_{i ∈ m} x_i` followed by `p`. -/
inductive Poly where
  | nil
  | cons (c m : Nat) (p : Poly)

/-- kernel bit test: `testBit m i`. -/
def tb (m i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

/-- `-c mod M`. -/
def negC (M c : Nat) : Nat := Nat.mod (Nat.sub M (Nat.mod c M)) M

/-- Merge two polynomials sorted by decreasing monomial; equal monomials are added mod `M`
and dropped when the sum is `0`. -/
def merge (M : Nat) (p : Poly) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun q => q)
    (fun c₁ m₁ p₁ ih₁ q =>
      Poly.rec (motive := fun _ => Poly)
        (Poly.cons c₁ m₁ p₁)
        (fun c₂ m₂ q₂ ih₂ =>
          Bool.rec
            (Bool.rec (Poly.cons c₂ m₂ ih₂) (Poly.cons c₁ m₁ (ih₁ (Poly.cons c₂ m₂ q₂)))
              (Nat.ble m₂ m₁))
            (Bool.rec (Poly.cons (Nat.mod (Nat.add c₁ c₂) M) m₁ (ih₁ q₂)) (ih₁ q₂)
              (Nat.beq (Nat.mod (Nat.add c₁ c₂) M) 0))
            (Nat.beq m₁ m₂))
        q)
    p

/-- single term `c·m` (reduced mod `M`, `nil` when `0`). -/
def single (M c m : Nat) : Poly :=
  Bool.rec (Poly.cons (Nat.mod c M) m Poly.nil) Poly.nil (Nat.beq (Nat.mod c M) 0)

/-- `k · p` (mod `M`, zero terms dropped; order preserved). -/
def scaleP (M k : Nat) (p : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.nil
    (fun c m _ ih => Bool.rec (Poly.cons (Nat.mod (Nat.mul k c) M) m ih) ih
      (Nat.beq (Nat.mod (Nat.mul k c) M) 0)) p

/-- balanced merging: one round merges neighbours. -/
def pairs (M : Nat) (ps : List Poly) : Option Poly → List Poly :=
  List.rec (motive := fun _ => Option Poly → List Poly)
    (fun pend => Option.rec [] (fun p => [p]) pend)
    (fun a _ ih pend => Option.rec (ih (some a)) (fun p => merge M p a :: ih none) pend)
    ps

def foldM (M : Nat) (ps : List Poly) : Poly :=
  List.rec (motive := fun _ => Poly) Poly.nil (fun a _ ih => merge M a ih) ps

def sumGo (M : Nat) (fuel : Nat) : List Poly → Poly :=
  Nat.rec (motive := fun _ => List Poly → Poly) (fun ps => foldM M ps)
    (fun _ ih ps =>
      List.rec (motive := fun _ => Poly) Poly.nil
        (fun a t _ =>
          List.rec (motive := fun _ => Poly) a (fun _ _ _ => ih (pairs M ps none)) t)
        ps)
    fuel

/-- sum of a list of sorted polynomials (balanced merge tree). -/
def sumB (M : Nat) (ps : List Poly) : Poly := sumGo M 64 ps

/-- prepend the products `(c·c') · (m ∪ m')`, `(c',m') ∈ R`, as singleton polynomials;
zero coefficients and vanishing monomials (`van`) are dropped. -/
def mulTerm (M : Nat) (van : Nat → Bool) (c m : Nat) (R : Poly) (acc : List Poly) : List Poly :=
  Poly.rec (motive := fun _ => List Poly) acc
    (fun c' m' _ ih =>
      Bool.rec
        (Bool.rec (Poly.cons (Nat.mod (Nat.mul c c') M) (Nat.lor m m') Poly.nil :: ih) ih
          (van (Nat.lor m m')))
        ih (Nat.beq (Nat.mod (Nat.mul c c') M) 0))
    R

def mulTerms (M : Nat) (van : Nat → Bool) (W R : Poly) : List Poly :=
  Poly.rec (motive := fun _ => List Poly) [] (fun c m _ ih => mulTerm M van c m R ih) W

def noVan (_ : Nat) : Bool := false

/-- `p · q` (no vanishing-pair reduction). -/
def mulP (M : Nat) (p q : Poly) : Poly := sumB M (mulTerms M noVan p q)

/-- drop vanishing monomials. -/
def normP (van : Nat → Bool) (p : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.nil
    (fun c m _ ih => Bool.rec (Poly.cons c m ih) ih (van m)) p

/-- the terms containing the symbol with bit `bs = 2^s`, with that symbol removed. Only the prefix
of terms with monomial `≥ bs` is scanned (decreasing order). -/
def collectS (bs : Nat) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.nil
    (fun c m _ ih =>
      Bool.rec Poly.nil (Bool.rec (Poly.cons c (Nat.xor m bs) ih) ih (Nat.beq (Nat.land m bs) 0))
        (Nat.ble bs m))

/-- the terms not containing the symbol `bs = 2^s`; the suffix `< bs` is shared. -/
def filterS (bs : Nat) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.nil
    (fun c m p ih =>
      Bool.rec (Poly.cons c m p) (Bool.rec ih (Poly.cons c m ih) (Nat.beq (Nat.land m bs) 0))
        (Nat.ble bs m))

/-- `P[s := R]`, new product terms filtered by `van`. -/
def substP (M : Nat) (van : Nat → Bool) (s : Nat) (R P : Poly) : Poly :=
  merge M (sumB M (mulTerms M van (collectS (Nat.pow 2 s) P) R)) (filterS (Nat.pow 2 s) P)

/-- `1 - R` -/
def oneSub (M : Nat) (R : Poly) : Poly := merge M (scaleP M (Nat.sub M 1) R) (single M 1 0)

/-- `x_s` with `x = sym(2n)` if positive, `1 - x` if negated. -/
def litP (M : Nat) (neg : Bool) (s : Nat) : Poly :=
  Bool.rec (single M 1 (Nat.pow 2 s)) (oneSub M (single M 1 (Nat.pow 2 s))) neg

def isNil (p : Poly) : Bool := Poly.rec true (fun _ _ _ _ => false) p

/-- OR of all monomials -/
def orMonos (p : Poly) : Nat := Poly.rec 0 (fun _ m _ ih => Nat.lor m ih) p

/-- all monomials ⊆ `S` -/
def subAll (S : Nat) (p : Poly) : Bool :=
  Poly.rec true (fun _ m _ ih => Bool.rec false ih (Nat.beq (Nat.land m S) m)) p

/-- `Σ c·[m ⊆ TS] mod M`: evaluation at the assignment `i ↦ testBit TS i`. -/
def evalK (M TS : Nat) (p : Poly) : Nat :=
  Poly.rec (motive := fun _ => Nat) 0
    (fun c m _ ih => Nat.mod (Nat.add (Bool.rec 0 c (Nat.beq (Nat.land m TS) m)) ih) M) p

/-! ## Binary tries -/

inductive Tree (α : Type) where
  | empty
  | tip (k : Nat) (v : α)
  | br (l r : Tree α)

def Tree.getP {α : Type} (k : Nat) (d : Nat) : Nat → Tree α → Option α :=
  Nat.rec (motive := fun _ => Nat → Tree α → Option α)
    (fun _ t => Tree.rec (motive := fun _ => Option α) none
      (fun k' v => Bool.rec none (some v) (Nat.beq k k')) (fun _ _ _ _ => none) t)
    (fun _ ih p t => Tree.rec (motive := fun _ => Option α) none (fun _ _ => none)
      (fun l r _ _ => Bool.rec (ih (Nat.shiftRight p 1) r) (ih (Nat.shiftRight p 1) l)
        (Nat.beq (Nat.land p 1) 0)) t)
    d

/-- lookup of key `k` in a trie of depth `d`. -/
def Tree.get {α : Type} (d k : Nat) (t : Tree α) : Option α := Tree.getP k d k t

def Tree.setP {α : Type} (k : Nat) (v : α) (d : Nat) : Nat → Tree α → Tree α :=
  Nat.rec (motive := fun _ => Nat → Tree α → Tree α)
    (fun _ _ => Tree.tip k v)
    (fun _ ih p t =>
      Tree.rec (motive := fun _ => Tree α)
        (Bool.rec (Tree.br Tree.empty (ih (Nat.shiftRight p 1) Tree.empty))
          (Tree.br (ih (Nat.shiftRight p 1) Tree.empty) Tree.empty) (Nat.beq (Nat.land p 1) 0))
        (fun _ _ => Bool.rec (Tree.br Tree.empty (ih (Nat.shiftRight p 1) Tree.empty))
          (Tree.br (ih (Nat.shiftRight p 1) Tree.empty) Tree.empty) (Nat.beq (Nat.land p 1) 0))
        (fun l r _ _ => Bool.rec (Tree.br l (ih (Nat.shiftRight p 1) r))
          (Tree.br (ih (Nat.shiftRight p 1) l) r) (Nat.beq (Nat.land p 1) 0)) t)
    d

def Tree.set {α : Type} (d k : Nat) (v : α) (t : Tree α) : Tree α := Tree.setP k v d k t

/-- number of bits (fuel 64 halvings). -/
def bitLen (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 64)
    (fun i ih x => Bool.rec (ih (Nat.shiftRight x 1)) (Nat.sub 64 i) (Nat.beq x 0))
    65 n

/-- floor log2 by binary search over 32 exponent bits (only a hint: callers re-verify). -/
def ilog (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun n ih acc => ih (Bool.rec (Nat.add acc (Nat.pow 2 n)) acc
      (Nat.beq (Nat.shiftRight x (Nat.add acc (Nat.pow 2 n))) 0)))
    32 0

/-! ## Vanishing pairs -/

/-- partner table: `pt.get c = some s` registers the HA pair `(c, s)`; `pc` has bit `2c` set. -/
structure Pairs where
  d : Nat
  pt : Tree Nat
  pc : Nat

def pairHit (P : Pairs) (m c : Nat) : Bool :=
  Bool.rec false (Option.rec false (fun s => tb m (Nat.mul 2 s)) (P.pt.get P.d c))
    (tb m (Nat.mul 2 c))

def vanGo (P : Pairs) (m : Nat) (fuel : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih T =>
      Bool.rec
        (Bool.rec (ih (Nat.xor T (Nat.land T (Nat.xor T (Nat.sub T 1)))))
          true
          (pairHit P m (Nat.shiftRight (ilog (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1)))
        false (Nat.beq T 0))
    fuel

/-- does monomial `m` contain both symbols of a registered pair? -/
def van (P : Pairs) (m : Nat) : Bool := vanGo P m 64 (Nat.land m P.pc)

/-! ## Byte / word decoding -/

def bytesSeq (acc : List Nat) (len : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => acc)
    (fun _ ih x => Nat.land x 255 :: ih (Nat.shiftRight x 8)) len

/-- `toUnits u d n len acc`: the `len` little-endian units of `8u` bits of `n`, then `acc`. -/
def toUnits (u : Nat) (d : Nat) : Nat → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → List Nat)
    (fun n len acc =>
      Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => acc)
        (fun _ ih x => Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.mul 8 u)) 1) ::
          ih (Nat.shiftRight x (Nat.mul 8 u))) len n)
    (fun _ ih n len acc =>
      Bool.rec
        (ih (Nat.land n
              (Nat.sub (Nat.shiftLeft 1 (Nat.mul (Nat.mul 8 u) (Nat.shiftRight len 1))) 1))
            (Nat.shiftRight len 1)
          (ih (Nat.shiftRight n (Nat.mul (Nat.mul 8 u) (Nat.shiftRight len 1)))
            (Nat.sub len (Nat.shiftRight len 1)) acc))
        (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => acc)
          (fun _ ih x => Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.mul 8 u)) 1) ::
            ih (Nat.shiftRight x (Nat.mul 8 u))) len n)
        (Nat.ble len 8))
    d

/-- `Σ_i l[i] · 2^(k·i)`: lets the generator pass a big file as a list of small literals (the Lean
parser is quadratic on one huge numeric literal: 64 KB takes 8 s). -/
def joinChunks (k : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ ih => Nat.lor c (Nat.shiftLeft ih k)) l

/-- bytes of a file given as a little-endian `Nat` and its length. -/
def toBytes (n len : Nat) : List Nat := toUnits 1 40 n len []
/-- `u32` words (length in words). -/
def toWords (n len : Nat) : List Nat := toUnits 4 40 n len []

/-! ## Binary AIGER (trusted parser: defines the circuit the theorem talks about) -/

structure Aig where
  M : Nat
  I : Nat
  outs : List Nat
  ands : List (Nat × Nat)

/-- CPS: read one element. -/
def rd {β : Type} (ws : List Nat) (fail : β) (k : Nat → List Nat → β) : β :=
  List.rec (motive := fun _ => β) fail (fun w ws _ => k w ws) ws

def isDigit (b : Nat) : Bool := Bool.rec false (Nat.ble b 57) (Nat.ble 48 b)

/-- parse decimal digits (accumulated in `acc`), stop at the first non-digit and require it to be
`term`; CPS with the value and the rest after the terminator. -/
def pnumGo {β : Type} (term : Nat) (fail : β) (k : Nat → List Nat → β) (bs : List Nat) :
    Nat → β :=
  List.rec (motive := fun _ => Nat → β) (fun _ => fail)
    (fun b bs ih acc =>
      Bool.rec (Bool.rec fail (k acc bs) (Nat.beq b term))
        (ih (Nat.add (Nat.mul acc 10) (Nat.sub b 48))) (isDigit b))
    bs

def pnum {β : Type} (term : Nat) (fail : β) (bs : List Nat) (k : Nat → List Nat → β) : β :=
  rd bs fail fun b _ => Bool.rec fail (pnumGo term fail k bs 0) (isDigit b)

/-- LEB128 varint (CPS). -/
def pvarGo {β : Type} (fail : β) (k : Nat → List Nat → β) (bs : List Nat) : Nat → Nat → β :=
  List.rec (motive := fun _ => Nat → Nat → β) (fun _ _ => fail)
    (fun b bs ih acc sh =>
      Bool.rec (k (Nat.lor acc (Nat.shiftLeft (Nat.land b 127) sh)) bs)
        (ih (Nat.lor acc (Nat.shiftLeft (Nat.land b 127) sh)) (Nat.add sh 7))
        (Nat.ble 128 b))
    bs

def pvar {β : Type} (fail : β) (bs : List Nat) (k : Nat → List Nat → β) : β := pvarGo fail k bs 0 0

/-- `O` output lines. -/
def poutsGo {β : Type} (fail : β) (k : List Nat → List Nat → β) (n : Nat) :
    List Nat → List Nat → β :=
  Nat.rec (motive := fun _ => List Nat → List Nat → β) (fun acc bs => k acc.reverse bs)
    (fun _ ih acc bs => pnum 10 fail bs fun o bs => ih (o :: acc) bs) n

/-- `A` delta-coded ANDs; `lhs = 2(I+1+i)`; requires `0 ≤ rhs1 ≤ rhs0 < lhs`. -/
def pandsGo {β : Type} (fail : β) (k : List (Nat × Nat) → β) (n : Nat) :
    Nat → List (Nat × Nat) → List Nat → β :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat) → List Nat → β)
    (fun _ acc _ => k acc.reverse)
    (fun _ ih lhs acc bs =>
      pvar fail bs fun d0 bs => pvar fail bs fun d1 bs =>
        Bool.rec fail
          (Bool.rec fail
            (ih (Nat.add lhs 2) ((Nat.sub lhs d0, Nat.sub (Nat.sub lhs d0) d1) :: acc) bs)
            (Nat.ble d1 (Nat.sub lhs d0)))
          (Bool.rec (Nat.ble d0 lhs) false (Nat.beq d0 0)))
    n

/-- Parse a binary AIGER file (`aig M I L O A\n`, `L = 0`, `M = I + A`). Trailing symbol table /
comments are ignored. -/
def parseAig (bs : List Nat) : Option Aig :=
  rd bs none fun b0 bs => rd bs none fun b1 bs => rd bs none fun b2 bs => rd bs none fun b3 bs =>
  Bool.rec none
    (pnum 32 none bs fun M bs => pnum 32 none bs fun I bs => pnum 32 none bs fun L bs =>
     pnum 32 none bs fun O bs => pnum 10 none bs fun A bs =>
     Bool.rec none
       (poutsGo none (fun outs bs =>
          pandsGo none (fun ands => some ⟨M, I, outs, ands⟩) A (Nat.mul 2 (Nat.add I 1)) [] bs)
          O [] bs)
       (Bool.rec false (Nat.beq M (Nat.add I A)) (Nat.beq L 0)))
    (Bool.rec false (Bool.rec false (Bool.rec false (Nat.beq b3 32) (Nat.beq b2 103))
      (Nat.beq b1 105)) (Nat.beq b0 97))

/-! ## Checker environment -/

def UNB : Nat := 0xFFFFFFFF

structure Env where
  M : Nat         -- modulus 2^n_out
  Mx : Nat        -- AIG maxvar
  I : Nat         -- #PIs
  ad : Nat        -- AIG trie depth
  andT : Tree (Nat × Nat)  -- AND node ↦ (rhs0, rhs1)
  nd : Nat        -- net trie depth
  bind : Tree Nat -- net ↦ literal (bound nets only)

/-- AND trie: node `I+1+i ↦ ands[i]`. -/
def andTree (d : Nat) (I : Nat) (ands : List (Nat × Nat)) : Tree (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → Tree (Nat × Nat) → Tree (Nat × Nat)) (fun _ t => t)
    (fun a _ ih n t => ih (Nat.succ n) (Tree.set d n a t)) ands (Nat.succ I) Tree.empty

/-! ## Cone simulation (truth tables over ≤ 3 leaves) -/

def lookup (n : Nat) (l : List (Nat × Nat)) : Option Nat :=
  List.rec none (fun a _ ih => Bool.rec ih (some a.2) (Nat.beq n a.1)) l

/-- complement within `full` if the literal is negated -/
def cmpl (full lit v : Nat) : Nat := Bool.rec v (Nat.xor full v) (Nat.beq (Nat.land lit 1) 1)

/-- one step of the cone simulation; `ih` simulates with one less fuel. -/
def simStep (e : Env) (full : Nat) (leaves : List (Nat × Nat))
    (ih : Nat → List (Nat × Nat) → Nat → Option (Nat × List (Nat × Nat) × Nat))
    (lit : Nat) (memo : List (Nat × Nat)) (bud : Nat) : Option (Nat × List (Nat × Nat) × Nat) :=
  Option.rec
    (Bool.rec
      (Option.rec
        (Bool.rec
          (Bool.rec
            (Option.rec none
              (fun r =>
                Bool.rec none
                  (Option.rec none
                    (fun x0 =>
                      Option.rec none
                        (fun x1 => some (cmpl full lit (Nat.land x0.1 x1.1),
                            (Nat.shiftRight lit 1, Nat.land x0.1 x1.1) :: x1.2.1, x1.2.2))
                        (ih r.2 x0.2.1 x0.2.2))
                    (ih r.1 memo (Nat.sub bud 1)))
                  (Bool.rec false (Nat.ble (Nat.succ r.2) (Nat.mul (Nat.shiftRight lit 1) 2))
                    (Nat.ble (Nat.succ r.1) (Nat.mul (Nat.shiftRight lit 1) 2))))
              (e.andT.get e.ad (Nat.shiftRight lit 1)))
            none (Nat.beq bud 0))
          none (Nat.ble (Nat.shiftRight lit 1) e.I))
        (fun v => some (cmpl full lit v, memo, bud))
        (lookup (Nat.shiftRight lit 1) memo))
      (some (cmpl full lit 0, memo, bud))
      (Nat.beq (Nat.shiftRight lit 1) 0))
    (fun v => some (cmpl full lit v, memo, bud))
    (lookup (Nat.shiftRight lit 1) leaves)

/-- `sim e full leaves fuel lit memo budget` : truth table of `lit`, the memo of visited AND
nodes and the remaining budget, or `none` (reject). Order of checks as in `art_ref.py`: leaf,
constant node, memo, PI (reject), budget, AND. -/
def sim (e : Env) (full : Nat) (leaves : List (Nat × Nat)) (fuel : Nat) :
    Nat → List (Nat × Nat) → Nat → Option (Nat × List (Nat × Nat) × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat) → Nat → Option (Nat × List (Nat × Nat) × Nat))
    (fun _ _ _ => none) (fun _ ih => simStep e full leaves ih) fuel

def tt (e : Env) (full : Nat) (leaves : List (Nat × Nat)) (lit : Nat) : Option Nat :=
  Option.rec none (fun r => some r.1) (sim e full leaves 70 lit [] 64)

/-! ## Gates -/

structure GS where
  rules : Tree Poly
  pr : Pairs

def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun j' _ => ih j') j) l i

/-- 6-variable projection masks `x_0 = 0xAAAA…, …, x_5 = 0xFFFFFFFF00000000` (bit `t` of `x_j`
is bit `j` of `t`); truncated to `2^k` bits by `&&& full`. -/
def xmask (j : Nat) : Nat :=
  nthN [0xAAAAAAAAAAAAAAAA, 0xCCCCCCCCCCCCCCCC, 0xF0F0F0F0F0F0F0F0, 0xFF00FF00FF00FF00,
    0xFFFF0000FFFF0000, 0xFFFFFFFF00000000] j

/-- read `n` words (CPS). -/
def rdN {β : Type} (fail : β) (n : Nat) (k : List Nat → List Nat → β) : List Nat → β :=
  Nat.rec (motive := fun _ => List Nat → List Nat → β) (fun acc ws => k acc.reverse ws)
    (fun _ ih acc ws => rd ws fail fun w ws => ih (w :: acc) ws) n []

/-- Leaves from the leaf literals `b_j`: node `b_j>>1` gets mask `x_j` (complemented when `b_j` is
negated, so that the literal has table `x_j`). `none` on a duplicate node. -/
def mkLeaves (full : Nat) (lits : List Nat) : Option (List (Nat × Nat)) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat) → Option (List (Nat × Nat)))
    (fun _ acc => some acc)
    (fun b _ ih j acc =>
      Option.rec
        (ih (Nat.succ j) ((Nat.shiftRight b 1, cmpl full b (Nat.land (xmask j) full)) :: acc))
        (fun _ => none) (lookup (Nat.shiftRight b 1) acc))
    lits 0 []

/-- bindings of the input nets (`none` if one is unbound). -/
def binds (e : Env) (ins : List Nat) : Option (List Nat) :=
  List.rec (some [])
    (fun x _ ih => Option.rec none (fun b => Option.rec none (fun bs => some (b :: bs)) ih)
      (e.bind.get e.nd (Nat.shiftRight x 1)))
    ins

def netsOf (ins : List Nat) : List Nat := List.rec [] (fun x _ ih => Nat.shiftRight x 1 :: ih) ins

/-- default-mode input tables `x_j &&& full`. -/
def tinDef (full : Nat) (ins : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ _ ih j => Nat.land (xmask j) full :: ih (Nat.succ j)) ins 0

/-- validation environment `(sym(2·net_j), table_j)`. -/
def zipEnv (ins tin : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List Nat → List (Nat × Nat)) (fun _ => [])
    (fun x _ ih tin =>
      List.rec [] (fun t tin' _ => (Nat.mul 2 (Nat.shiftRight x 1), t) :: ih tin') tin)
    ins tin

/-- true-set at row `t`: OR of `2^sym` over env entries whose table has bit `t`. -/
def tset (env : List (Nat × Nat)) (t : Nat) : Nat :=
  List.rec 0 (fun a _ ih => Nat.lor (Bool.rec 0 (Nat.pow 2 a.1) (tb a.2 t)) ih) env

def sAll (env : List (Nat × Nat)) : Nat :=
  List.rec 0 (fun a _ ih => Nat.lor (Nat.pow 2 a.1) ih) env

/-- generic rule validation over all `rows` rows: `Q(row t) = bit t of table`. -/
def validate (M : Nat) (env : List (Nat × Nat)) (rows : Nat) (Q : Poly) (tab : Nat) : Bool :=
  Bool.rec false
    (Nat.rec (motive := fun _ => Bool) true
      (fun t ih => Bool.rec false ih
        (Nat.beq (evalK M (tset env t) Q) (Nat.land (Nat.shiftRight tab t) 1)))
      rows)
    (subAll (sAll env) Q)

/-- input literal polys `ℓ_j` -/
def lits (M : Nat) (ins : List Nat) : List Poly :=
  List.rec []
    (fun x _ ih => litP M (Nat.beq (Nat.land x 1) 1) (Nat.mul 2 (Nat.shiftRight x 1)) :: ih)
    ins

def nth (l : List Poly) (i : Nat) : Poly :=
  List.rec (motive := fun _ => Nat → Poly) (fun _ => Poly.nil)
    (fun a _ ih j => Nat.rec (motive := fun _ => Poly) a (fun j' _ => ih j') j) l i

def addP (M : Nat) (p q : Poly) : Poly := merge M p q

def majP (M : Nat) (L : List Poly) : Poly :=
  addP M (addP M (addP M (mulP M (nth L 0) (nth L 1)) (mulP M (nth L 0) (nth L 2)))
      (mulP M (nth L 1) (nth L 2)))
    (scaleP M (negC M 2) (mulP M (mulP M (nth L 0) (nth L 1)) (nth L 2)))

/-- rule polynomials, per output (`c` = first output net, used by HA/FA sums). Their correctness
is irrelevant for soundness: every rule is validated semantically. -/
def rulesOf (M : Nat) (kind : Nat) (L : List Poly) (c : Nat) : List Poly :=
  let l0 := nth L 0; let l1 := nth L 1; let l2 := nth L 2
  let sum2 := addP M l0 l1
  let sum3 := addP M sum2 l2
  let m01 := mulP M l0 l1
  let sc := single M (negC M 2) (Nat.pow 2 (Nat.mul 2 c))
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec []
    [majP M L, addP M sum3 sc] (Nat.beq kind 7))
    [m01, addP M sum2 sc] (Nat.beq kind 6))
    [majP M L] (Nat.beq kind 5))
    [addP M (addP M sum3 (scaleP M (negC M 2)
        (addP M (addP M m01 (mulP M l0 l2)) (mulP M l1 l2))))
      (scaleP M 4 (mulP M m01 l2))] (Nat.beq kind 4))
    [addP M sum2 (scaleP M (negC M 2) m01)] (Nat.beq kind 3))
    [addP M sum2 (scaleP M (negC M 1) m01)] (Nat.beq kind 2))
    [m01] (Nat.beq kind 1)

def nOut (kind : Nat) : Nat := Bool.rec 1 2 (Bool.rec (Nat.beq kind 7) true (Nat.beq kind 6))
def nIn (kind : Nat) : Nat :=
  Bool.rec 2 3 (Bool.rec (Bool.rec (Nat.beq kind 7) true (Nat.beq kind 5)) true (Nat.beq kind 4))

/-- output-net requirements: bound, its node is not a PI, no rule yet. -/
def outOk (e : Env) (st : GS) (o : Nat) : Bool :=
  Option.rec false
    (fun b => Bool.rec
      (Option.rec true (fun _ => false) (st.rules.get e.nd o))
      false
      (Bool.rec false (Nat.ble (Nat.shiftRight b 1) e.I) (Nat.ble 1 (Nat.shiftRight b 1))))
    (e.bind.get e.nd o)

def allB (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec true (fun a _ ih => Bool.rec false ih (f a)) l

/-- tables `tt(bind[n])` of a list of nets (in order) -/
def ttAll (e : Env) (full : Nat) (leaves : List (Nat × Nat)) (nets : List Nat) :
    Option (List Nat) :=
  List.rec (some [])
    (fun o _ ih => Option.rec none
      (fun b => Option.rec none (fun v => Option.rec none (fun vs => some (v :: vs)) ih)
        (tt e full leaves b))
      (e.bind.get e.nd o))
    nets

/-- validate and install each `(o, Q, table)`. -/
def install (e : Env) (env : List (Nat × Nat)) (rows : Nat) (pr : Pairs) :
    List Nat → List Poly → List Nat → Tree Poly → Option (Tree Poly) :=
  List.rec (motive := fun _ => List Poly → List Nat → Tree Poly → Option (Tree Poly))
    (fun _ _ rules => some rules)
    (fun o _ ih Qs tabs rules =>
      List.rec (motive := fun _ => Option (Tree Poly)) none
        (fun Q Qs _ => List.rec (motive := fun _ => Option (Tree Poly)) none
          (fun tab tabs _ =>
            Bool.rec none (ih Qs tabs (rules.set e.nd o (normP (van pr) Q)))
              (validate e.M env rows Q tab))
          tabs)
        Qs)

/-- install the rules of one gate (+ HA pair) given its tables. -/
def gateFinish {β : Type} (e : Env) (st : GS) (kind : Nat) (outs ins : List Nat) (rows : Nat)
    (tin tabs : List Nat) (ws : List Nat) (kont : GS → List Nat → β) (fail : β) : β :=
  Option.rec fail
    (fun rules' =>
      Bool.rec (kont ⟨rules', st.pr⟩ ws)
        (Bool.rec fail
          (kont ⟨rules', ⟨st.pr.d, st.pr.pt.set st.pr.d (nthN outs 0) (nthN outs 1),
              Nat.lor st.pr.pc (Nat.pow 2 (Nat.mul 2 (nthN outs 0)))⟩⟩ ws)
          (Nat.beq (Nat.land (nthN tabs 0) (nthN tabs 1)) 0))
        (Nat.beq kind 6))
    (install e
      (Bool.rec (zipEnv ins tin) ((Nat.mul 2 (nthN outs 0), nthN tabs 0) :: zipEnv ins tin)
        (Nat.ble 6 kind))
      rows st.pr outs (rulesOf e.M kind (lits e.M ins) (nthN outs 0)) tabs st.rules)

/-- one gate given its leaf literals `lits` (`k` leaves) -/
def gateBody {β : Type} (e : Env) (st : GS) (kind : Nat) (expl : Bool) (outs ins lits : List Nat)
    (k : Nat) (ws : List Nat) (kont : GS → List Nat → β) (fail : β) : β :=
  Bool.rec fail
    (Option.rec fail
      (fun leaves =>
        Option.rec fail
          (fun tin =>
            Option.rec fail
              (fun tabs => gateFinish e st kind outs ins (Nat.pow 2 k) tin tabs ws kont fail)
              (ttAll e (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1) leaves outs))
          (Bool.rec (some (tinDef (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1) ins))
            (ttAll e (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1) leaves (netsOf ins)) expl))
      (mkLeaves (Nat.sub (Nat.pow 2 (Nat.pow 2 k)) 1) lits))
    (Bool.rec (allB (outOk e st) outs) false
      (Bool.rec false (Nat.beq (nthN outs 0) (nthN outs 1)) (Nat.beq (nOut kind) 2)))

/-- one GATE record. -/
def gateStep {β : Type} (e : Env) (st : GS) (ws : List Nat)
    (kont : GS → List Nat → β) (fail : β) : β :=
  rd ws fail fun kraw ws =>
  Bool.rec fail
  (rdN fail (nOut (Nat.land kraw 255)) (fun outs ws =>
    rdN fail (nIn (Nat.land kraw 255)) (fun ins ws =>
      Option.rec fail
        (fun bl =>
          Bool.rec
            (gateBody e st (Nat.land kraw 255) false outs ins bl
              (nIn (Nat.land kraw 255)) ws kont fail)
            (rd ws fail fun nl ws =>
              Bool.rec fail
                (rdN fail nl (fun lv ws =>
                  Bool.rec fail
                    (gateBody e st (Nat.land kraw 255) true outs ins lv nl ws kont fail)
                    (allB (fun l => Nat.ble (Nat.succ l) (Nat.mul 2 (Nat.succ e.Mx))) lv)) ws)
                (Bool.rec false (Nat.ble nl 6) (Nat.ble 1 nl)))
            (tb kraw 8))
        (binds e ins))
      ws) ws)
  (Bool.rec false (Bool.rec false (Nat.ble kraw 511) (Nat.ble (Nat.land kraw 255) 7))
    (Nat.ble 1 (Nat.land kraw 255)))

def gates {β : Type} (e : Env) (fail : β) (k : GS → List Nat → β) (n : Nat) : GS → List Nat → β :=
  Nat.rec (motive := fun _ => GS → List Nat → β) k
    (fun _ ih st ws => gateStep e st ws ih fail) n

/-! ## Cones -/

def coneVars (e : Env) (pr : Pairs) (root : Nat) (rules : Tree Poly) (k : Nat) :
    Poly → List Nat → (Poly → List Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Poly → List Nat → (Poly → List Nat → Bool) → Bool)
    (fun r ws kk => kk r ws)
    (fun _ ih r ws kk => rd ws false fun v ws =>
      Option.rec false
        (fun Rv => Bool.rec (ih (normP (van pr) (substP e.M (van pr) (Nat.mul 2 v) Rv r)) ws kk)
          false (Nat.beq v root))
        (rules.get e.nd v))
    k

def cones (e : Env) (k : GS → List Nat → Bool) (n : Nat) : GS → List Nat → Bool :=
  Nat.rec (motive := fun _ => GS → List Nat → Bool) k
    (fun _ ih st ws =>
      rd ws false fun root ws => rd ws false fun kk ws =>
        Option.rec false
          (fun r => coneVars e st.pr root st.rules kk r ws
            (fun r' ws => ih ⟨st.rules.set e.nd root r', st.pr⟩ ws))
          (st.rules.get e.nd root))
    n

/-! ## Main reduction -/

/-- replace every flipped `sym(2x)` occurring in `R` by `1 - sym(2x+1)`; `T` = flipped symbols
of `R` (bits); the index is recomputed by `ilog` (any `x` gives a valid substitution). -/
def flipR (M : Nat) (fuel : Nat) : Nat → Poly → Poly :=
  Nat.rec (motive := fun _ => Nat → Poly → Poly) (fun _ R => R)
    (fun _ ih T R =>
      Bool.rec
        (ih (Nat.xor T (Nat.land T (Nat.xor T (Nat.sub T 1))))
          (substP M noVan
            (Nat.mul 2 (Nat.shiftRight (ilog (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1))
            (oneSub M (single M 1 (Nat.pow 2 (Nat.add (Nat.mul 2
              (Nat.shiftRight (ilog (Nat.land T (Nat.xor T (Nat.sub T 1)))) 1)) 1)))) R))
        R (Nat.beq T 0))
    fuel

/-- MAIN loop: `fl` = bitset of flipped symbols `2x`. -/
def mainLoop (e : Env) (pr : Pairs) (rules : Tree Poly) (nNets : Nat) (n : Nat) :
    Poly → Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Poly → Nat → List Nat → Bool)
    (fun P _ ws => Bool.rec false (isNil P) (List.rec true (fun _ _ _ => false) ws))
    (fun _ ih P fl ws =>
      rd ws false fun op ws =>
        Bool.rec
          -- SUBST v
          (Option.rec false
            (fun R0 =>
              Bool.rec
                (ih (substP e.M (van pr) (Nat.mul 2 (Nat.shiftRight op 1))
                    (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0) P) fl ws)
                (ih (substP e.M (van pr) (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)
                    (oneSub e.M (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0)) P) fl ws)
                (tb fl (Nat.mul 2 (Nat.shiftRight op 1))))
            (rules.get e.nd (Nat.shiftRight op 1)))
          -- FLIP v
          (Bool.rec
            (ih (substP e.M (van pr) (Nat.mul 2 (Nat.shiftRight op 1))
                (oneSub e.M
                  (single e.M 1 (Nat.pow 2 (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)))) P)
              (Nat.lor fl (Nat.pow 2 (Nat.mul 2 (Nat.shiftRight op 1)))) ws)
            false
            (Bool.rec (tb fl (Nat.mul 2 (Nat.shiftRight op 1))) true
              (Nat.ble nNets (Nat.shiftRight op 1))))
          (Nat.beq (Nat.land op 1) 1))
    n

/-! ## Initial polynomial `W(O) - Wspec(a)·Wspec(b)` -/

/-- `Σ_j 2^j · bit_j`, `bit_j = x` or `1 - x` per out_ref word. -/
def woTerms (M : Nat) (refs : List Nat) : List Poly :=
  List.rec (motive := fun _ => Nat → List Poly) (fun _ => [])
    (fun r _ ih j =>
      scaleP M (Nat.pow 2 j) (litP M (Nat.beq (Nat.land r 1) 1) (Nat.mul 2 (Nat.shiftRight r 1)))
        :: ih (Nat.succ j))
    refs 0

/-- weighted input terms `(coef, bit)`: `2^i`, top weight negated when signed. -/
def wTerms (M : Nat) (signed : Bool) (n : Nat) (nets : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => [])
    (fun x _ ih i =>
      (Bool.rec (Nat.pow 2 i)
        (Bool.rec (Nat.pow 2 i) (negC M (Nat.pow 2 i)) (Nat.beq (Nat.succ i) n))
        signed, Nat.pow 2 (Nat.mul 2 x)) :: ih (Nat.succ i))
    nets 0

/-- `- a·b` terms -/
def prodTerms (M : Nat) (A B : List (Nat × Nat)) : List Poly :=
  List.rec (motive := fun _ => List Poly) []
    (fun a _ ih =>
      List.rec (motive := fun _ => List Poly) ih
        (fun b _ ih' => single M (negC M (Nat.mul a.1 b.1)) (Nat.lor a.2 b.2) :: ih') B)
    A

def takeN (n : Nat) (l : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun _ ih l => List.rec [] (fun a t _ => a :: ih t) l) n l
def dropN (n : Nat) (l : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun l => l)
    (fun _ ih l => List.rec [] (fun _ t _ => ih t) l) n l

def initP (M : Nat) (pr : Pairs) (signed : Bool) (n : Nat) (inNet outRef : List Nat) : Poly :=
  normP (van pr) (sumB M (woTerms M outRef ++
    prodTerms M (wTerms M signed n (takeN n inNet)) (wTerms M signed n (dropN n inNet))))

/-! ## Header, NET / IN / OUT sections -/

def bindTree (Mx : Nat) (d : Nat) : Nat → List Nat → Tree Nat → Option (Tree Nat) :=
  fun _ ws t =>
  List.rec (motive := fun _ => Nat → Tree Nat → Option (Tree Nat)) (fun _ t => some t)
    (fun b _ ih i t =>
      Bool.rec
        (Bool.rec none (ih (Nat.succ i) (t.set d i b))
          (Nat.ble (Nat.succ b) (Nat.mul 2 (Nat.succ Mx))))
        (ih (Nat.succ i) t) (Nat.beq b UNB))
    ws 0 t

def inOk (e : Env) (nNets : Nat) (inNet : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i =>
      Bool.rec false
        (Option.rec false
          (fun b => Bool.rec false (ih (Nat.succ i)) (Nat.beq b (Nat.mul 2 (Nat.succ i))))
          (e.bind.get e.nd x))
        (Nat.ble (Nat.succ x) nNets))
    inNet 0

def outOkAll (e : Env) (nNets : Nat) (outRef aouts : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun r _ ih ao => List.rec false
      (fun a ao' _ => Bool.rec false
        (Option.rec false (fun b => Bool.rec false (ih ao') (Nat.beq (Nat.xor b (Nat.land r 1)) a))
          (e.bind.get e.nd (Nat.shiftRight r 1)))
        (Nat.ble (Nat.succ (Nat.shiftRight r 1)) nNets)) ao)
    outRef aouts

def len (l : List Nat) : Nat := List.rec 0 (fun _ _ ih => Nat.succ ih) l

/-- phases after the IN/OUT sections. -/
def runPhases (e : Env) (signed : Bool) (nNets nG nC nMain nIn : Nat) (inNet outRef : List Nat)
    (ws : List Nat) : Bool :=
  gates e false
    (fun st ws =>
      cones e (fun st ws =>
          mainLoop e st.pr st.rules nNets nMain
            (initP e.M st.pr signed (Nat.shiftRight nIn 1) inNet outRef) 0 ws)
        nC st ws)
    nG ⟨Tree.empty, ⟨e.nd, Tree.empty, 0⟩⟩ ws

def headerOk (signed : Bool) (g : Aig) (h ws0 : List Nat) : Bool :=
  Bool.rec false (Bool.rec false (Bool.rec false (Bool.rec false (Bool.rec false
    (Nat.beq (nthN h 9) (len ws0))
    (Nat.beq (nthN h 4) (len g.outs)))
    (Bool.rec false (Nat.beq (Nat.land (nthN h 3) 1) 0) (Nat.beq (nthN h 3) g.I)))
    (Nat.beq (nthN h 2) (Bool.rec 0 1 signed)))
    (Nat.beq (nthN h 1) 1))
    (Nat.beq (nthN h 0) 0x31545241)

def afterBind (signed : Bool) (g : Aig) (h : List Nat) (bt : Tree Nat) (ws : List Nat) : Bool :=
  let e : Env := ⟨Nat.pow 2 (nthN h 4), g.M, g.I, bitLen g.M, andTree (bitLen g.M) g.I g.ands,
    bitLen (nthN h 5), bt⟩
  rdN false (nthN h 3) (fun inNet ws => rdN false (nthN h 4) (fun outRef ws =>
      Bool.rec false
        (runPhases e signed (nthN h 5) (nthN h 6) (nthN h 7) (nthN h 8) (nthN h 3) inNet outRef ws)
        (Bool.rec false (outOkAll e (nthN h 5) outRef g.outs) (inOk e (nthN h 5) inNet)))
    ws) ws

/-- the checker on a parsed AIG and the ART word list. -/
def checkWords (signed : Bool) (g : Aig) (ws0 : List Nat) : Bool :=
  rdN false 10 (fun h ws =>
    Bool.rec false
      (rdN false (nthN h 5) (fun bindW ws =>
          Option.rec false (fun bt => afterBind signed g h bt ws)
            (bindTree g.M (bitLen (nthN h 5)) (nthN h 5) bindW Tree.empty))
        ws)
      (headerOk signed g h ws0))
    ws0

/-- **The checker.** `aigN`/`artN`: file contents as little-endian `Nat`s, `aigLen`/`artLen`: sizes
in bytes. `signed` must match the ART header's spec field. -/
def checkArt (signed : Bool) (aigN aigLen artN artLen : Nat) : Bool :=
  Option.rec false
    (fun g => Bool.rec false (checkWords signed g (toWords artN (Nat.shiftRight artLen 2)))
      (Nat.beq (Nat.land artLen 3) 0))
    (parseAig (toBytes aigN aigLen))

end LeanQbe.T.Examples.Arisca

end
end
