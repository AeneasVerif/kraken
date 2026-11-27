module

public import LeanQbe.T.Examples.Arisca.ArtCore

/-!
# ART checker, geobucket variant (`checkArtB`)

Identical to `checkArt` up to and including the CONE phase. In MAIN, `P` is stored as buckets
keyed by the leading (largest) symbol of each monomial: a trie `Tree Poly` (each bucket sorted by
decreasing monomial) plus a hint bitset `nz` of the possibly-nonempty bucket keys.

* SUBST `s`: only buckets with key `≥ s` (bits of `nz >>> s`) are split into (terms containing `s`,
  rest); for rank-ordered certificates that is exactly bucket `s`.
* the products (sorted by `sumB`) are cut into runs of equal leading symbol (one `lead` call per
  run) and each run is merged into its bucket: cost O(run + bucket prefix) instead of a walk over
  `P`.
* `lead` (= `ilog`) and `nz` are only hints: soundness never depends on them (a wrong hint can only
  leave terms unsubstituted, i.e. make the checker reject). `setNE` never evicts (it fails instead),
  so the bucket sum is exactly the value of `P`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace LeanQbe.T.Examples.Arisca

/-- floor log2 by binary search over `K` exponent bits (hint only). -/
def ilogK (K x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun n ih acc => ih (Bool.rec (Nat.add acc (Nat.pow 2 n)) acc
      (Nat.beq (Nat.shiftRight x (Nat.add acc (Nat.pow 2 n))) 0)))
    K 0

/-- set without eviction: `none` if another key occupies the leaf. -/
def Tree.setNEP {α : Type} (k : Nat) (v : α) (d : Nat) : Nat → Tree α → Option (Tree α) :=
  Nat.rec (motive := fun _ => Nat → Tree α → Option (Tree α))
    (fun _ t => Tree.rec (motive := fun _ => Option (Tree α)) (some (Tree.tip k v))
      (fun k' _ => Bool.rec none (some (Tree.tip k v)) (Nat.beq k k')) (fun _ _ _ _ => none) t)
    (fun _ ih p t =>
      Tree.rec (motive := fun _ => Option (Tree α))
        (Bool.rec
          (Option.rec none (fun c => some (Tree.br Tree.empty c))
            (ih (Nat.shiftRight p 1) Tree.empty))
          (Option.rec none (fun c => some (Tree.br c Tree.empty))
            (ih (Nat.shiftRight p 1) Tree.empty))
          (Nat.beq (Nat.land p 1) 0))
        (fun _ _ => none)
        (fun l r _ _ =>
          Bool.rec
            (Option.rec none (fun c => some (Tree.br l c)) (ih (Nat.shiftRight p 1) r))
            (Option.rec none (fun c => some (Tree.br c r)) (ih (Nat.shiftRight p 1) l))
            (Nat.beq (Nat.land p 1) 0)) t)
    d

def Tree.setNE {α : Type} (d k : Nat) (v : α) (t : Tree α) : Option (Tree α) :=
  Tree.setNEP k v d k t

/-- bucket `k` (`nil` if absent) -/
def bget (d k : Nat) (t : Tree Poly) : Poly := Option.rec Poly.nil (fun p => p) (t.get d k)

/-- every bucket is empty -/
def allNil (t : Tree Poly) : Bool :=
  Tree.rec (motive := fun _ => Bool) true (fun _ v => isNil v)
    (fun _ _ il ir => Bool.rec false ir il) t

def appendP (p q : Poly) : Poly :=
  Poly.rec (motive := fun _ => Poly) q (fun c m _ ih => Poly.cons c m ih) p

/-- terms of the leading run (monomial `≥ b`) -/
def takeRun (b : Nat) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.nil
    (fun c m _ ih => Bool.rec Poly.nil (Poly.cons c m ih) (Nat.ble b m))

/-- the rest after the leading run -/
def dropRun (b : Nat) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly) Poly.nil
    (fun c m p ih => Bool.rec (Poly.cons c m p) ih (Nat.ble b m))

/-- update the nonempty-hint for bucket `k` with new contents `B` -/
def nzUpd (nz k : Nat) (B : Poly) : Nat :=
  Bool.rec (Nat.lor nz (Nat.pow 2 k)) (Nat.xor nz (Nat.land nz (Nat.pow 2 k))) (isNil B)

/-- merge `B` into bucket `k` (CPS; fails on a trie collision). -/
def addBucket (M bd k : Nat) (B : Poly) (t : Tree Poly) (nz : Nat)
    (kont : Tree Poly → Nat → Bool) : Bool :=
  Option.rec false (fun t' => kont t' (nzUpd nz k (merge M B (bget bd k t))))
    (t.setNE bd k (merge M B (bget bd k t)))

/-- insert a sorted polynomial into the buckets, one leading run at a time. -/
def insRuns (M bd : Nat) (lead : Nat → Nat) (fuel : Nat) :
    Poly → Tree Poly → Nat → (Tree Poly → Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => Poly → Tree Poly → Nat → (Tree Poly → Nat → Bool) → Bool)
    (fun _ _ _ _ => false)
    (fun _ ih Q t nz kont =>
      Poly.rec (motive := fun _ => Bool) (kont t nz)
        (fun c m q _ =>
          addBucket M bd (lead m) (Poly.cons c m (takeRun (Nat.pow 2 (lead m)) q)) t nz
            (fun t' nz' => ih (dropRun (Nat.pow 2 (lead m)) q) t' nz' kont))
        Q)
    fuel

/-- split buckets with keys `s + (bit positions of H)` into (terms containing `s`, rest). -/
def collB (bd s : Nat) (lead : Nat → Nat) (fuel : Nat) :
    Nat → Tree Poly → Nat → Poly → (Tree Poly → Nat → Poly → Bool) → Bool :=
  Nat.rec (motive := fun _ => Nat → Tree Poly → Nat → Poly → (Tree Poly → Nat → Poly → Bool) → Bool)
    (fun _ _ _ _ _ => false)
    (fun _ ih H t nz W kont =>
      Bool.rec
        (Option.rec false
          (fun t' => ih (Nat.xor H (Nat.land H (Nat.xor H (Nat.sub H 1)))) t'
            (nzUpd nz (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1)))))
              (filterS (Nat.pow 2 s)
                (bget bd (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1))))) t)))
            (appendP (collectS (Nat.pow 2 s)
              (bget bd (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1))))) t)) W) kont)
          (t.setNE bd (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1)))))
            (filterS (Nat.pow 2 s)
              (bget bd (Nat.add s (lead (Nat.land H (Nat.xor H (Nat.sub H 1))))) t))))
        (kont t nz W)
        (Nat.beq H 0))
    fuel

/-- bucketed `P[s := R]` (CPS). -/
def substB (M bd : Nat) (lead : Nat → Nat) (van : Nat → Bool) (s : Nat) (R : Poly)
    (t : Tree Poly) (nz : Nat) (kont : Tree Poly → Nat → Bool) : Bool :=
  collB bd s lead 1000000000 (Nat.shiftRight nz s) t nz Poly.nil
    (fun t nz W => insRuns M bd lead 1000000000 (sumB M (mulTerms M van W R)) t nz kont)

/-- MAIN loop on buckets (`fl` = flipped symbols `2x`). -/
def mainLoopB (e : Env) (pr : Pairs) (rules : Tree Poly) (nNets bd : Nat) (lead : Nat → Nat)
    (n : Nat) : Tree Poly → Nat → Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Tree Poly → Nat → Nat → List Nat → Bool)
    (fun t _ _ ws => Bool.rec false (allNil t) (List.rec true (fun _ _ _ => false) ws))
    (fun _ ih t nz fl ws =>
      rd ws false fun op ws =>
        Bool.rec
          (Option.rec false
            (fun R0 =>
              Bool.rec
                (substB e.M bd lead (van pr) (Nat.mul 2 (Nat.shiftRight op 1))
                  (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0) t nz
                  (fun t nz => ih t nz fl ws))
                (substB e.M bd lead (van pr) (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)
                  (oneSub e.M (flipR e.M 100000 (Nat.land (orMonos R0) fl) R0)) t nz
                  (fun t nz => ih t nz fl ws))
                (tb fl (Nat.mul 2 (Nat.shiftRight op 1))))
            (rules.get e.nd (Nat.shiftRight op 1)))
          (Bool.rec
            (substB e.M bd lead (van pr) (Nat.mul 2 (Nat.shiftRight op 1))
              (oneSub e.M
                (single e.M 1 (Nat.pow 2 (Nat.add (Nat.mul 2 (Nat.shiftRight op 1)) 1)))) t nz
              (fun t nz => ih t nz (Nat.lor fl (Nat.pow 2 (Nat.mul 2 (Nat.shiftRight op 1)))) ws))
            false
            (Bool.rec (tb fl (Nat.mul 2 (Nat.shiftRight op 1))) true
              (Nat.ble nNets (Nat.shiftRight op 1))))
          (Nat.beq (Nat.land op 1) 1))
    n

def runPhasesB (e : Env) (signed : Bool) (nNets nG nC nMain nIn : Nat) (inNet outRef : List Nat)
    (ws : List Nat) : Bool :=
  gates e false
    (fun st ws =>
      cones e (fun st ws =>
          insRuns e.M (bitLen (Nat.mul 2 (Nat.succ nNets)))
            (ilogK (bitLen (Nat.mul 2 (Nat.succ nNets)))) 1000000000
            (initP e.M st.pr signed (Nat.shiftRight nIn 1) inNet outRef) Tree.empty 0
            (fun t nz => mainLoopB e st.pr st.rules nNets (bitLen (Nat.mul 2 (Nat.succ nNets)))
              (ilogK (bitLen (Nat.mul 2 (Nat.succ nNets)))) nMain t nz 0 ws))
        nC st ws)
    nG ⟨Tree.empty, ⟨e.nd, Tree.empty, 0⟩⟩ ws

def afterBindB (signed : Bool) (g : Aig) (h : List Nat) (bt : Tree Nat) (ws : List Nat) : Bool :=
  let e : Env := ⟨Nat.pow 2 (nthN h 4), g.M, g.I, bitLen g.M, andTree (bitLen g.M) g.I g.ands,
    bitLen (nthN h 5), bt⟩
  rdN false (nthN h 3) (fun inNet ws => rdN false (nthN h 4) (fun outRef ws =>
      Bool.rec false
        (runPhasesB e signed (nthN h 5) (nthN h 6) (nthN h 7) (nthN h 8) (nthN h 3) inNet outRef ws)
        (Bool.rec false (outOkAll e (nthN h 5) outRef g.outs) (inOk e (nthN h 5) inNet)))
    ws) ws

def checkWordsB (signed : Bool) (g : Aig) (ws0 : List Nat) : Bool :=
  rdN false 10 (fun h ws =>
    Bool.rec false
      (rdN false (nthN h 5) (fun bindW ws =>
          Option.rec false (fun bt => afterBindB signed g h bt ws)
            (bindTree g.M (bitLen (nthN h 5)) (nthN h 5) bindW Tree.empty))
        ws)
      (headerOk signed g h ws0))
    ws0

/-- **The geobucket checker** (same inputs and meaning as `checkArt`). -/
def checkArtB (signed : Bool) (aigN aigLen artN artLen : Nat) : Bool :=
  Option.rec false
    (fun g => Bool.rec false (checkWordsB signed g (toWords artN (Nat.shiftRight artLen 2)))
      (Nat.beq (Nat.land artLen 3) 0))
    (parseAig (toBytes aigN aigLen))

end LeanQbe.T.Examples.Arisca

end
end
