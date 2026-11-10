module

public import spike.a.Core

/-! Spike A examples (body of the old standalone Examples.lean, which inlined Core.lean). -/

set_option autoImplicit false

@[expose] public section

namespace A
set_option Elab.async false

/-! ### (a) loop summing 0..n-1 -/
def sumTo (V : Type) (L : Nat → Type) (n : V) : Expr V L :=
  .let_ (.const 0) fun zero =>
  .let_ (.const 1) fun one =>
  .letRecs [2]
    (fun (loop, ()) =>
      .cons (.param fun i => .param fun acc => .body <|
        .let_ (.ult i n) fun c =>
        .ite c
          (.let_ (.bin .add acc i) fun acc' =>
           .let_ (.bin .add i one) fun i' =>
           .jump loop (i', acc', ()))
          (.ret acc))
      .nil)
    (fun (loop, ()) => .jump loop (zero, zero, ()))

/-! ### (b) even/odd: a two-block mutually recursive group -/
def evenOdd (V : Type) (L : Nat → Type) (n : V) : Expr V L :=
  .let_ (.const 0) fun zero =>
  .let_ (.const 1) fun one =>
  .letRecs [1, 1]
    (fun (even, odd, ()) =>
      .cons (.param fun x => .body <|
        .let_ (.ult zero x) fun c =>
        .ite c (.let_ (.bin .sub x one) fun x' => .jump odd (x', ())) (.ret one)) <|
      .cons (.param fun x => .body <|
        .let_ (.ult zero x) fun c =>
        .ite c (.let_ (.bin .sub x one) fun x' => .jump even (x', ())) (.ret zero))
      .nil)
    (fun (even, _, ()) => .jump even (n, ()))

/-! ### (c) loop with two exits to an outer join point, using an outer variable -/
def twoExit (V : Type) (L : Nat → Type) (n d : V) : Expr V L :=
  .let_ (.const 0) fun zero =>
  .let_ (.const 1) fun one =>
  .let_ (.bin .add d one) fun bias =>           -- bound outside both groups
  .letRecs [1]                                   -- outer join point `done`
    (fun (_, ()) => .cons (.param fun r => .body <|
        .let_ (.bin .add r bias) fun r' => .ret r') .nil)
    fun (done, ()) =>
  .letRecs [1]                                   -- the loop
    (fun (loop, ()) => .cons (.param fun i => .body <|
        .let_ (.ult i n) fun c =>
        .ite c
          (.let_ (.bin .and i bias) fun t =>     -- outer variable used inside the group
           .ite t
             (.jump done (i, ()))                -- exit 1: outer label
             (.let_ (.bin .add i one) fun i' => .jump loop (i', ())))
          (.jump done (zero, ())))               -- exit 2: outer label
      .nil)
    fun (loop, ()) => .jump loop (zero, ())

/-! ### (d) a Lean-level helper used as a macro, twice inside a loop body -/
def absDiff {V : Type} {L : Nat → Type} (a b : V) (k : V → Expr V L) : Expr V L :=
  .let_ (.ult a b) fun c =>
  .letRecs [1] (fun _ => .cons (.param fun r => .body (k r)) .nil) fun (join, ()) =>
  .ite c
    (.let_ (.bin .sub b a) fun d => .jump join (d, ()))
    (.let_ (.bin .sub a b) fun d => .jump join (d, ()))

def macroLoop (V : Type) (L : Nat → Type) (x y : V) : Expr V L :=
  .let_ (.const 0) fun zero =>
  .let_ (.const 1) fun one =>
  .letRecs [2]
    (fun (loop, ()) => .cons (.param fun i => .param fun acc => .body <|
        .let_ (.ult i x) fun c =>
        .ite c
          (absDiff i y fun d1 =>
           absDiff acc d1 fun d2 =>
           .let_ (.bin .add i one) fun i' =>
           .jump loop (i', d2, ()))
          (.ret acc))
      .nil)
    fun (loop, ()) => .jump loop (zero, zero, ())


/-! ## 4. Reification.  Variant 1: `#eval toFlat (prog Nat NL args…) nv 0` and paste the output. -/

-- #eval toFlat (sumTo Nat NL 0) 1 0
def sumTo.flat : Flat :=
A.Flat.let_
  (A.Op.const 0x0000000000000000#64)
  (A.Flat.let_
    (A.Op.const 0x0000000000000001#64)
    (A.Flat.letRecs
      [2]
      (A.FBlocks.cons
        (A.Flat.let_
          (A.Op.ult 3 0)
          (A.Flat.ite
            5
            (A.Flat.let_ (A.Op.bin (A.BinOp.add) 4 3) (A.Flat.let_ (A.Op.bin (A.BinOp.add) 3 2) (A.Flat.jump 0 [7, 6])))
            (A.Flat.ret 4)))
        (A.FBlocks.nil))
      (A.Flat.jump 0 [1, 1])))

-- #eval toFlat (evenOdd Nat NL 0) 1 0
def evenOdd.flat : Flat :=
A.Flat.let_
  (A.Op.const 0x0000000000000000#64)
  (A.Flat.let_
    (A.Op.const 0x0000000000000001#64)
    (A.Flat.letRecs
      [1, 1]
      (A.FBlocks.cons
        (A.Flat.let_
          (A.Op.ult 1 3)
          (A.Flat.ite 4 (A.Flat.let_ (A.Op.bin (A.BinOp.sub) 3 2) (A.Flat.jump 1 [5])) (A.Flat.ret 2)))
        (A.FBlocks.cons
          (A.Flat.let_
            (A.Op.ult 1 3)
            (A.Flat.ite 4 (A.Flat.let_ (A.Op.bin (A.BinOp.sub) 3 2) (A.Flat.jump 0 [5])) (A.Flat.ret 1)))
          (A.FBlocks.nil)))
      (A.Flat.jump 0 [0])))

-- #eval toFlat (twoExit Nat NL 0 1) 2 0
def twoExit.flat : Flat :=
A.Flat.let_
  (A.Op.const 0x0000000000000000#64)
  (A.Flat.let_
    (A.Op.const 0x0000000000000001#64)
    (A.Flat.let_
      (A.Op.bin (A.BinOp.add) 1 3)
      (A.Flat.letRecs
        [1]
        (A.FBlocks.cons (A.Flat.let_ (A.Op.bin (A.BinOp.add) 5 4) (A.Flat.ret 6)) (A.FBlocks.nil))
        (A.Flat.letRecs
          [1]
          (A.FBlocks.cons
            (A.Flat.let_
              (A.Op.ult 5 0)
              (A.Flat.ite
                6
                (A.Flat.let_
                  (A.Op.bin (A.BinOp.and) 5 4)
                  (A.Flat.ite 7 (A.Flat.jump 0 [5]) (A.Flat.let_ (A.Op.bin (A.BinOp.add) 5 3) (A.Flat.jump 1 [8]))))
                (A.Flat.jump 0 [2])))
            (A.FBlocks.nil))
          (A.Flat.jump 1 [2])))))

-- #eval toFlat (macroLoop Nat NL 0 1) 2 0
def macroLoop.flat : Flat :=
A.Flat.let_
  (A.Op.const 0x0000000000000000#64)
  (A.Flat.let_
    (A.Op.const 0x0000000000000001#64)
    (A.Flat.letRecs
      [2]
      (A.FBlocks.cons
        (A.Flat.let_
          (A.Op.ult 4 0)
          (A.Flat.ite
            6
            (A.Flat.let_
              (A.Op.ult 4 1)
              (A.Flat.letRecs
                [1]
                (A.FBlocks.cons
                  (A.Flat.let_
                    (A.Op.ult 5 8)
                    (A.Flat.letRecs
                      [1]
                      (A.FBlocks.cons
                        (A.Flat.let_ (A.Op.bin (A.BinOp.add) 4 3) (A.Flat.jump 0 [11, 10]))
                        (A.FBlocks.nil))
                      (A.Flat.ite
                        9
                        (A.Flat.let_ (A.Op.bin (A.BinOp.sub) 8 5) (A.Flat.jump 2 [10]))
                        (A.Flat.let_ (A.Op.bin (A.BinOp.sub) 5 8) (A.Flat.jump 2 [10])))))
                  (A.FBlocks.nil))
                (A.Flat.ite
                  7
                  (A.Flat.let_ (A.Op.bin (A.BinOp.sub) 1 4) (A.Flat.jump 1 [8]))
                  (A.Flat.let_ (A.Op.bin (A.BinOp.sub) 4 1) (A.Flat.jump 1 [8])))))
            (A.Flat.ret 5)))
        (A.FBlocks.nil))
      (A.Flat.jump 0 [2, 2])))

/-! Variant 1, elaborator `rfl` (Meta.isDefEq, then the kernel re-checks). -/
theorem sumTo_reified :
    @sumTo = fun V L n => denoteTop V L sumTo.flat 1 [n] := rfl
theorem evenOdd_reified :
    @evenOdd = fun V L n => denoteTop V L evenOdd.flat 1 [n] := rfl
theorem twoExit_reified :
    @twoExit = fun V L n d => denoteTop V L twoExit.flat 2 [n, d] := rfl
theorem macroLoop_reified :
    @macroLoop = fun V L x y => denoteTop V L macroLoop.flat 2 [x, y] := rfl

/-! Variant 1, kernel-only (`kernel_rfl` assigns `Eq.refl lhs` unchecked; only the kernel checks). -/
theorem sumTo_reified_k :
    @sumTo = fun V L n => denoteTop V L sumTo.flat 1 [n] := by kernel_rfl
theorem evenOdd_reified_k :
    @evenOdd = fun V L n => denoteTop V L evenOdd.flat 1 [n] := by kernel_rfl
theorem twoExit_reified_k :
    @twoExit = fun V L n d => denoteTop V L twoExit.flat 2 [n, d] := by
  kernel_rfl
theorem macroLoop_reified_k :
    @macroLoop = fun V L x y => denoteTop V L macroLoop.flat 2 [x, y] := by
  kernel_rfl

/-! Variant 2: a small term elaborator normalizes `toFlat …` with `Meta.whnf`
(no compiled code, no paste). `noncomputable` only to skip code generation. -/
noncomputable def sumTo.flatE : Flat := reify% toFlat (sumTo Nat NL 0) 1 0
noncomputable def evenOdd.flatE : Flat := reify% toFlat (evenOdd Nat NL 0) 1 0
noncomputable def twoExit.flatE : Flat := reify% toFlat (twoExit Nat NL 0 1) 2 0
noncomputable def macroLoop.flatE : Flat := reify% toFlat (macroLoop Nat NL 0 1) 2 0

-- the elaborated literal agrees with the pasted one
example : sumTo.flatE = sumTo.flat := rfl
example : evenOdd.flatE = evenOdd.flat := rfl
example : twoExit.flatE = twoExit.flat := rfl
example : macroLoop.flatE = macroLoop.flat := rfl

theorem sumTo_reified_E :
    @sumTo = fun V L n => denoteTop V L sumTo.flatE 1 [n] := rfl
theorem evenOdd_reified_E :
    @evenOdd = fun V L n => denoteTop V L evenOdd.flatE 1 [n] := rfl
theorem twoExit_reified_E :
    @twoExit = fun V L n d => denoteTop V L twoExit.flatE 2 [n, d] := rfl
theorem macroLoop_reified_E :
    @macroLoop = fun V L x y => denoteTop V L macroLoop.flatE 2 [x, y] := rfl
theorem sumTo_reified_Ek :
    @sumTo = fun V L n => denoteTop V L sumTo.flatE 1 [n] := by kernel_rfl
theorem evenOdd_reified_Ek :
    @evenOdd = fun V L n => denoteTop V L evenOdd.flatE 1 [n] := by kernel_rfl
theorem twoExit_reified_Ek :
    @twoExit = fun V L n d => denoteTop V L twoExit.flatE 2 [n, d] := by
  kernel_rfl
theorem macroLoop_reified_Ek :
    @macroLoop = fun V L x y => denoteTop V L macroLoop.flatE 2 [x, y] := by
  kernel_rfl

/-! Variant 3: leave `toFlat (prog Nat NL …)` unreduced; `rfl` / the kernel evaluates it lazily. -/
theorem sumTo_reified_U :
    @sumTo = fun V L n =>
      denoteTop V L (toFlat (sumTo Nat NL 0) 1 0) 1 [n] := rfl
theorem evenOdd_reified_U :
    @evenOdd = fun V L n =>
      denoteTop V L (toFlat (evenOdd Nat NL 0) 1 0) 1 [n] := rfl
theorem twoExit_reified_U :
    @twoExit = fun V L n d =>
      denoteTop V L (toFlat (twoExit Nat NL 0 1) 2 0) 2 [n, d] := rfl
theorem macroLoop_reified_U :
    @macroLoop = fun V L x y =>
      denoteTop V L (toFlat (macroLoop Nat NL 0 1) 2 0) 2 [x, y] := rfl
theorem sumTo_reified_Uk :
    @sumTo = fun V L n =>
      denoteTop V L (toFlat (sumTo Nat NL 0) 1 0) 1 [n] := by kernel_rfl
theorem evenOdd_reified_Uk :
    @evenOdd = fun V L n =>
      denoteTop V L (toFlat (evenOdd Nat NL 0) 1 0) 1 [n] := by kernel_rfl
theorem twoExit_reified_Uk :
    @twoExit = fun V L n d =>
      denoteTop V L (toFlat (twoExit Nat NL 0 1) 2 0) 2 [n, d] := by
  kernel_rfl
theorem macroLoop_reified_Uk :
    @macroLoop = fun V L x y =>
      denoteTop V L (toFlat (macroLoop Nat NL 0 1) 2 0) 2 [x, y] := by
  kernel_rfl

/-! ## 6. Ergonomics: even/odd correctness from S2 in the new encoding -/

def parity (k : Nat) : Val := if k % 2 = 0 then 1 else 0

theorem evenOdd_correct (n : Val) (m : Mem) :
    wp (fun r m' => r = parity n.toNat ∧ m' = m) (evenOdd Val Cont n) m := by
  simp only [evenOdd, wp, Op.wp]
  intro J hJ
  obtain ⟨Je, Jo, _⟩ := J          -- the label tuple is a nested product
  simp only [closedBlocks, closedBlock, wp, Op.wp] at hJ ⊢
  obtain ⟨hE, hO, -⟩ := hJ
  -- invariant: `even` on x returns parity x, `odd` on x returns the opposite
  suffices h : ∀ k : Nat, k < 2 ^ 64 →
      (n.toNat % 2 = k % 2 → Je (BitVec.ofNat 64 k, ()) m) ∧
      (n.toNat % 2 ≠ k % 2 → Jo (BitVec.ofNat 64 k, ()) m) by
    have := (h n.toNat (by omega)).1 rfl
    simpa using this
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun hk => hE _ _ ?_, fun hk => hO _ _ ?_⟩
    · simp [parity]; omega
    · simp [parity]; omega
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    have hsub : BitVec.ofNat 64 (k + 1) - 1#64 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    refine ⟨fun h => hE _ _ ?_, fun h => hO _ _ ?_⟩
    · simp [BinOp.eval]
      refine ⟨fun _ => ?_, fun h0 => by omega⟩
      rw [hsub]; exact ih.2 (by omega)      -- rewriting under the block argument
    · simp [BinOp.eval]
      refine ⟨fun _ => ?_, fun h0 => by omega⟩
      rw [hsub]; exact ih.1 (by omega)

#print axioms wp_mono
#print axioms evenOdd_correct
#print axioms sumTo_reified
#print axioms sumTo_reified_k
#print axioms macroLoop_reified_k
#print axioms macroLoop_reified_Uk

end A
