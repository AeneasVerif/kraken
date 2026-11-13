module

public import LeanQbe.Fold
public import LeanQbe.WfLemmas
import LeanQbe.OpsLemmas

/-!
# Correctness of `fold` (constant folding, copy propagation, algebraic rules, strength reduction)

* `fold_wp`: the source `wp` implies the `wp` of the output. Read the input at `V' := FVal Val` next to
  the source at `Val`, related by `Wf` with `FGood ρ b G` (every input variable denotes an operand and key
  whose values equal the source variable's value) and equal labels.
* `fold_wf`: `Wf` is preserved; so the output can be fed to the next pass or to the lowering.
* `Func.fold_spec`, `Func.fold_wf`: the same for closed functions.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

def SimpAct.val (va vb : Val) : SimpAct → Val
  | .imm c => c
  | .fst => va
  | .snd => vb

/-! ## Soundness of `cmpAct`, `binAct`, and `Op.rewrite` -/

theorem cmpOp_eval_self {n : Nat} (o : CmpOp) (v : BitVec n) : o.eval v v = o.isRefl := by
  cases o <;> grind [CmpOp.eval, CmpOp.isRefl]

theorem cmpAct_eval {k : Cls} {o : CmpOp} {eqKey : Bool} {va vb : Val} {act : SimpAct}
    (heq : eqKey = true → va = vb) (h : cmpAct k o eqKey = some act) :
    (Op.cmp k o (.imm va) (.imm vb)).eval = some (act.val va vb) := by
  cases k <;> grind [cmpAct, Op.eval, cmpOp_eval_self, SimpAct.val, Arg.val]

theorem binAct_eval {k : Cls} {o : BinOp} {ai bi : Option Val} {eqKey : Bool} {va vb : Val}
    {act : SimpAct} (hai : ∀ c, ai = some c → va = c) (hbi : ∀ c, bi = some c → vb = c)
    (heq : eqKey = true → va = vb) (h : binAct k o ai bi eqKey = some act) :
    (Op.bin k o (.imm va) (.imm vb)).eval = some (act.val va vb) := by
  cases o <;> cases k <;>
    grind [binAct, Op.eval, BinOp.eval, SimpAct.val, Arg.val, Option.some_inj]

theorem findPow2_spec {w : Nat} {x : BitVec w} :
    ∀ {limit m : Nat}, findPow2 w x limit = some m → m < limit ∧ x = BitVec.twoPow w m
  | 0, _, h => by simp [findPow2] at h
  | l + 1, m, h => by
    simp only [findPow2] at h
    split at h
    · next hx => cases h; exact ⟨Nat.lt_succ_self l, hx⟩
    · obtain ⟨hm, hx⟩ := findPow2_spec h
      exact ⟨Nat.lt_succ_of_lt hm, hx⟩

theorem pow2Shift?_eval_r {k : Cls} {c m : Val} (a : Arg Val) (h : pow2Shift? k c = some m) :
    (Op.bin k .shl a (.imm m)).eval = (Op.bin k .mul a (.imm c)).eval := by
  cases k with
  | l =>
    simp only [pow2Shift?, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hilt, rfl⟩ := findPow2_spec hi
    have hm : (BitVec.ofNat 64 i).toNat % 64 = i := by
      simp [BitVec.toNat_ofNat]; omega
    simp only [Op.eval, BinOp.eval, Arg.val, hm, BitVec.shiftLeft_eq_mul_twoPow]
  | w =>
    simp only [pow2Shift?, Option.map_eq_some_iff] at h
    obtain ⟨i, hi, rfl⟩ := h
    obtain ⟨hilt, hlo⟩ := findPow2_spec hi
    have hm : (lo32 (BitVec.ofNat 64 i)).toNat % 32 = i := by
      simp [lo32, BitVec.toNat_ofNat]; omega
    simp only [Op.eval, BinOp.eval, Arg.val, hm, hlo, BitVec.shiftLeft_eq_mul_twoPow]

theorem pow2Shift?_eval_l {k : Cls} {c m : Val} (b : Arg Val) (h : pow2Shift? k c = some m) :
    (Op.bin k .shl b (.imm m)).eval = (Op.bin k .mul (.imm c) b).eval := by
  rw [pow2Shift?_eval_r b h]
  cases k <;> simp [Op.eval, BinOp.eval, Arg.val, BitVec.mul_comm]

theorem Arg.imm?_eq_some {a : Arg Val} {c : Val} (h : a.imm? = some c) : a.val = c := by
  cases a <;> simp_all [Arg.imm?]

theorem lo32_allOnes : lo32 (BitVec.allOnes 64) = BitVec.allOnes 32 := by decide

theorem rewriteMul_eval (k : Cls) (a b : Arg Val) :
    (rewriteMul k a b).eval = (Op.bin k .mul a b).eval := by
  unfold rewriteMul
  cases b with
  | imm c =>
    dsimp only [Arg.imm?, Option.bind]
    cases hp : pow2Shift? k c with
    | some m => exact pow2Shift?_eval_r a hp
    | none =>
      dsimp only
      cases a with
      | imm c' =>
        dsimp only [Arg.imm?, Option.bind]
        cases hp' : pow2Shift? k c' with
        | some m => exact pow2Shift?_eval_l (.imm c) hp'
        | none => rfl
      | var _ => rfl
  | var v =>
    dsimp only [Arg.imm?, Option.bind]
    cases a with
    | imm c' =>
      dsimp only [Arg.imm?, Option.bind]
      cases hp' : pow2Shift? k c' with
      | some m => exact pow2Shift?_eval_l (.var v) hp'
      | none => rfl
    | var _ => rfl

theorem rewriteBin_eval (k : Cls) (o : BinOp) (a b : Arg Val) :
    (rewriteBin k o a b).eval = (Op.bin k o a b).eval := by
  unfold rewriteBin
  cases k with
  | l =>
    cases o <;> try rfl
    exact rewriteMul_eval .l a b
  | w =>
    cases o with
    | add =>
      simp only [beq_iff_eq]
      split
      · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
      · split
        · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
        · rfl
    | sub =>
      simp only [beq_iff_eq]
      split
      · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
      · rfl
    | or =>
      simp only [beq_iff_eq]
      split
      · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
      · split
        · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
        · rfl
    | xor =>
      simp only [beq_iff_eq]
      split
      · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
      · split
        · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
        · rfl
    | and =>
      simp only [beq_iff_eq]
      split
      · next h =>
        rw [Op.eval_copy]
        simp only [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h, lo32_allOnes,
          BitVec.and_allOnes, Option.map]
      · split
        · next h =>
          rw [Op.eval_copy]
          simp only [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h, lo32_allOnes,
            BitVec.allOnes_and, Option.map]
        · rfl
    | shl | shr | sar =>
      simp only [beq_iff_eq]
      split
      · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
      · rfl
    | mul =>
      simp only [beq_iff_eq]
      split
      · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
      · split
        · next h => rw [Op.eval_copy]; simp [Op.eval, BinOp.eval, Cls.trunc, Arg.imm?_eq_some h]
        · exact rewriteMul_eval .w a b
    | div | rem | udiv | urem => rfl

theorem Op.rewrite_eval (o : Op Val) : o.rewrite.eval = o.eval := by
  cases o with
  | bin k op a b => exact rewriteBin_eval k op a b
  | cmp k op a b => rfl
  | copy k a => rfl
  | ext k s sg a =>
    cases k <;> cases s <;> cases sg <;>
      grind [Op.rewrite, Op.eval, Cls.trunc, Sz.extend, Option.some_inj]

/-! ## Context invariants and `OpRel` lemmas for `fold` -/

def Arg.fev (ρ : Nat → Val) : FKey → Val
  | .var i => ρ i
  | .imm c => c

def Arg.FLt (b : Nat) : FKey → Prop
  | .var i => i < b
  | .imm _ => True

def fupd (ρ : Nat → Val) (b : Nat) (v : Val) : Nat → Val := fun i => if i = b then v else ρ i

theorem Arg.FLt.mono {b : Nat} {κ : FKey} (h : κ.FLt b) : κ.FLt (b + 1) := by
  cases κ with
  | var i => exact Nat.lt_succ_of_lt h
  | imm _ => trivial

theorem Arg.fev_fupd {ρ : Nat → Val} {b : Nat} {v : Val} {κ : FKey} (h : κ.FLt b) :
    κ.fev (fupd ρ b v) = κ.fev ρ := by
  cases κ <;> grind [Arg.fev, fupd, Arg.FLt]

/-- Every input variable denotes an operand and a key with the source value. -/
def FGood (ρ : Nat → Val) (b : Nat) (G : List (FVal Val × Val)) : Prop :=
  ∀ p ∈ G, p.1.1.val = p.2 ∧ p.1.2.fev ρ = p.2 ∧ p.1.2.FLt b

theorem FGood.cons {ρ : Nat → Val} {b : Nat} {G : List (FVal Val × Val)} (hG : FGood ρ b G)
    {r : FVal Val} {v : Val} (h1 : r.1.val = v) (h2 : r.2.fev ρ = v) (h3 : r.2.FLt b) :
    FGood ρ b ((r, v) :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨h1, h2, h3⟩
  | tail _ hp => exact hG p hp

theorem FGood.upd {ρ : Nat → Val} {b : Nat} {G : List (FVal Val × Val)} (hG : FGood ρ b G)
    (v : Val) : FGood (fupd ρ b v) (b + 1) G := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hG p hp
  exact ⟨h1, (Arg.fev_fupd h3).trans h2, h3.mono⟩

theorem FGood.fresh {ρ : Nat → Val} {b : Nat} {G : List (FVal Val × Val)} (hG : FGood ρ b G)
    (v : Val) : FGood (fupd ρ b v) (b + 1) (((.var v, .var b), v) :: G) :=
  (hG.upd v).cons rfl (by simp [Arg.fev, fupd]) (Nat.lt_succ_self b)

section
variable {G : List (FVal Val × Val)} {ρ : Nat → Val} {b : Nat}

theorem ArgRel.fout_val (hG : FGood ρ b G) {a₁ : Arg (FVal Val)} {a₂ : Arg Val} :
    ArgRel G a₁ a₂ → a₁.fout.val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem ArgRel.fkey_ev (hG : FGood ρ b G) {a₁ : Arg (FVal Val)} {a₂ : Arg Val} :
    ArgRel G a₁ a₂ → a₁.fkey.fev ρ = a₂.val
  | .var h => (hG _ h).2.1
  | .imm _ => rfl

theorem ArgRel.fkey_lt (hG : FGood ρ b G) {a₁ : Arg (FVal Val)} {a₂ : Arg Val} :
    ArgRel G a₁ a₂ → a₁.fkey.FLt b
  | .var h => (hG _ h).2.2
  | .imm _ => trivial

theorem ArgRel.fpair_good (hG : FGood ρ b G) {a₁ : Arg (FVal Val)} {a₂ : Arg Val}
    (h : ArgRel G a₁ a₂) :
    a₁.fpair.1.val = a₂.val ∧ a₁.fpair.2.fev ρ = a₁.fpair.1.val ∧ a₁.fpair.2.FLt b :=
  ⟨h.fout_val hG, (h.fkey_ev hG).trans (h.fout_val hG).symm, h.fkey_lt hG⟩

theorem Forall₂.fout_vals (hG : FGood ρ b G) :
    ∀ {as₁ : List (Arg (FVal Val))} {as₂ : List (Arg Val)}, Forall₂ (ArgRel G) as₁ as₂ →
      (as₁.map Arg.fout).map Arg.val = as₂.map Arg.val
  | _, _, .nil => rfl
  | _, _, .cons h hs => by simp only [List.map_cons, h.fout_val hG, Forall₂.fout_vals hG hs]

theorem OpRel.fout_eval (hG : FGood ρ b G) {o₁ : Op (FVal Val)} {o₂ : Op Val}
    (h : OpRel G o₁ o₂) : (o₁.mapArgs Arg.fout).eval = o₂.eval := by
  cases h with
  | bin k o ha hb =>
    cases k <;> simp only [Op.mapArgs, Op.eval, ha.fout_val hG, hb.fout_val hG]
  | cmp k o ha hb =>
    cases k <;> simp only [Op.mapArgs, Op.eval, ha.fout_val hG, hb.fout_val hG]
  | ext k s sg ha => simp only [Op.mapArgs, Op.eval, ha.fout_val hG]
  | copy k ha => simp only [Op.mapArgs, Op.eval, ha.fout_val hG]

end

theorem Op.constVal?_eval {o : Op Val} {c : Val} (h : o.constVal? = some c) : o.eval = some c := by
  cases o with
  | bin k o a b => cases a <;> cases b <;> simp_all [Op.constVal?, Op.toImm?, Arg.imm?]
  | cmp k o a b => cases a <;> cases b <;> simp_all [Op.constVal?, Op.toImm?, Arg.imm?]
  | ext k s sg a => cases a <;> simp_all [Op.constVal?, Op.toImm?, Arg.imm?]
  | copy k a => cases a <;> simp_all [Op.constVal?, Op.toImm?, Arg.imm?]

theorem Op.copyL?_eval {o : Op Val} {a : Arg Val} (h : o.copyL? = some a) : o.eval = some a.val := by
  cases o with
  | copy k a' => cases k <;> simp_all [Op.copyL?, Op.eval, Cls.trunc]
  | _ => simp [Op.copyL?] at h

theorem OpRel.simpAct_eval {G : List (FVal Val × Val)} {ρ : Nat → Val} {b : Nat} (hG : FGood ρ b G)
    {op₁ : Op (FVal Val)} {op₂ : Op Val} (ho : OpRel G op₁ op₂) {act : SimpAct}
    (h : op₁.simpAct = some act) :
    let r := act.apply op₁
    op₂.eval = some r.1.val ∧ r.2.fev ρ = r.1.val ∧ r.2.FLt b := by
  unfold Op.simpAct at h
  cases hc : (op₁.mapArgs Arg.fout).constVal? with
  | some c =>
    rw [hc] at h
    cases h
    have he := (ho.fout_eval hG).symm.trans (Op.constVal?_eval hc)
    exact ⟨he, rfl, trivial⟩
  | none =>
    rw [hc] at h
    dsimp only at h
    cases ho with
    | @bin k o a₁ b₁ a₂ b₂ ha hb =>
      have hai : ∀ c, a₁.fout.imm? = some c → a₂.val = c := fun c hc =>
        (ha.fout_val hG).symm.trans (Arg.imm?_eq_some hc)
      have hbi : ∀ c, b₁.fout.imm? = some c → b₂.val = c := fun c hc =>
        (hb.fout_val hG).symm.trans (Arg.imm?_eq_some hc)
      have heq : (a₁.fkey == b₁.fkey) = true → a₂.val = b₂.val := fun hk => by
        have hk' : a₁.fkey = b₁.fkey := eq_of_beq hk
        exact (ha.fkey_ev hG).symm.trans (hk' ▸ hb.fkey_ev hG)
      have hev := binAct_eval hai hbi heq h
      have hev' : (Op.bin k o a₂ b₂).eval = (Op.bin k o (.imm a₂.val) (.imm b₂.val)).eval := by
        cases k <;> rfl
      cases act with
      | imm c => exact ⟨hev'.trans hev, rfl, trivial⟩
      | fst =>
        obtain ⟨h1, h2, h3⟩ := ha.fpair_good hG
        dsimp only [SimpAct.apply, Op.firstArg]
        rw [h1] at h2 ⊢
        exact ⟨hev'.trans hev, h2, h3⟩
      | snd =>
        obtain ⟨h1, h2, h3⟩ := hb.fpair_good hG
        dsimp only [SimpAct.apply, Op.secondArg]
        rw [h1] at h2 ⊢
        exact ⟨hev'.trans hev, h2, h3⟩
    | @cmp k o a₁ b₁ a₂ b₂ ha hb =>
      have heq : (a₁.fkey == b₁.fkey) = true → a₂.val = b₂.val := fun hk => by
        have hk' : a₁.fkey = b₁.fkey := eq_of_beq hk
        exact (ha.fkey_ev hG).symm.trans (hk' ▸ hb.fkey_ev hG)
      have hev := cmpAct_eval heq h
      have hev' : (Op.cmp k o a₂ b₂).eval = (Op.cmp k o (.imm a₂.val) (.imm b₂.val)).eval := by
        cases k <;> rfl
      simp only [cmpAct] at h
      split at h
      · cases h; exact ⟨hev'.trans hev, rfl, trivial⟩
      · contradiction
    | @ext k s sg a₁ a₂ ha =>
      cases k <;> cases s <;> simp only [extAct, reduceCtorEq] at h
      cases h
      obtain ⟨h1, h2, h3⟩ := ha.fpair_good hG
      dsimp only [SimpAct.apply, Op.firstArg]
      exact ⟨by simp [Op.eval, Cls.trunc, Sz.extend, h1], h2, h3⟩
    | @copy k a₁ a₂ ha =>
      cases k <;> simp only [copyAct, reduceCtorEq] at h
      cases h
      obtain ⟨h1, h2, h3⟩ := ha.fpair_good hG
      dsimp only [SimpAct.apply, Op.firstArg]
      exact ⟨by simp [Op.eval, Cls.trunc, h1], h2, h3⟩

/-! ## `Wf` relations for `fold` -/

section
variable {V₁ V₂ : Type}

def FRelG (G' : List (V₁ × V₂)) (G : List (FVal V₁ × FVal V₂)) : Prop :=
  ∀ p ∈ G, ArgRel G' p.1.1 p.2.1 ∧ p.1.2 = p.2.2

variable {G' : List (V₁ × V₂)} {G : List (FVal V₁ × FVal V₂)}

theorem FRelG.cons (hG : FRelG G' G) {r₁ : FVal V₁} {r₂ : FVal V₂} (h1 : ArgRel G' r₁.1 r₂.1)
    (h2 : r₁.2 = r₂.2) : FRelG G' ((r₁, r₂) :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨h1, h2⟩
  | tail _ hp => exact hG p hp

theorem FRelG.fresh (hG : FRelG G' G) (v₁ : V₁) (v₂ : V₂) (b : Nat) :
    FRelG ((v₁, v₂) :: G') (((.var v₁, .var b), (.var v₂, .var b)) :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨.var (List.Mem.head _), rfl⟩
  | tail _ hp =>
    obtain ⟨h1, h2⟩ := hG p hp
    exact ⟨h1.weaken fun _ hq => List.Mem.tail _ hq, h2⟩

theorem ArgRel.imm?_eq {a₁ : Arg V₁} {a₂ : Arg V₂} :
    ArgRel G' a₁ a₂ → a₁.imm? = a₂.imm?
  | .var _ => rfl
  | .imm _ => rfl

theorem OpRel.toImm?_eq {o₁ : Op V₁} {o₂ : Op V₂} (h : OpRel G' o₁ o₂) :
    o₁.toImm? = o₂.toImm? := by
  cases h with
  | bin k o ha hb => simp only [Op.toImm?, ha.imm?_eq, hb.imm?_eq]
  | cmp k o ha hb => simp only [Op.toImm?, ha.imm?_eq, hb.imm?_eq]
  | ext k s sg ha => simp only [Op.toImm?, ha.imm?_eq]
  | copy k ha => simp only [Op.toImm?, ha.imm?_eq]

theorem OpRel.constVal?_eq {o₁ : Op V₁} {o₂ : Op V₂} (h : OpRel G' o₁ o₂) :
    o₁.constVal? = o₂.constVal? := by
  simp only [Op.constVal?, h.toImm?_eq]

theorem ArgRel.fkey_eq (hG : FRelG G' G) {a₁ : Arg (FVal V₁)} {a₂ : Arg (FVal V₂)} :
    ArgRel G a₁ a₂ → a₁.fkey = a₂.fkey
  | .var h => (hG _ h).2
  | .imm _ => rfl

theorem ArgRel.fout (hG : FRelG G' G) {a₁ : Arg (FVal V₁)} {a₂ : Arg (FVal V₂)} :
    ArgRel G a₁ a₂ → ArgRel G' a₁.fout a₂.fout
  | .var h => (hG _ h).1
  | .imm c => .imm c

theorem Forall₂.fout (hG : FRelG G' G) :
    ∀ {as₁ as₂}, Forall₂ (ArgRel G) as₁ as₂ → Forall₂ (ArgRel G') (as₁.map Arg.fout) (as₂.map Arg.fout)
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (h.fout hG) (Forall₂.fout hG hs)

theorem OpRel.fout (hG : FRelG G' G) {o₁ : Op (FVal V₁)} {o₂ : Op (FVal V₂)} :
    OpRel G o₁ o₂ → OpRel G' (o₁.mapArgs Arg.fout) (o₂.mapArgs Arg.fout)
  | .bin k o ha hb => .bin k o (ha.fout hG) (hb.fout hG)
  | .cmp k o ha hb => .cmp k o (ha.fout hG) (hb.fout hG)
  | .ext k s sg ha => .ext k s sg (ha.fout hG)
  | .copy k ha => .copy k (ha.fout hG)

theorem OpRel.simpAct_eq (hG : FRelG G' G) {o₁ : Op (FVal V₁)} {o₂ : Op (FVal V₂)}
    (ho : OpRel G o₁ o₂) : o₁.simpAct = o₂.simpAct := by
  have hc := (ho.fout hG).constVal?_eq
  unfold Op.simpAct
  rw [hc]
  cases (o₂.mapArgs Arg.fout).constVal? with
  | some _ => rfl
  | none =>
    cases ho with
    | bin k o ha hb =>
      simp only [(ha.fout hG).imm?_eq, (hb.fout hG).imm?_eq, ha.fkey_eq hG, hb.fkey_eq hG]
    | cmp k o ha hb =>
      simp only [ha.fkey_eq hG, hb.fkey_eq hG]
    | ext _ _ _ _ => rfl
    | copy _ _ => rfl

theorem OpRel.apply_rel (hG : FRelG G' G) {o₁ : Op (FVal V₁)} {o₂ : Op (FVal V₂)}
    (ho : OpRel G o₁ o₂) (act : SimpAct) :
    ArgRel G' (act.apply o₁).1 (act.apply o₂).1 ∧ (act.apply o₁).2 = (act.apply o₂).2 := by
  cases act with
  | imm c => exact ⟨.imm c, rfl⟩
  | fst =>
    cases ho with
    | bin _ _ ha _ | cmp _ _ ha _ | ext _ _ _ ha | copy _ ha =>
      exact ⟨ha.fout hG, ha.fkey_eq hG⟩
  | snd =>
    cases ho with
    | bin _ _ _ hb | cmp _ _ _ hb => exact ⟨hb.fout hG, hb.fkey_eq hG⟩
    | ext _ _ _ ha | copy _ ha => exact ⟨ha.fout hG, ha.fkey_eq hG⟩

theorem OpRel.rewriteMul (k : Cls) {a₁ b₁ : Arg V₁} {a₂ b₂ : Arg V₂}
    (ha : ArgRel G' a₁ a₂) (hb : ArgRel G' b₁ b₂) :
    OpRel G' (LeanQbe.rewriteMul k a₁ b₁) (LeanQbe.rewriteMul k a₂ b₂) := by
  unfold LeanQbe.rewriteMul
  rw [ha.imm?_eq, hb.imm?_eq]
  cases b₂.imm?.bind (pow2Shift? k) with
  | some m => exact .bin k .shl ha (.imm m)
  | none =>
    cases a₂.imm?.bind (pow2Shift? k) with
    | some m => exact .bin k .shl hb (.imm m)
    | none => exact .bin k .mul ha hb

theorem OpRel.rewriteBin (k : Cls) (o : BinOp) {a₁ b₁ : Arg V₁} {a₂ b₂ : Arg V₂}
    (ha : ArgRel G' a₁ a₂) (hb : ArgRel G' b₁ b₂) :
    OpRel G' (LeanQbe.rewriteBin k o a₁ b₁) (LeanQbe.rewriteBin k o a₂ b₂) := by
  cases k with
  | l =>
    cases o <;> simp only [LeanQbe.rewriteBin] <;>
      first | exact .bin .l _ ha hb | exact OpRel.rewriteMul .l ha hb
  | w =>
    cases o <;> simp only [LeanQbe.rewriteBin, ha.imm?_eq, hb.imm?_eq] <;>
      repeat (first
        | split
        | exact .copy .w ha
        | exact .copy .w hb
        | exact .bin .w _ ha hb
        | exact OpRel.rewriteMul .w ha hb)

theorem OpRel.rewrite {o₁ : Op V₁} {o₂ : Op V₂} (ho : OpRel G' o₁ o₂) :
    OpRel G' o₁.rewrite o₂.rewrite := by
  cases ho with
  | bin k o ha hb => exact OpRel.rewriteBin k o ha hb
  | cmp k o ha hb => exact .cmp k o ha hb
  | copy k ha => exact .copy k ha
  | ext k s sg ha =>
    cases k <;> cases s <;> cases sg <;> first | exact .copy .w ha | exact .ext _ _ _ ha

end

/-! ## `wp` preservation and `Wf` preservation -/

theorem fold_wp {Γ : Env} {Q : Post} {X : XPost} :
    ∀ {G : List (FVal Val × Val)} {D : List (Cont × Cont)} {e₁ : Expr (FVal Val) Cont}
      {e₂ : Expr Val Cont}, Wf G D e₁ e₂ → (∀ p ∈ D, p.1 = p.2) →
    ∀ n b ρ, FGood ρ b G →
    ∀ args acc m, acc.length = n → wp Γ Q X e₂ args acc m → wp Γ Q X (fold n b e₁) args acc m := by
  intro G D e₁ e₂ h
  induction h with
  | @let_ G D op₁ op₂ k₁ k₂ ho _ ih =>
    intro hD n b ρ hG args acc m hn hw
    simp only [wp, Op.wp] at hw
    obtain ⟨rfl, v, hv, hk⟩ := hw
    have he : (op₁.mapArgs Arg.fout).rewrite.eval = op₂.eval :=
      (Op.rewrite_eval _).trans (ho.fout_eval hG)
    have miss : wp Γ Q X (.let_ (op₁.mapArgs Arg.fout).rewrite fun v' =>
        fold 0 (b + 1) (k₁ (.var v', .var b))) [] acc m :=
      ⟨rfl, v, he ▸ hv, ih (.var v, .var b) v hD 0 (b + 1) (fupd ρ b v) (hG.fresh v) [] [] m rfl hk⟩
    unfold fold
    split
    · next hn0 =>
      subst hn0
      have : acc = [] := List.eq_nil_of_length_eq_zero hn
      subst this
      split
      · next act hact =>
        obtain ⟨h1, h2, h3⟩ := ho.simpAct_eval hG hact
        have hvr : v = (act.apply op₁).1.val := Option.some.inj (hv.symm.trans h1)
        subst hvr
        exact ih (act.apply op₁) (act.apply op₁).1.val hD 0 b ρ (hG.cons rfl h2 h3) [] [] m rfl hk
      · exact miss
    · exact miss
  | load c s sg ha _ ih =>
    intro hD n b ρ hG args acc m _ hw
    simp only [wp, fold] at hw ⊢
    obtain ⟨rfl, v, hv, hk⟩ := hw
    exact ⟨rfl, v, ha.fout_val hG ▸ hv,
      ih (.var v, .var b) v hD 0 (b + 1) (fupd ρ b v) (hG.fresh v) [] [] m rfl hk⟩
  | store s hv ha _ ih =>
    intro hD n b ρ hG args acc m _ hw
    simp only [wp, fold] at hw ⊢
    obtain ⟨rfl, hok, hk⟩ := hw
    rw [ha.fout_val hG, hv.fout_val hG]
    exact ⟨rfl, hok, ih hD 0 b ρ hG [] [] _ rfl hk⟩
  | call f has _ ih =>
    intro hD n b ρ hG args acc m _ hw
    simp only [wp, fold] at hw ⊢
    obtain ⟨rfl, P, E, hΓ, hP, hE⟩ := hw
    rw [has.fout_vals hG]
    exact ⟨rfl, P, E, hΓ, fun rs m' hp => ih hD 0 b ρ hG rs [] m' rfl (hP rs m' hp), hE⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro hD n b ρ hG args acc m hn hw
    simp only [wp] at hw
    obtain ⟨rfl, ht, he⟩ := hw
    have hcv := hc.fout_val hG
    unfold fold
    split
    · next hn0 =>
      subst hn0
      have : acc = [] := List.eq_nil_of_length_eq_zero hn
      subst this
      split
      · next c hcj =>
        rw [hcj] at hcv
        have hc2 : c = c₂.val := hcv
        grind
      · next v hcj =>
        have hcv' : (Arg.var v : Arg Val).val = c₂.val := hcj ▸ hcv
        exact ⟨rfl, fun h => iht hD 0 b ρ hG [] [] m rfl (ht (hcv' ▸ h)),
          fun h => ihe hD 0 b ρ hG [] [] m rfl (he (hcv' ▸ h))⟩
    · exact ⟨rfl, fun h => iht hD 0 b ρ hG [] [] m rfl (ht (hcv ▸ h)),
        fun h => ihe hD 0 b ρ hG [] [] m rfl (he (hcv ▸ h))⟩
  | jump hj has =>
    intro hD n b ρ hG args acc m _ hw
    simp only [wp, fold] at hw ⊢
    have hj' := hD _ hj
    simp only at hj'
    subst hj'
    rw [has.fout_vals hG]
    exact hw
  | ret has =>
    intro _ n b ρ hG args acc m _ hw
    simp only [wp, fold] at hw ⊢
    rw [has.fout_vals hG]
    exact hw
  | exit f has =>
    intro _ n b ρ hG args acc m _ hw
    simp only [wp, fold] at hw ⊢
    rw [has.fout_vals hG]
    exact hw
  | hlt => intro _ _ _ _ _ _ _ _ _ hw; simp only [wp] at hw
  | param _ ih =>
    intro hD n b ρ hG args acc m _ hw
    cases args with
    | nil => simp only [wp] at hw
    | cons a as =>
      simp only [wp, fold] at hw ⊢
      exact ih (.var a, .var b) a hD 0 (b + 1) (fupd ρ b a) (hG.fresh a) as [] m rfl hw
  | label _ ih =>
    intro hD n b ρ hG args acc m hn hw
    simp only [wp, fold] at hw ⊢
    grind
  | block _ _ ihb ihr =>
    intro hD n b ρ hG args acc m hn hw
    cases acc with
    | nil => simp only [wp, and_false] at hw
    | cons J acc' =>
      simp only [wp, fold] at hw ⊢
      grind

theorem fold_wf {V₁ V₂ L₁ L₂ : Type} :
    ∀ {G : List (FVal V₁ × FVal V₂)} {D : List (L₁ × L₂)} {e₁ : Expr (FVal V₁) L₁}
      {e₂ : Expr (FVal V₂) L₂}, Wf G D e₁ e₂ →
    ∀ {G' : List (V₁ × V₂)}, FRelG G' G → ∀ n b, Wf G' D (fold n b e₁) (fold n b e₂) := by
  intro G D e₁ e₂ h
  induction h with
  | @let_ G D op₁ op₂ k₁ k₂ ho _ ih =>
    intro G' hG n b
    have ho' := (ho.fout hG).rewrite
    have hact := ho.simpAct_eq hG
    simp only [fold]
    rw [hact]
    split
    · cases op₂.simpAct with
      | some act =>
        obtain ⟨h1, h2⟩ := ho.apply_rel hG act
        exact ih _ _ (hG.cons h1 h2) 0 b
      | none => exact .let_ ho' fun v₁ v₂ => ih _ _ (hG.fresh v₁ v₂ b) 0 (b + 1)
    · exact .let_ ho' fun v₁ v₂ => ih _ _ (hG.fresh v₁ v₂ b) 0 (b + 1)
  | load c s sg ha _ ih =>
    intro G' hG n b
    exact .load c s sg (ha.fout hG) fun v₁ v₂ => ih _ _ (hG.fresh v₁ v₂ b) 0 (b + 1)
  | store s hv ha _ ih =>
    intro G' hG n b; exact .store s (hv.fout hG) (ha.fout hG) (ih hG 0 b)
  | call f has _ ih => intro G' hG n b; exact .call f (has.fout hG) (ih hG 0 b)
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro G' hG n b
    have hc' := hc.fout hG
    simp only [fold]
    split
    · cases hc with
      | @var p₁ p₂ h =>
        rcases p₁ with ⟨a₁, κ₁⟩
        rcases p₂ with ⟨a₂, κ₂⟩
        obtain ⟨h', _⟩ := hG _ h
        simp only [Arg.fout] at h' ⊢
        cases h' with
        | var h'' => exact .jnz (.var h'') (iht hG 0 b) (ihe hG 0 b)
        | imm c => dsimp only; split <;> first | exact iht hG 0 b | exact ihe hG 0 b
      | imm c => dsimp only [Arg.fout]; split <;> first | exact iht hG 0 b | exact ihe hG 0 b
    · exact .jnz hc' (iht hG 0 b) (ihe hG 0 b)
  | jump hj has => intro G' hG n b; exact .jump hj (has.fout hG)
  | ret has => intro G' hG n b; exact .ret (has.fout hG)
  | exit f has => intro G' hG n b; exact .exit f (has.fout hG)
  | hlt => intro _ _ _ _; exact .hlt
  | param _ ih => intro G' hG n b; exact .param fun v₁ v₂ => ih _ _ (hG.fresh v₁ v₂ b) 0 (b + 1)
  | label _ ih => intro G' hG n b; exact .label fun j₁ j₂ => ih j₁ j₂ hG (n + 1) b
  | block _ _ ihb ihr => intro G' hG n b; exact .block (ihb hG 0 b) (ihr hG (n - 1) b)

/-! ## Closed functions -/

theorem Func.fold_wf {f : Func} (hf : f.Wf) : (Func.fold f).Wf :=
  fun V₁ V₂ L₁ L₂ => LeanQbe.fold_wf (hf (FVal V₁) (FVal V₂) L₁ L₂) (fun _ hp => nomatch hp) 0 0

/-- Folding refines the contract: every run of the source satisfying `Q` / `X` is matched. -/
theorem Func.fold_spec {f : Func} (hf : f.Wf) {Γ : Env} {args : List Val} {m : Mem 64}
    {Q : Post} {X : XPost} (h : Func.spec Γ f args m Q X) : Func.spec Γ (Func.fold f) args m Q X :=
  LeanQbe.fold_wp (hf (FVal Val) Val Cont Cont) (fun _ hp => nomatch hp) 0 0 (fun _ => 0)
    (fun _ hp => nomatch hp) args [] m rfl h

end LeanQbe
