module

public import LeanQbe.T.LeanLCNF.Sem.LowerSound1c
import LeanQbe.T.OpsLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.LeanLCNF.Sem.SpecNormProof

/-!
# Tier-H Primitive Lowering Infrastructure & `tagBin` (`LowerSound2`)

Provides `EvalWordArg`/`EvalWordArgs`, pure bitvector helpers for tagged-fixnum arithmetic and
uint shifts, `LMMono` monotonicity lemmas for `tagBin`/`natBin`/`natPrim`, runtime bridges for
`lcnf_nat_slow` and `lcnf_nat_to_str`, and the `tagBin_wp` / `tagBin_cmp_wp` simulation lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0
open Std.ExtHashMap

/-! ## 1. Argument Evaluation Bridges & Pure Bitvector Lemmas -/

/-- Zero-extend a `Word` bitvector payload to 64 bits. -/
@[expose] def Word.zext64 : Word → BitVec 64
  | ⟨.bits _, v⟩ => v.setWidth 64
  | _ => 0#64

/-- Single lowered `LArg` matching a Tier-H `Word` at its exact bit width. -/
@[expose] def EvalWordArg (ρ : Frontend.C0.VEnv) (a : LArg) (w : Word) : Prop :=
  ∃ (bw : Nat) (bv : BitVec bw),
    bw = argBitsWidth a ∧ w = ⟨.bits bw, bv⟩ ∧ LArg.eval ρ (.bits bw) a = some bv

/-- List of lowered `LArg`s matching Tier-H `Word`s pointwise. -/
@[expose] def EvalWordArgs (ρ : Frontend.C0.VEnv) (args : List LArg) (ws : List Word) : Prop :=
  args.length = ws.length ∧ ∀ p ∈ args.zip ws, EvalWordArg ρ p.1 p.2

theorem EvalWordArg.agree {n : Nat} {ρ' ρ : Frontend.C0.VEnv} {a : LArg} {w : Word}
    (hagr : VEnvAgreeBelow n ρ' ρ) (ha : argIdsBelow a n) (h : EvalWordArg ρ a w) :
    EvalWordArg ρ' a w := by
  rcases h with ⟨bw, bv, hbw, hw, hev⟩
  exact ⟨bw, bv, hbw, hw, (hagr.eval ha).trans hev⟩

theorem EvalWordArgs.agree {n : Nat} {ρ' ρ : Frontend.C0.VEnv} {args : List LArg}
    {ws : List Word} (hagr : VEnvAgreeBelow n ρ' ρ) (hids : ∀ a ∈ args, argIdsBelow a n)
    (h : EvalWordArgs ρ args ws) : EvalWordArgs ρ' args ws := by
  refine ⟨h.1, fun p hp => ?_⟩
  exact (h.2 p hp).agree hagr (hids p.1 (List.of_mem_zip hp).1)

private theorem word_toBV64_eq {bw : Nat} {bv : BitVec bw} {v : BitVec 64}
    (h : Word.toBV64? ⟨.bits bw, bv⟩ = some v) : ∃ hbw : bw = 64, hbw ▸ bv = v := by
  by_cases h64 : bw = 64
  · subst h64
    have hv : (some bv : Option (BitVec 64)) = some v := h
    exact ⟨rfl, Option.some.inj hv⟩
  · unfold Word.toBV64? at h
    split at h
    · rename_i v' heq
      have hbw : Ty.bits bw = Ty.bits 64 := congrArg Sigma.fst heq
      cases hbw
      exact absurd rfl h64
    · cases h

theorem EvalWordArg.toBV64? {ρ : Frontend.C0.VEnv} {a : LArg} {w : Word} {v : BitVec 64}
    (h : EvalWordArg ρ a w) (hv : w.toBV64? = some v) : LArg.eval ρ i64 a = some v := by
  rcases h with ⟨bw, bv, _, rfl, hev⟩
  obtain ⟨rfl, rfl⟩ := word_toBV64_eq hv
  exact hev

theorem EvalWordArg.toBits? {ρ : Frontend.C0.VEnv} {a : LArg} {w : Word} {k : Nat}
    {v : BitVec k} (h : EvalWordArg ρ a w) (hv : w.toBits? k = some v) :
    LArg.eval ρ (.bits k) a = some v := by
  rcases h with ⟨bw, bv, _, rfl, hev⟩
  dsimp [Word.toBits?] at hv
  split at hv
  · rename_i heq; subst heq; injection hv with hbv; subst hbv; exact hev
  · cases hv

theorem EvalWordArg.toRtArg {ρ : Frontend.C0.VEnv} {a : LArg} {w : Word}
    (h : EvalWordArg ρ a w) : EvalRtArg ρ a w.zext64 := by
  rcases h with ⟨bw, bv, hbw, rfl, hev⟩
  exact ⟨bw, bv, hbw, hev, rfl⟩

theorem EvalWordArg.toRtArgBV64 {ρ : Frontend.C0.VEnv} {a : LArg} {w : Word} {v : BitVec 64}
    (h : EvalWordArg ρ a w) (hv : w.toBV64? = some v) : EvalRtArg ρ a v := by
  rcases h with ⟨bw, bv, hbw, rfl, hev⟩
  obtain ⟨rfl, rfl⟩ := word_toBV64_eq hv
  exact ⟨64, bv, hbw, hev, (BitVec.setWidth_eq bv).symm⟩

theorem EvalWordArgs.toRtArgs {ρ : Frontend.C0.VEnv} :
    ∀ {args : List LArg} {ws : List Word}, EvalWordArgs ρ args ws →
      EvalRtArgs ρ args (ws.map Word.zext64)
  | [], [], _ => ⟨rfl, fun _ hp => by simp at hp⟩
  | a :: args, w :: ws, h => by
    have ha := (h.2 (a, w) List.mem_cons_self).toRtArg
    have hrest : EvalWordArgs ρ args ws :=
      ⟨Nat.succ.inj h.1, fun p hp => h.2 p (List.mem_cons_of_mem _ hp)⟩
    have ih := hrest.toRtArgs
    refine ⟨by simp [h.1], fun p hp => ?_⟩
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact ha
    · exact ih.2 p hp'

private theorem bv64_or_eq_zero_iff (u v : BitVec 64) :
    (u ||| v = 0#64) ↔ u = 0#64 ∧ v = 0#64 := by
  constructor
  · intro h
    constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro i _ <;>
      have hi := congrArg (fun x : BitVec 64 => x.getLsbD i) h <;>
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_zero, Bool.or_eq_false_iff] at hi ⊢
    · exact hi.1
    · exact hi.2
  · rintro ⟨rfl, rfl⟩; decide

theorem bv64_mul_fast_iff (x y : BitVec 64) (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    ((BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) ||| ((x * y) >>> 63)) ≠ 0#64) ↔
      ¬ (x.toNat * y.toNat < 2 ^ 63) := by
  have hprod : x.toNat * y.toNat < 2 ^ 126 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hx hy) (by decide)
  have hdiv : x.toNat * y.toNat / 2 ^ 64 < 2 ^ 64 := by
    have : (2 ^ 126 : Nat) < 2 ^ 64 * 2 ^ 64 := by decide
    omega
  have hhi : (BitVec.ofNat 64 (x.toNat * y.toNat / 2 ^ 64) = 0#64) ↔
      x.toNat * y.toNat / 2 ^ 64 = 0 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdiv] using this
    · intro h; simp [h]
  have htop : (((x * y) >>> 63) = 0#64) ↔ (x.toNat * y.toNat) % 2 ^ 64 / 2 ^ 63 = 0 := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simpa [BitVec.toNat_ushiftRight, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow] using this
    · intro h
      apply BitVec.eq_of_toNat_eq
      simpa [BitVec.toNat_ushiftRight, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow] using h
  rw [ne_eq, bv64_or_eq_zero_iff, hhi, htop]
  constructor <;> intro h <;> omega

private theorem nat_two_mul_or_one (n : Nat) : (2 * n ||| 1) = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit]
  | succ k =>
    have hk2 : (2 * n).testBit (k + 1) = n.testBit k := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    have hk1 : (2 * n + 1).testBit (k + 1) = n.testBit k := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ', ← Nat.div_div_eq_div_mul,
        show (2 * n + 1) / 2 = n by omega]
    have hone : Nat.testBit 1 (k + 1) = false := by
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    rw [Nat.testBit_or, hk2, hk1, hone, Bool.or_false]

theorem bv64_box_nat_eq (n : Nat) (hn : n < 2 ^ 63) :
    (((BitVec.ofNat 64 n) <<< 1) ||| 1#64) = BitVec.ofNat 64 (2 * n + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hn64 : n < 2 ^ 64 := by omega
  have hto : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have hshl : (BitVec.ofNat 64 n <<< 1).toNat = 2 * n := by
    rw [BitVec.toNat_shiftLeft, hto, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hmod : (2 * n + 1) % 2 ^ 64 = 2 * n + 1 := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_or, hshl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hmod]
  exact nat_two_mul_or_one n

theorem bv64_box_self_eq (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    ((x <<< 1) ||| 1#64) = BitVec.ofNat 64 (2 * x.toNat + 1) := by
  have h := bv64_box_nat_eq x.toNat hx
  simpa [BitVec.ofNat_toNat] using h

theorem bv64_shl_fast_iff (x y : BitVec 64) (_hx : x.toNat < 2 ^ 63) (hy : y.toNat < 63) :
    (((x <<< y.toNat) >>> y.toNat = x) ∧ ((x <<< y.toNat) >>> 63 = 0#64)) ↔
      x.toNat <<< y.toNat < 2 ^ 63 := by
  let p := 2 ^ y.toNat
  let q := 2 ^ (64 - y.toNat)
  have hp : 0 < p := Nat.two_pow_pos _
  have hq : 0 < q := Nat.two_pow_pos _
  have hpq : q * p = 2 ^ 64 := by
    dsimp [p, q]
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hz : (x <<< y.toNat).toNat = (x.toNat % q) * p := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, ← hpq, Nat.mul_mod_mul_right]
  have hshlEq : x.toNat <<< y.toNat = x.toNat * p := Nat.shiftLeft_eq _ _
  have hshrEq : ((x <<< y.toNat) >>> y.toNat).toNat = x.toNat % q := by
    rw [BitVec.toNat_ushiftRight, hz, Nat.shiftRight_eq_div_pow]
    exact Nat.mul_div_left _ hp
  have hok1 : ((x <<< y.toNat) >>> y.toNat = x) ↔ x.toNat < q := by
    constructor
    · intro h
      have h1 : x.toNat % q = x.toNat := by
        have := congrArg BitVec.toNat h
        rwa [hshrEq] at this
      rw [← h1]
      exact Nat.mod_lt _ hq
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [hshrEq, Nat.mod_eq_of_lt h]
  have hok2 : ((x <<< y.toNat) >>> 63 = 0#64) ↔ (x.toNat % q) * p < 2 ^ 63 := by
    constructor
    · intro h
      have h1 := congrArg BitVec.toNat h
      rw [BitVec.toNat_ushiftRight, hz, Nat.shiftRight_eq_div_pow] at h1
      change ((x.toNat % q) * p) / 2 ^ 63 = 0 at h1
      omega
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, hz, Nat.shiftRight_eq_div_pow]
      change ((x.toNat % q) * p) / 2 ^ 63 = 0
      omega
  rw [hok1, hok2, hshlEq]
  constructor
  · rintro ⟨hltq, hlt63⟩
    rwa [Nat.mod_eq_of_lt hltq] at hlt63
  · intro hlt63
    have hlt264 : x.toNat * p < q * p := by rw [hpq]; exact Nat.lt_trans hlt63 (by decide)
    have hltq : x.toNat < q := Nat.lt_of_mul_lt_mul_right hlt264
    refine ⟨hltq, ?_⟩
    rwa [Nat.mod_eq_of_lt hltq]

theorem bv64_shr1_lt (a : BitVec 64) : (a >>> 1).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt := a.isLt
  omega

theorem bv64_shr_fast_eq (a y : BitVec 64) (hy : y.toNat < 63) :
    ((a >>> ((y + 1#64).toNat % 64)) <<< 1) ||| 1#64 =
      (((a >>> (y.toNat + 1)) <<< 1) ||| 1#64) := by
  have hy1 : (y + 1#64).toNat % 64 = y.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hy63 : y.toNat < 63 := hy
    omega
  rw [hy1]

theorem uint_shift_mod_eq {w : Nat} (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)
    (b : BitVec w) :
    (b &&& BitVec.ofNat w (w - 1)).toNat % w = (b &&& BitVec.ofNat w (w - 1)).toNat := by
  have hle : (b &&& BitVec.ofNat w (w - 1)).toNat ≤ w - 1 := by
    rw [BitVec.toNat_and]
    have hlt : (BitVec.ofNat w (w - 1)).toNat ≤ w - 1 := by
      rcases hw with rfl | rfl | rfl | rfl <;> decide
    exact Nat.le_trans Nat.and_le_right hlt
  rcases hw with rfl | rfl | rfl | rfl <;> exact Nat.mod_eq_of_lt (by omega)

/-! ## 2. `LMMono` Monotonicity Lemmas -/

theorem pure_mono {α : Type} (a : α) : LMMono (pure a : LM α) := by
  intro n a' n' h
  rw [lm_pure_run] at h
  injection h with hp
  have hn : n = n' := congrArg Prod.snd hp
  subst hn
  exact Nat.le_refl _

theorem bind_mono {α β : Type} {x : LM α} {f : α → LM β}
    (hx : LMMono x) (hf : ∀ a, LMMono (f a)) : LMMono (x >>= f) := by
  intro n b n' h
  rw [lm_bind_run] at h
  rcases h with ⟨a, n1, ha, hb⟩
  exact Nat.le_trans (hx n a n1 ha) (hf a n1 b n' hb)

theorem lfail_mono {α : Type} {msg : String} : LMMono (lfail msg : LM α) := by
  intro _ _ _ h
  cases h

theorem op2_mono {t u : Ty} {sig : List Ty} {code : OpCode sig [t, u]} {args : List LArg}
    {k : LArg → LArg → LM LExpr} (hk : ∀ a b, LMMono (k a b)) :
    LMMono (LeanLCNF.op2 t u code args k) := by
  intro n e n' h
  unfold LeanLCNF.op2 at h
  rw [lm_bind_run] at h; rcases h with ⟨v1, n1, hv1, h1⟩
  rw [freshVar_run] at hv1; injection hv1 with hv1p
  have hn1 : n1 = n + 1 := (congrArg Prod.snd hv1p).symm; subst hn1
  rw [lm_bind_run] at h1; rcases h1 with ⟨v2, n2, hv2, h2⟩
  rw [freshVar_run] at hv2; injection hv2 with hv2p
  have hn2 : n2 = n + 2 := (congrArg Prod.snd hv2p).symm; subst hn2
  rw [lm_bind_run] at h2; rcases h2 with ⟨ek, n3, hek, hp⟩
  rw [lm_pure_run] at hp; injection hp with hpr
  have hn3 : n3 = n' := congrArg Prod.snd hpr; subst hn3
  exact Nat.le_trans (by omega) (hk _ _ (n + 2) ek n3 hek)

theorem tagBin_mono {rtArg : LArg} {fn : Sym} {code resW : Nat} {aArg bArg : LArg}
    {fast : LM LExpr → (LArg → LExpr) → LM LExpr} {k : LArg → LM LExpr}
    (hfast : ∀ slow j, LMMono slow → LMMono (fast slow j))
    (hk : ∀ r, LMMono (k r)) :
    LMMono (tagBin rtArg fn code resW aArg bArg fast k) := by
  unfold tagBin
  refine and64_mono fun _ => isScalarObj_mono fun _ => withJoin1_mono hk fun j => ?_
  have hslow :
      LMMono (call1 fn [i64, i64, i64, i64] i64 [rtArg, imm64 code, aArg, bArg] fun r =>
        convW 64 resW r fun r' => pure (j r')) :=
    call1_mono fun r => convW_mono fun r' => pure_mono _
  exact bind_mono (hfast _ j hslow) fun _ => bind_mono hslow fun _ => pure_mono _

theorem natBin_mono {rtArg : LArg} {op : String} {resW : Nat} {aArg bArg : LArg}
    {fast : LM LExpr → (LArg → LExpr) → LM LExpr} {k : LArg → LM LExpr}
    (hfast : ∀ slow j, LMMono slow → LMMono (fast slow j))
    (hk : ∀ r, LMMono (k r)) :
    LMMono (natBin rtArg op resW aArg bArg fast k) :=
  tagBin_mono hfast hk

theorem natPrim_mono {rtArg : LArg} {op : String} {args : List LArg} {k : LArg → LM LExpr}
    (hk : ∀ r, LMMono (k r)) : LMMono (natPrim rtArg op args k) := by
  unfold natPrim
  split
  · refine natBin_mono (fun _ j hslow => ?_) hk
    exact sub64_mono fun _ => add64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono hslow fun _ => pure_mono _
  · refine natBin_mono (fun _ j _ => ?_) hk
    exact cmpOp_mono fun _ => bind_mono (sub64_mono fun _ => add64_mono fun _ => pure_mono _)
      fun _ => pure_mono _
  · refine natBin_mono (fun _ j hslow => ?_) hk
    exact lshr64_mono fun _ => lshr64_mono fun _ => op2_mono fun _ _ =>
      lshr64_mono fun _ => or64_mono fun _ => cmpOp_mono fun _ =>
        bind_mono (boxSmall_mono fun _ => pure_mono _) fun _ =>
          bind_mono hslow fun _ => pure_mono _
  · refine natBin_mono (fun _ j _ => ?_) hk
    exact lshr64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono (lshr64_mono fun _ => op1_mono fun _ => boxSmall_mono fun _ => pure_mono _)
        fun _ => pure_mono _
  · refine natBin_mono (fun _ j _ => ?_) hk
    exact lshr64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono (lshr64_mono fun _ => op1_mono fun _ => boxSmall_mono fun _ => pure_mono _)
        fun _ => pure_mono _
  · exact natBin_mono (fun _ j _ => cmpOp_mono fun _ => boolToU8_mono fun _ => pure_mono _) hk
  · exact natBin_mono (fun _ j _ => cmpOp_mono fun _ => boolToU8_mono fun _ => pure_mono _) hk
  · exact natBin_mono (fun _ j _ => cmpOp_mono fun _ => boolToU8_mono fun _ => pure_mono _) hk
  · exact natBin_mono (fun _ j _ => cmpOp_mono fun _ => boolToU8_mono fun _ => pure_mono _) hk
  · exact natBin_mono (fun _ j _ => cmpOp_mono fun _ => boolToU8_mono fun _ => pure_mono _) hk
  · exact natBin_mono (fun _ j _ => cmpOp_mono fun _ => boolToU8_mono fun _ => pure_mono _) hk
  · refine natBin_mono (fun _ j _ => ?_) hk
    exact lshr64_mono fun _ => cmpOp_mono fun _ =>
      bind_mono (add64_mono fun _ => lshr64_mono fun _ => boxSmall_mono fun _ => pure_mono _)
        fun _ => pure_mono _
  · exact natBin_mono (fun _ j _ => and64_mono fun _ => pure_mono _) hk
  · exact natBin_mono (fun _ j _ => or64_mono fun _ => pure_mono _) hk
  · exact natBin_mono (fun _ j _ => op1_mono fun _ => or64_mono fun _ => pure_mono _) hk
  · refine natBin_mono (fun _ j hslow => ?_) hk
    refine lshr64_mono fun _ => cmpOp_mono fun _ => bind_mono ?_ fun _ =>
      bind_mono hslow fun _ => pure_mono _
    exact lshr64_mono fun _ => shl64_mono fun _ => lshr64_mono fun _ =>
      cmpOp_mono fun _ => lshr64_mono fun _ => cmpOp_mono fun _ =>
        bind_mono (boxSmall_mono fun _ => pure_mono _) fun _ =>
          bind_mono hslow fun _ => bind_mono hslow fun _ => pure_mono _
  · refine isScalarObj_mono fun _ => withJoin1_mono hk fun j => ?_
    refine bind_mono (rtCall1_mono fun _ => pure_mono _) fun _ =>
      bind_mono (cmpOp_mono fun _ => bind_mono (sub64_mono fun _ => pure_mono _) fun _ =>
        pure_mono _) fun _ => pure_mono _
  · exact rtCall1_mono hk
  · exact rtCall1_mono hk
  · exact rtCall1_mono hk
  · exact rtCall1_mono hk
  · exact lfail_mono

/-! ## 3. Runtime Bridges (`lcnf_nat_slow` and `lcnf_nat_to_str`) -/

theorem evalRtArg_imm64 (ρ : Frontend.C0.VEnv) (v : Nat) :
    EvalRtArg ρ (imm64 v) (BitVec.ofNat 64 v) :=
  ⟨64, BitVec.ofNat 64 v, rfl, LArg.eval_imm_self ρ i64 _, rfl⟩

theorem evalRtArgs_nil (ρ : Frontend.C0.VEnv) : EvalRtArgs ρ [] [] :=
  ⟨rfl, fun _ hp => by simp at hp⟩

theorem evalRtArgs_cons {ρ : Frontend.C0.VEnv} {a : LArg} {as : List LArg}
    {v : BitVec 64} {vs : List (BitVec 64)}
    (ha : EvalRtArg ρ a v) (has : EvalRtArgs ρ as vs) :
    EvalRtArgs ρ (a :: as) (v :: vs) := by
  refine ⟨by simp [has.1], fun p hp => ?_⟩
  rw [List.zip_cons_cons, List.mem_cons] at hp
  rcases hp with rfl | hp'
  · exact ha
  · exact has.2 p hp'

theorem natArithSlow_specR0 {rt va vb : BitVec 64} {code resW : Nat}
    {σ : HState} {R : Mem 64 → Prop} {mem : Mem 64} {K : HPost}
    (hcode : code ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17])
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hslow : HNatArithSlowWp rt code va vb resW K σ) :
    let P : Post [i64] := fun (res, ()) m' =>
      ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K ⟨.bits resW, res.setWidth resW⟩ σ'
    lcnfNatSlowSpecR0 (rt, BitVec.ofNat 64 code, va, vb, ()) mem P (fun _ _ _ _ => False) := by
  rcases hslow with ⟨aVal, bVal, ha, hb, hok, hk⟩
  rw [hstate_mem_unfold] at hm
  refine ⟨σ.st, σ.scr, σ.scrLimbs, σ.objs, R, hinv, hm, ?_⟩
  have hlt : code < 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    rcases hcode with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have htoNat : (BitVec.ofNat 64 code).toNat = code := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [htoNat, ite_eq_left hcode]
  refine ⟨aVal, bVal, ha, hb, hok, fun res st' scrLimbs' objs' m' hpm hrem hwf' hpost hm' => ?_⟩
  let σ' : HState := { st := st', objs := objs', scr := σ.scr, scrLimbs := scrLimbs' }
  have hm'' : (σ'.mem rt ⋆ R) m' := by rw [hstate_mem_unfold]; exact hm'
  exact ⟨σ', hwf', hm'', hk res st' scrLimbs' objs' hpm hrem hwf' hpost⟩

theorem natBitsSlow_specR0 {rt va vb : BitVec 64} {code resW : Nat}
    {σ : HState} {R : Mem 64 → Prop} {mem : Mem 64} {K : HPost}
    (hcode : code ∈ [9, 10, 11, 12, 13, 14, 15, 19])
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hslow : HNatBitsSlowWp rt code va vb resW K σ) :
    let P : Post [i64] := fun (res, ()) m' =>
      ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K ⟨.bits resW, res.setWidth resW⟩ σ'
    lcnfNatSlowSpecR0 (rt, BitVec.ofNat 64 code, va, vb, ()) mem P (fun _ _ _ _ => False) := by
  rcases hslow with ⟨aVal, ha, hok, hk⟩
  rw [hstate_mem_unfold] at hm
  refine ⟨σ.st, σ.scr, σ.scrLimbs, σ.objs, R, hinv, hm, ?_⟩
  have hlt : code < 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
    rcases hcode with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have htoNat : (BitVec.ofNat 64 code).toNat = code := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hnot1 : ¬ (code ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17]) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode ⊢
    rcases hcode with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [htoNat, ite_eq_right hnot1, ite_eq_left hcode]
  refine ⟨aVal, ha, hok, fun res st' scrLimbs' objs' m' hpm hrem hwf' hpost hm' => ?_⟩
  let σ' : HState := { st := st', objs := objs', scr := σ.scr, scrLimbs := scrLimbs' }
  have hm'' : (σ'.mem rt ⋆ R) m' := by rw [hstate_mem_unfold]; exact hm'
  exact ⟨σ', hwf', hm'', hk res st' scrLimbs' objs' hpm hrem hwf' hpost⟩

theorem natSlow_call1_conv_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg} {code resW : Nat}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64
      [rtArg, imm64 code, aArg, bArg] fun r => convW 64 resW r k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt)
    (ha : LArg.eval ρ i64 aArg = some va)
    (hb : LArg.eval ρ i64 bArg = some vb)
    (hspec : lcnfNatSlowSpecR0 (rt, BitVec.ofNat 64 code, va, vb, ()) mem
      (fun (res, ()) m' => ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧
        K ⟨.bits resW, res.setWidth resW⟩ σ') (fun _ _ _ _ => False))
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (vr : BitVec resW) (σ' : HState) (m' : Mem 64),
      n + 1 ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' (.bits resW) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits resW, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  have hsig : ("lcnf_nat_slow", [i64, i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  refine call1_wp hrun (evalArgs_cons hrt (evalArgs_cons (LArg.eval_imm_self ρ i64 _)
    (evalArgs_cons ha (evalArgs_cons hb (evalArgs_nil ρ)))))
    (hΓ.rt hsig (lcnfNatSlowSpecR0_le_rtC0CoreEnv hspec))
    (fun _ _ _ _ hf => False.elim hf) ?_
  intro r1 ek1 hek1 hr1 res m' ⟨σ', hinv', hm', hK⟩ hagr1 hr1Ev
  refine convW_wp hek1 hr1Ev hr1 ?_
  intro r2 ek2 ρ2 nr2 hnr2 hek2 hr2 hagr2 hr2Ev
  exact hk r2 ek2 ρ2 nr2 (res.setWidth resW) σ' m' (by omega) hek2 hr2
    ((hagr2.mono (Nat.le_succ n)).trans hagr1) hr2Ev hinv' hm' hK

theorem natSlow_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg opArg aArg bArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt op va vb : BitVec 64}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (rtCall1 rtArg "lcnf_nat_slow" [opArg, aArg, bArg] 64 k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (hids : ∀ a ∈ [opArg, aArg, bArg], argIdsBelow a n)
    (hevs : EvalRtArgs ρ [opArg, aArg, bArg] [op, va, vb])
    (hspec : lcnfNatSlowSpecR0 (rt, op, va, vb, ()) mem
      (fun (res, ()) m' => ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧
        K (Word.i64 res) σ') (fun _ _ _ _ => False))
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  have hsig : ("lcnf_nat_slow", [i64, i64, i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  refine rtCall1_wp hrun hrt hnrt hids hevs
    (hΓ.rt hsig (lcnfNatSlowSpecR0_le_rtC0CoreEnv hspec))
    (fun _ _ _ _ hf => False.elim hf) ?_
  intro ret m' ⟨σ', hinv', hm', hK⟩ r ek ρ' nr hnr hek hr hagr hrEv
  have hrEv' : LArg.eval ρ' i64 r = some ret := by simpa [BitVec.setWidth_eq] using hrEv
  exact hk r ek ρ' nr ret σ' m' hnr hek hr hagr hrEv' hinv' hm' hK

theorem natReprFast_rtCall1_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg : LArg}
    {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost} {X : HXPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (rtCall1 rtArg "lcnf_nat_to_str" [aArg] 64 k).run n = .ok (e, n'))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (haId : argIdsBelow aArg n) (haEv : EvalRtArg ρ aArg va)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem) (hX : HXPostRel rt R X XT)
    (hpre : HNatReprFastWp va K X σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (nr : Nat)
        (res : BitVec 64) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, n') → argIdsBelow r nr → VEnvAgreeBelow n ρ' ρ →
      LArg.eval ρ' i64 r = some res → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K (Word.i64 res) σ' → LExpr.wp Γ QT XT ek ρ' J m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  rcases hpre with ⟨val, hnih, hwf, hbody⟩
  dsimp only at hbody
  let scrFrame : Mem 64 → Prop :=
    cell64 (rt + 33672#64) σ.scr ⋆
    cell64 (rt + 33680#64) (BitVec.ofNat 64 σ.scrLimbs.length) ⋆
    array64 σ.scr σ.scrLimbs ⋆ R
  have hm' : (rtC0Inv rt σ.st ⋆ lcnfHeap σ.objs ⋆ scrFrame) mem := by
    rw [hstate_mem_unfold] at hm
    exact sep_cast hm (by dsimp only [scrFrame]; ac_rfl)
  let P : Post [i64] := fun (s, ()) m' =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧ K (Word.i64 s) σ'
  have hspec : lcnfNatToStrSpec (rt, va, ()) mem P XT := by
    refine ⟨σ.st, val, σ.objs, scrFrame, hnih, hwf, hm', ?_⟩
    by_cases hsc : (va &&& 1#64) ≠ 0#64
    · rw [ite_eq_left hsc] at hbody ⊢
      rcases hbody with ⟨hcan, hkSc⟩
      refine ⟨hcan, fun s st' m' hs0 hs8 hpm hrem hcan' hmObj => ?_⟩
      let sObj := mkStrObj s 1#32 ((natToDecimalBytes val).length + 1)
        (natToDecimalBytes val) (natToDecimalBytes val).length
      let σ' : HState := { σ with st := st', objs := sObj :: σ.objs }
      have hmPost : (σ'.mem rt ⋆ R) m' := by
        rw [hstate_mem_unfold]; dsimp only [σ']; rw [lcnfHeap.eq_2]
        exact sep_cast hmObj (by dsimp only [scrFrame]; ac_rfl)
      exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost,
        hkSc s st' hs0 hs8 hpm hrem hcan'⟩
    · rw [ite_eq_right hsc] at hbody ⊢
      rcases hbody with ⟨nObj, hmemN, haddrN, hcanon, hrcN, hcn⟩
      refine ⟨nObj, hmemN, haddrN, hcanon, hrcN, ?_⟩
      by_cases hcn0 : trimZeroLimbsLen nObj.limbs nObj.arrSize = 0
      · rw [ite_eq_left hcn0] at hcn ⊢
        rcases hcn with ⟨hcan, hk0⟩
        refine ⟨hcan, fun s st' objs' m' hs0 hs8 hpm hrem hcan' hdec hmObj => ?_⟩
        let sObj := mkStrObj s 1#32 2 [UInt8.ofNat 48] 1
        let σ' : HState := { σ with st := st', objs := sObj :: objs' }
        have hmPost : (σ'.mem rt ⋆ R) m' := by
          rw [hstate_mem_unfold]; dsimp only [σ']; rw [lcnfHeap.eq_2]
          exact sep_cast hmObj (by dsimp only [scrFrame]; ac_rfl)
        exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost,
          hk0 s st' objs' hs0 hs8 hpm hrem hcan' hdec⟩
      · rw [ite_eq_right hcn0] at hcn ⊢
        by_cases hcap : mpzMaxLimbsNat < trimZeroLimbsLen nObj.limbs nObj.arrSize
        · rw [ite_eq_left hcap] at hcn ⊢
          exact hX panicCapCode σ hcn mem hm
        · rw [ite_eq_right hcap] at hcn ⊢
          rcases hcn with ⟨hremNeed, hkBig⟩
          refine ⟨hremNeed, fun s st' objs' m' hs0 hs8 hpm hrem hcan' hdec hmObj => ?_⟩
          let sObj := mkStrObj s 1#32 ((natToDecimalBytes val).length + 1)
            (natToDecimalBytes val) (natToDecimalBytes val).length
          let σ' : HState := { σ with st := st', objs := sObj :: objs' }
          have hmPost : (σ'.mem rt ⋆ R) m' := by
            rw [hstate_mem_unfold]; dsimp only [σ']; rw [lcnfHeap.eq_2]
            exact sep_cast hmObj (by dsimp only [scrFrame]; ac_rfl)
          exact ⟨σ', hinv_of_preservesMeta hinv hpm, hmPost,
            hkBig s st' objs' hs0 hs8 hpm hrem hcan' hdec⟩
  have hsig : ("lcnf_nat_to_str", [i64, i64], [i64]) ∈ rtCoreCallSigs := by decide
  refine rtCall1_wp hrun hrt hnrt (by simp [haId])
    (evalRtArgs_cons haEv (evalRtArgs_nil ρ))
    (hΓ.rt hsig (rtR2bEnv_le_rtC0CoreEnv _ _ _ _ _ _ _ (rtR2bEnv_lcnf_nat_to_str hspec)))
    (fun _ _ _ _ h => h) ?_
  intro ret m' ⟨σ', hinv', hm'', hK⟩ r ek ρ' nr hnr hek hr hagr hrEv
  have hrEv' : LArg.eval ρ' i64 r = some ret := by simpa [BitVec.setWidth_eq] using hrEv
  exact hk r ek ρ' nr ret σ' m' hnr hek hr hagr hrEv' hinv' hm'' hK

/-! ## 4. Generic `tagBin_wp` and Tagged Comparison Bridge -/

theorem tagBin_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg} {code resW : Nat}
    {fast : LM LExpr → (LArg → LExpr) → LM LExpr} {k : LArg → LM LExpr}
    {n n' : Nat} {e : LExpr} {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64}
    {rt va vb : BitVec 64} {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hrun : (tagBin rtArg "lcnf_nat_slow" code resW aArg bArg fast k).run n = .ok (e, n'))
    (hfastMono : ∀ slow j, LMMono slow → LMMono (fast slow j))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (ha : LArg.eval ρ i64 aArg = some va) (hna : argIdsBelow aArg n)
    (hb : LArg.eval ρ i64 bArg = some vb) (hnb : argIdsBelow bArg n)
    (hslow : (((va &&& vb) &&& 1#64) = 0#64) →
      lcnfNatSlowSpecR0 (rt, BitVec.ofNat 64 code, va, vb, ()) mem
        (fun (res, ()) m' => ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧
          K ⟨.bits resW, res.setWidth resW⟩ σ') (fun _ _ _ _ => False))
    (hfast : ((va &&& vb) &&& 1#64) ≠ 0#64 →
      ∀ (j : LArg → LExpr) (body : LExpr) (n2 n3 : Nat) (J' : JEnv)
        (ρ2 : Frontend.C0.VEnv) (slow : LM LExpr),
        n + 5 ≤ n2 →
        slow = call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64
          [rtArg, imm64 code, aArg, bArg] (fun r => convW 64 resW r fun r' => pure (j r')) →
        (fast slow j).run n2 = .ok (body, n3) →
        VEnvAgreeBelow n ρ2 ρ →
        LArg.eval ρ2 i64 aArg = some va → LArg.eval ρ2 i64 bArg = some vb →
        argIdsBelow aArg n2 → argIdsBelow bArg n2 →
        (∀ (nS nSEnd : Nat) (eS : LExpr) (ρS : Frontend.C0.VEnv) (J_S : JEnv),
          n ≤ nS → slow.run nS = .ok (eS, nSEnd) →
          VEnvAgreeBelow n ρS ρ → JEnvAgreeBelow (n + 4) J_S J' →
          lcnfNatSlowSpecR0 (rt, BitVec.ofNat 64 code, va, vb, ()) mem
            (fun (res, ()) m' => ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧
              K ⟨.bits resW, res.setWidth resW⟩ σ') (fun _ _ _ _ => False) →
          LExpr.wp Γ QT XT eS ρS J_S mem) →
        (∀ (J_cur : JEnv) (a : LArg) (ρ_j : Frontend.C0.VEnv) (m_j : Mem 64)
            (v : BitVec resW) (σ' : HState),
          JEnvAgreeBelow (n + 4) J_cur J' →
          LArg.eval ρ_j (.bits resW) a = some v →
          HInv rt σ' → (σ'.mem rt ⋆ R) m_j → K ⟨.bits resW, v⟩ σ' →
          LExpr.wp Γ QT XT (j a) ρ_j J_cur m_j) →
        LExpr.wp Γ QT XT body ρ2 J' mem)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk : Nat)
        (vr : BitVec resW) (σ' : HState) (m' : Mem 64),
      n + 5 ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits resW) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits resW, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  unfold tagBin at hrun
  refine and64_wp hrun ha hb ?_
  intro abArg ek1 ρ1 hek1 _ hagr1 habEv
  refine isScalarObj_wp hek1 habEv ?_
  intro bothArg ek2 ρ2 hek2 _ hagr2 hbothEv
  let Inv : Val (.bits resW) → Mem 64 → Prop := fun v m1 =>
    ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m1 ∧ K ⟨.bits resW, v⟩ σ'
  refine withJoin1_wp (Inv := Inv) hek2 (hkMono _) ?_ ?_
  · intro r blk n2 J' hblk hr hJagr v m1 ⟨σ', hinv', hm', hK⟩ hagr rEv
    exact hk r blk _ J' (n + 5) n2 v σ' m1 (Nat.le_refl _) hblk hr
      ((hagr.mono (by omega : n ≤ n + 3)).trans ((hagr2.mono (by omega : n ≤ n + 1)).trans hagr1))
      (hJagr.mono (by omega : n ≤ n + 3)) rEv hinv' hm' hK
  · intro j body n2 J' hn2 hbody _ hjok
    rw [lm_bind_run] at hbody
    rcases hbody with ⟨fastE, n3, hfastE, hrest⟩
    rw [lm_bind_run] at hrest
    rcases hrest with ⟨slowE, n4, hslowE, hpure⟩
    rw [lm_pure_run] at hpure
    injection hpure with hpr
    have hbod : LExpr.jnz bothArg fastE slowE = body := congrArg Prod.fst hpr
    have hn4 : n4 = n' := congrArg Prod.snd hpr
    subst hbod; subst hn4
    have hslowMono : LMMono (call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64
        [rtArg, imm64 code, aArg, bArg] fun r => convW 64 resW r fun r' => pure (j r')) :=
      call1_mono fun _ => convW_mono fun _ => pure_mono _
    have hn23 : n2 ≤ n3 := hfastMono _ j hslowMono n2 fastE n3 hfastE
    have hagr20 : VEnvAgreeBelow n ρ2 ρ := (hagr2.mono (by omega : n ≤ n + 1)).trans hagr1
    have hslowRun : ∀ (nS nSEnd : Nat) (eS : LExpr) (ρS : Frontend.C0.VEnv) (J_S : JEnv),
        n ≤ nS →
        (call1 "lcnf_nat_slow" [i64, i64, i64, i64] i64 [rtArg, imm64 code, aArg, bArg]
          fun r => convW 64 resW r fun r' => pure (j r')).run nS = .ok (eS, nSEnd) →
        VEnvAgreeBelow n ρS ρ → JEnvAgreeBelow (n + 4) J_S J' →
        lcnfNatSlowSpecR0 (rt, BitVec.ofNat 64 code, va, vb, ()) mem
          (fun (res, ()) m' => ∃ σ' : HState, HInv rt σ' ∧ (σ'.mem rt ⋆ R) m' ∧
            K ⟨.bits resW, res.setWidth resW⟩ σ') (fun _ _ _ _ => False) →
        LExpr.wp Γ QT XT eS ρS J_S mem := by
      intro nS nSEnd eS ρS J_S hnS heS hagrS hJS hsp
      refine natSlow_call1_conv_wp hΓ heS ((hagrS.eval hnrt).trans hrt)
        ((hagrS.eval hna).trans ha) ((hagrS.eval hnb).trans hb) hsp ?_
      intro r2 ekS ρS' nrS vr σ' m' _ hekS _ _ hr2Ev hinv' hm' hK
      rw [lm_pure_run] at hekS
      injection hekS with hps
      have heS' : j r2 = ekS := congrArg Prod.fst hps
      subst heS'
      exact hjok J_S r2 ρS' m' vr hJS hr2Ev ⟨σ', hinv', hm', hK⟩
    refine wp_jnz hbothEv ?_ ?_
    · intro htrue
      have hsc : ((va &&& vb) &&& 1#64) ≠ 0#64 := of_decide_eq_true htrue
      exact hfast hsc j fastE n2 n3 J' ρ2 _ (by omega) rfl hfastE hagr20
        ((hagr20.eval hna).trans ha) ((hagr20.eval hnb).trans hb)
        (argIdsBelow_mono (by omega) hna) (argIdsBelow_mono (by omega) hnb) hslowRun
        (fun J_cur a ρ_j m_j v σ' hJcur haEv hinv' hm' hK =>
          hjok J_cur a ρ_j m_j v hJcur haEv ⟨σ', hinv', hm', hK⟩)
    · intro hfalse
      have hsc : ((va &&& vb) &&& 1#64) = 0#64 := by
        have := of_decide_eq_false hfalse
        simpa using this
      exact hslowRun n3 n4 slowE ρ2 J' (by omega) hslowE hagr20
        (JEnvAgreeBelow.refl _ J') (hslow hsc)

theorem tagBin_cmp_wp {m : LcModule} {Δ : HEnv} {Γ : Env} {rs : List Ty}
    {QT : Post rs} {XT : XPost} {rtArg aArg bArg : LArg} {op' : String} {code : Nat}
    {cmpO : CmpOp} {k : LArg → LM LExpr} {n n' : Nat} {e : LExpr}
    {ρ : Frontend.C0.VEnv} {J : JEnv} {mem : Mem 64} {rt va vb : BitVec 64} {σ : HState}
    {R : Mem 64 → Prop} {K : HPost}
    (hΓ : HCallEnvOk m Δ Γ)
    (hcode : code ∈ [1, 2, 3, 4, 5, 6, 7, 8, 17])
    (hfastEq : ((va &&& vb) &&& 1#64) ≠ 0#64 →
      natBinFast? op' va vb = some (Word.i8 (if cmpO.evalBits va vb then 1#8 else 0#8)))
    (hrun : (tagBin rtArg "lcnf_nat_slow" code 8 aArg bArg
      (fun _ j => cmpOp cmpO 64 aArg bArg fun c => boolToU8 c fun r => pure (j r)) k).run n =
      .ok (e, n'))
    (hkMono : ∀ r, LMMono (k r))
    (hrt : LArg.eval ρ i64 rtArg = some rt) (hnrt : argIdsBelow rtArg n)
    (ha : LArg.eval ρ i64 aArg = some va) (hna : argIdsBelow aArg n)
    (hb : LArg.eval ρ i64 bArg = some vb) (hnb : argIdsBelow bArg n)
    (hinv : HInv rt σ) (hm : (σ.mem rt ⋆ R) mem)
    (hwp : match natBinFast? op' va vb with
      | some w => K w σ
      | none => HNatArithSlowWp rt code va vb 8 K σ)
    (hk : ∀ (r : LArg) (ek : LExpr) (ρ' : Frontend.C0.VEnv) (J' : JEnv) (nr nk rw : Nat)
        (vr : BitVec rw) (σ' : HState) (m' : Mem 64),
      n ≤ nr → (k r).run nr = .ok (ek, nk) → argIdsBelow r nr →
      VEnvAgreeBelow n ρ' ρ → JEnvAgreeBelow n J' J →
      LArg.eval ρ' (.bits rw) r = some vr → HInv rt σ' → (σ'.mem rt ⋆ R) m' →
      K ⟨.bits rw, vr⟩ σ' → LExpr.wp Γ QT XT ek ρ' J' m') :
    LExpr.wp Γ QT XT e ρ J mem := by
  refine tagBin_wp (R := R) (K := K) hΓ hrun
    (fun _ _ _ => cmpOp_mono fun _ => boolToU8_mono fun _ => pure_mono _)
    hkMono hrt hnrt ha hna hb hnb ?_ ?_ ?_
  · intro hsc0
    have hnone : natBinFast? op' va vb = none := by simp [natBinFast?, hsc0]
    rw [hnone] at hwp
    exact natArithSlow_specR0 hcode hinv hm hwp
  · intro hsc j body n2 n3 J' ρ2 slow hn2 _ hbody _ ha2 hb2 _ _ _ hj
    refine cmpOp_wp hbody ha2 hb2 ?_
    intro cArg ek1 ρ1 hek1 _ _ hcEv
    refine boolToU8_wp hek1 hcEv ?_
    intro rArg ek2 ρ3 hek2 _ _ hrEv
    rw [lm_pure_run] at hek2
    injection hek2 with hp
    have hej : j rArg = ek2 := congrArg Prod.fst hp
    subst hej
    rw [hfastEq hsc] at hwp
    exact hj J' rArg ρ3 mem _ σ (JEnvAgreeBelow.refl _ J') hrEv hinv hm hwp
  · intro r ek ρ' J' nr nk vr σ' m' hnr hek hr hagr hJagr hrEv hinv' hm' hK
    exact hk r ek ρ' J' nr nk 8 vr σ' m' (by omega) hek hr hagr hJagr hrEv hinv' hm' hK

end LeanQbe.T.LeanLCNF.Sem
