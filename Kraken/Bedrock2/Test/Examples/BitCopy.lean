module

public import Kraken.Bedrock2.SemanticsLemmas
import Kraken.Bedrock2.Notation
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Kraken.Bedrock2.CPrinter

@[expose] public section

open Std Std.ExtHashMap

namespace Kraken.Bedrock2.Test.Examples

def bitcopy_store := bedrock2:(fn bitcopy_store() -> (r) {
  stackalloc 8 as x {
    store8(x, 0);
    i = 0;
    b = 1;
    while b {
      if x & b { i = i | b };
      b = b << 1
    };
    store8(i, 15);
    r = load8(x)
  }
})

private theorem bitcopy_step {w : Nat} (hw : w = 32 ∨ w = 64) (a bv : BitVec w)
    (hb : bv &&& (bv - 1) = 0) (hnz : bv ≠ 0) :
    (bv <<< 1) &&& ((bv <<< 1) - 1) = 0 ∧
    (a &&& bv ≠ 0 → (a &&& (bv - 1)) ||| bv = a &&& ((bv <<< 1) - 1)) ∧
    (a &&& bv = 0 → a &&& (bv - 1) = a &&& ((bv <<< 1) - 1)) := by
  obtain rfl | rfl := hw <;> bv_decide

theorem bitcopy_store_ok {w : Nat} (hw : w = 32 ∨ w = 64) {ext : ExtSpec w} {e : Env}
    {B : Nat} (hB : 8 ≤ B) (he : e.lookup bitcopy_store.1 = some bitcopy_store.2)
    {t : Trace w} {m : Mem w} :
    call ext e B bitcopy_store.1 t m [] fun t' m' rets => t' = t ∧ m' = m ∧ rets = [15] := by
  refine call.of_body he (putManyZip_nil _) ?_
  refine Exec.stackalloc_cps hB fun a _ mC ⟨bs, hbs, hlen, _⟩ hsplit => ?_
  subst hbs
  have h8 : AccessSize.eight.bytes ≤ 2 ^ w := by obtain rfl | rfl := hw <;> decide
  have hshamt : shamt (1#w) = 1 := by obtain rfl | rfl := hw <;> decide
  have hC : mC =⋆ Eq (bs.At a) ⋆ Eq m := by rwa [split_iff_sep, sep_comm] at hsplit
  refine Exec.seq_cps (Exec.store_sep (a := a) (v := .ofInt w 0) (by simp [Expr.eval]) rfl hC hlen
    h8 fun m1 hm1 => ?_)
  refine Exec.seq_cps (Exec.set_cps rfl (Exec.seq_cps (Exec.set_cps rfl (Exec.seq_cps ?_))))
  refine Exec.while_wf (Measure := Nat) (lt := (· < ·)) Nat.lt_wfRel.wf
    (fun v t' m' l' => ∃ k ≤ w, v = w - k ∧ t = t' ∧ m1 = m' ∧ l'["x"]? = some a ∧
      l'["b"]? = some (1#w <<< k) ∧ (1#w <<< k) &&& ((1#w <<< k) - 1) = 0 ∧
      l'["i"]? = some (a &&& ((1#w <<< k) - 1)))
    w ⟨0, by omega, rfl, rfl, rfl, by simp, by simp,
      by obtain rfl | rfl := hw <;> decide, by simp⟩ ?_
  rintro _ _ _ l' ⟨k, hk, rfl, rfl, rfl, hx, hb, hpow, hi⟩
  refine ⟨1#w <<< k, by simp [Expr.eval, hb], fun hnz => ?_, fun hz => ?_⟩
  · have hkw : k < w := by
      refine Nat.lt_of_le_of_ne hk ?_
      rintro rfl
      exact hnz (by obtain rfl | rfl := hw <;> decide)
    obtain ⟨hpow', hset, hskip⟩ := bitcopy_step hw a (1#w <<< k) hpow hnz
    refine Exec.seq_cps (Exec.weaken (post1 := fun t'' m'' l'' => t = t'' ∧ m1 = m'' ∧
      l''["x"]? = some a ∧ l''["b"]? = some (1#w <<< k) ∧
      l''["i"]? = some (a &&& (((1#w <<< k) <<< 1) - 1))) ?_ ?_)
    · refine Exec.cond_cps (v := a &&& (1#w <<< k)) (by simp [Expr.eval, interpBinop, hx, hb])
        (fun hand => Exec.set_cps (by simp [Expr.eval, interpBinop, hi, hb]; rfl)
          ⟨rfl, rfl, by simp [hx], by simp [hb], by simpa using hset hand⟩)
        fun hand => .skip _ _ _ _ _ ⟨rfl, rfl, hx, hb, by rwa [← hskip hand]⟩
    · rintro _ _ l'' ⟨rfl, rfl, hx', hb', hi'⟩
      refine Exec.set_cps (v := (1#w <<< k) <<< 1)
        (by simp [Expr.eval, interpBinop, hb', hshamt]) ?_
      rw [← BitVec.shiftLeft_add] at hpow' hi' ⊢
      exact ⟨w - (k + 1), ⟨k + 1, by omega, rfl, rfl, rfl, by simp [hx'], by simp, hpow',
        by simp [hi']⟩, by omega⟩
  · rw [hz, show a &&& (0 - 1) = a by obtain rfl | rfl := hw <;> bv_decide] at hi
    refine Exec.seq_cps (Exec.store_sep (a := a) (v := .ofInt w 15) (by simp [Expr.eval, hi]) rfl
      hm1 (Int.toBytes_length _ _) h8 fun m2 hm2 => ?_)
    have hld := load?_sep (sz := .eight) hm2 (Int.toBytes_length _ _) h8
    simp [AccessSize.bytes, Int.take] at hld
    refine Exec.set_cps (v := 15)
      (by simp [Expr.eval, hx, hld]; obtain rfl | rfl := hw <;> decide) ⟨m, _,
      ⟨_, rfl, Int.toBytes_length _ _, h8⟩, by rw [split_iff_sep, sep_comm]; exact hm2, [15],
      by simp [getMany, bitcopy_store], rfl, rfl, rfl⟩

#guard (cModuleForWidth 32 [bitcopy_store] []).isOk
#guard (cModuleForWidth 64 [bitcopy_store] []).isOk

end Kraken.Bedrock2.Test.Examples
