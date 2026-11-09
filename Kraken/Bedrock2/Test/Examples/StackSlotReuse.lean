module

public import Kraken.Bedrock2.SemanticsLemmas
import Kraken.Bedrock2.Notation
import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Kraken.Bedrock2.CPrinter

@[expose] public section

open Std Std.ExtHashMap

namespace Kraken.Bedrock2.Test.Examples

def addrs := bedrock2:(fn addrs() -> (x, y) {
  if 1 { stackalloc 8 as a { x = a } };
  if 1 { stackalloc 8 as b { y = b } }
})

def same_slot := bedrock2:(fn same_slot() -> (r) {
  x, y = addrs();
  r = 0;
  if x == y { skip } else {
    if x - y == y - x {
      if ((0 - 1) / 2) < (x - y) { skip } else { r = 1 }
    }
  }
})

theorem addrs_ok {w : Nat} (hw : w = 32 ∨ w = 64) {ext : ExtSpec w} {e : Env} {B : Nat}
    (hB : 8 ≤ B) (he : e.lookup addrs.1 = some addrs.2) {t : Trace w} {m : Mem w} :
    call ext e B addrs.1 t m [] fun t' m' rets => t' = t ∧ m' = m ∧ ∃ x y, rets = [x, y] := by
  have h1 : BitVec.ofInt w 1 ≠ 0 := by obtain rfl | rfl := hw <;> decide
  refine call.of_body he (putManyZip_nil _) (Exec.seq_cps (Exec.cond_cps (v := .ofInt w 1) rfl
    (fun _ => ?_) fun h => absurd h h1))
  refine Exec.stackalloc_cps hB fun a _ _ hany hsplit =>
    Exec.set_cps (v := a) (by simp [Expr.eval]) ⟨_, _, hany, hsplit, ?_⟩
  refine Exec.cond_cps (v := .ofInt w 1) rfl (fun _ => ?_) fun h => absurd h h1
  refine Exec.stackalloc_cps hB fun b _ _ hany hsplit =>
    Exec.set_cps (v := b) (by simp [Expr.eval]) ⟨_, _, hany, hsplit, ?_⟩
  exact ⟨[a, b], by simp [getMany, addrs], rfl, rfl, a, b, rfl⟩

theorem same_slot_ok {w : Nat} (hw : w = 32 ∨ w = 64) {ext : ExtSpec w} {e : Env} {B : Nat}
    (hB : 8 ≤ B) (he : e.lookup addrs.1 = some addrs.2)
    (he' : e.lookup same_slot.1 = some same_slot.2)
    {t : Trace w} {m : Mem w} :
    call ext e B same_slot.1 t m [] fun t' m' rets => t' = t ∧ m' = m ∧ rets = [0] := by
  refine call.of_body he' (putManyZip_nil _) (Exec.seq_cps (Exec.call_cps (args := []) rfl
    ((addrs_ok hw hB he).weaken ?_)))
  rintro t m _ ⟨rfl, rfl, x, y, rfl⟩
  refine ⟨_, by simp; rfl, Exec.seq_cps (Exec.set_cps rfl ?_)⟩
  have hdone : ∀ l : Locals w, l["r"]? = some (.ofInt w 0) →
      Exec ext e B .skip t m l fun t' m' l' =>
        ∃ rets, getMany l' same_slot.2.rets = some rets ∧ t' = t ∧ m' = m ∧ rets = [0] :=
    fun l hl => .skip _ _ _ _ _ ⟨_, by simp [getMany, same_slot, hl], rfl, rfl, rfl⟩
  refine Exec.cond_cps (v := if x = y then 1 else 0) (by simp [Expr.eval, interpBinop])
    (fun _ => hdone _ getElem?_insert_self) fun hv => ?_
  refine Exec.cond_cps (v := if x - y = y - x then 1 else 0) (by simp [Expr.eval, interpBinop])
    (fun hv' => ?_) fun _ => hdone _ getElem?_insert_self
  refine Exec.cond_cps (v := 1) ?_ (fun _ => hdone _ getElem?_insert_self)
    fun h => absurd h (by obtain rfl | rfl := hw <;> decide)
  simp [Expr.eval, interpBinop]
  clear hdone
  obtain rfl | rfl := hw <;> bv_decide

#guard (cModuleForWidth 32 [addrs, same_slot] []).isOk
#guard (cModuleForWidth 64 [addrs, same_slot] []).isOk

end Kraken.Bedrock2.Test.Examples
