module

public import Kraken.Bedrock2.SemanticsLemmas
import Kraken.Bedrock2.Notation
meta import Kraken.Bedrock2.CPrinter

@[expose] public section

open Std Std.ExtHashMap

namespace Kraken.Bedrock2.Test.Examples

def set_bytes := bedrock2:(fn set_bytes(p, n, v) {
  while n {
    store1(p, v);
    p = p + 1;
    n = n - 1
  }
})

theorem set_bytes_ok {w : Nat} {ext : ExtSpec w} {e : Env} {B : Nat}
    (he : e.lookup set_bytes.1 = some set_bytes.2)
    {t : Trace w} {m : Mem w} {p n v : BitVec w} {bs : List UInt8} {R : Mem w → Prop}
    (hl : bs.length = n.toNat) (hm : m =⋆ Eq (bs.At p) ⋆ R) :
    call ext e B set_bytes.1 t m [p, n, v] fun t' m' rets =>
      rets = [] ∧ t' = t ∧ (m' =⋆ Eq ((List.replicate n.toNat v.toNat.toUInt8).At p) ⋆ R) := by
  refine call.of_body he (by simp [set_bytes]; rfl) ?_
  refine Exec.tailrec (Measure := Nat) (Ghost := List UInt8 × BitVec w × (Mem w → Prop))
    (fun k g t' m' l' => t' = t ∧ l'["p"]? = some g.2.1 ∧
      (∃ nb, l'["n"]? = some nb ∧ nb.toNat = k) ∧ l'["v"]? = some v ∧ g.1.length = k ∧
      (m' =⋆ Eq (g.1.At g.2.1) ⋆ g.2.2))
    (fun k g t' m' _ => t' = t ∧ (m' =⋆ Eq ((List.replicate k v.toNat.toUInt8).At g.2.1) ⋆ g.2.2))
    (· < ·) Nat.lt_wfRel.wf n.toNat (bs, p, R)
    ⟨rfl, by simp, ⟨n, by simp, rfl⟩, by simp, hl, hm⟩
    ?_ fun _ _ _ ⟨ht, hq⟩ => ⟨[], rfl, rfl, ht, hq⟩
  rintro k ⟨bs, q, F⟩ t' m' l' ⟨rfl, hp, ⟨nb, hn, rfl⟩, hv, hlen, hsep⟩
  refine ⟨nb, by simp [Expr.eval, hn], fun hnz => ?_, fun hz => ⟨rfl, ?_⟩⟩
  · obtain _ | ⟨b0, bs⟩ := bs
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using hlen.symm)) hnz
    simp only [List.length_cons] at hlen
    have hlt := nb.isLt
    rw [At_cons_sep _ _ _ (by omega), sep_assoc] at hsep
    refine Exec.seq_cps (Exec.store_sep (a := q) (v := v) (by simp [Expr.eval, hp])
      (by simp [Expr.eval, hv]) hsep rfl Nat.one_le_two_pow fun m1 hm1 => ?_)
    rw [toBytes_one, sep_comm_l] at hm1
    refine Exec.seq_cps (Exec.set_cps (v := q + 1) (by simp [Expr.eval, hp, interpBinop])
      (Exec.set_cps (v := nb - 1) (by simp [Expr.eval, hn, interpBinop]) ?_))
    refine ⟨bs.length, (bs, q + 1, Eq ([v.toNat.toUInt8].At q) ⋆ F),
      ⟨rfl, by simp, ⟨nb - 1, by simp, by rw [toNat_sub_one (by omega)]; omega⟩,
        by simp [hv], rfl, hm1⟩, by omega, ?_⟩
    rintro _ m2 _ ⟨rfl, hm2⟩
    rw [← hlen, List.replicate_succ, At_cons_sep _ _ _ (by simp; omega), sep_assoc, sep_comm_l]
    exact ⟨rfl, hm2⟩
  · subst hz
    obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    exact hsep

#guard (cModuleForWidth 32 [set_bytes] []).isOk
#guard (cModuleForWidth 64 [set_bytes] []).isOk

end Kraken.Bedrock2.Test.Examples
