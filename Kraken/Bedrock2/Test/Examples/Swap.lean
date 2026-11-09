module

public import Kraken.Bedrock2.SemanticsLemmas
import Kraken.Bedrock2.Notation
meta import Kraken.Bedrock2.CPrinter

@[expose] public section

open Std Std.ExtHashMap

namespace Kraken.Bedrock2.Test.Examples

def swap (w : Nat) : String × Func :=
  let sz := AccessSize.ofWidth w
  bedrock2:(fn swap(a, b) {
    t = %❰.load sz (.var "b")❱;
    %❰.store sz (.var "b") (.load sz (.var "a"))❱;
    %❰.store sz (.var "a") (.var "t")❱
  })

def swap_swap := bedrock2:(fn swap_swap(a, b) {
  swap(a, b);
  swap(a, b)
})

theorem swap_ok {w : Nat} (hw : w = 32 ∨ w = 64) {ext : ExtSpec w} {e : Env}
    (he : e.lookup (swap w).1 = some (swap w).2)
    {t : Trace w} {m : Mem w} {pa pb : BitVec w} {bsa bsb : List UInt8} {R : Mem w → Prop}
    (hla : bsa.length = w / 8) (hlb : bsb.length = w / 8)
    (hm : m =⋆ Eq (bsa.At pa) ⋆ Eq (bsb.At pb) ⋆ R) :
    call ext e (swap w).1 t m [pa, pb] fun t' m' rets =>
      rets = [] ∧ t' = t ∧ (m' =⋆ Eq (bsb.At pa) ⋆ Eq (bsa.At pb) ⋆ R) := by
  refine call.of_body he (by simp [swap]; rfl) ?_
  have hmA : m =⋆ Eq (bsa.At pa) ⋆ (Eq (bsb.At pb) ⋆ R) := by rwa [← sep_assoc]
  have hmB : m =⋆ Eq (bsb.At pb) ⋆ (Eq (bsa.At pa) ⋆ R) := by rwa [sep_comm_l]
  have hla' := hla.trans (bytes_ofWidth hw).symm
  have hlb' := hlb.trans (bytes_ofWidth hw).symm
  have hA := load?_sep hmA hla' (bytes_ofWidth_le hw)
  have hB := load?_sep hmB hlb' (bytes_ofWidth_le hw)
  refine Exec.seq_cps (Exec.set_cps (v := .ofInt w (Int.ofBytes bsb))
    (by simp [Expr.eval, hB]) (Exec.seq_cps ?_))
  refine Exec.store_sep (a := pb) (v := .ofInt w (Int.ofBytes bsa))
    (by simp [Expr.eval]) (by simp [Expr.eval, hA]) hmB hlb'
    (bytes_ofWidth_le hw) fun m1 hm1 => ?_
  rw [← hla', toBytes_toNat_ofInt_ofBytes (by omega), sep_comm_l] at hm1
  refine Exec.store_sep (a := pa) (v := .ofInt w (Int.ofBytes bsb))
    (by simp [Expr.eval]) (by simp [Expr.eval]) hm1 hla'
    (bytes_ofWidth_le hw) fun m2 hm2 => ?_
  rw [← hlb', toBytes_toNat_ofInt_ofBytes (by omega), ← sep_assoc] at hm2
  exact ⟨[], rfl, rfl, rfl, hm2⟩

theorem swap_swap_ok {w : Nat} (hw : w = 32 ∨ w = 64) {ext : ExtSpec w} {e : Env}
    (he : e.lookup (swap w).1 = some (swap w).2)
    (he' : e.lookup swap_swap.1 = some swap_swap.2)
    {t : Trace w} {m : Mem w} {pa pb : BitVec w} {bsa bsb : List UInt8} {R : Mem w → Prop}
    (hla : bsa.length = w / 8) (hlb : bsb.length = w / 8)
    (hm : m =⋆ Eq (bsa.At pa) ⋆ Eq (bsb.At pb) ⋆ R) :
    call ext e swap_swap.1 t m [pa, pb] fun t' m' rets =>
      rets = [] ∧ t' = t ∧ (m' =⋆ Eq (bsa.At pa) ⋆ Eq (bsb.At pb) ⋆ R) := by
  refine call.of_body he' (by simp [swap_swap]; rfl) ?_
  refine Exec.seq_cps (Exec.call_cps (args := [pa, pb]) (by simp [evalArgs, Expr.eval])
    ((swap_ok hw he hla hlb hm).weaken ?_))
  rintro t1 m1 _ ⟨rfl, rfl, hm1⟩
  refine ⟨_, putManyZip_nil _, Exec.call_cps (args := [pa, pb]) (by simp [evalArgs, Expr.eval])
    ((swap_ok hw he hlb hla hm1).weaken ?_)⟩
  rintro t2 m2 _ ⟨rfl, rfl, hm2⟩
  exact ⟨_, putManyZip_nil _, [], rfl, rfl, rfl, hm2⟩

#guard (cModuleForWidth 32 [swap 32, swap_swap] []).isOk
#guard (cModuleForWidth 64 [swap 64, swap_swap] []).isOk

end Kraken.Bedrock2.Test.Examples
