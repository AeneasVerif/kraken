module

public import Kraken.Bedrock2.Test.Examples.SetBytes
import Kraken.Bedrock2.Notation
meta import Kraken.Bedrock2.CPrinter
meta import Kraken.Bedrock2.Test.Examples.SetBytes

@[expose] public section

open Std Std.ExtHashMap

namespace Kraken.Bedrock2.Test.Examples

def stackalloc_set_bytes := bedrock2:(fn stackalloc_set_bytes(x) -> (r) {
  stackalloc 16 as buf {
    set_bytes(buf, 16, x);
    r = load1(buf + 3)
  }
})

theorem stackalloc_set_bytes_ok {w : Nat} (hw : w = 32 ∨ w = 64) {ext : ExtSpec w}
    {e : Env}
    (he : e.lookup set_bytes.1 = some set_bytes.2)
    (he' : e.lookup stackalloc_set_bytes.1 = some stackalloc_set_bytes.2)
    {t : Trace w} {m : Mem w} {x : BitVec w} :
    call ext e stackalloc_set_bytes.1 t m [x] fun t' m' rets =>
      t' = t ∧ m' = m ∧ rets = [x &&& 0xff] := by
  refine call.of_body he' (by simp [stackalloc_set_bytes]; rfl) ?_
  refine Exec.stackalloc_cps fun a _ mC ⟨bs, hbs, hlen, _⟩ hsplit => ?_
  subst hbs
  have hC : mC =⋆ Eq (bs.At a) ⋆ Eq m := by rwa [split_iff_sep, sep_comm] at hsplit
  have h16 : (BitVec.ofInt w 16).toNat = 16 := by obtain rfl | rfl := hw <;> decide
  have h16le : 16 ≤ 2 ^ w := by obtain rfl | rfl := hw <;> decide
  refine Exec.seq_cps (Exec.call_cps (args := [a, .ofInt w 16, x]) (by simp [evalArgs, Expr.eval])
    ((set_bytes_ok he (by rw [hlen, h16]) hC).weaken ?_))
  rintro _ mC1 _ ⟨rfl, rfl, hm1⟩
  rw [h16] at hm1
  have hsplit1 : split mC1 m ((List.replicate 16 x.toNat.toUInt8).At a) := by
    rwa [split_iff_sep, sep_comm]
  rw [show List.replicate 16 x.toNat.toUInt8 = List.replicate 3 x.toNat.toUInt8 ++
      x.toNat.toUInt8 :: List.replicate 12 x.toNat.toUInt8 from rfl,
    Mem.At_append_sep _ _ _ (by simpa using h16le), List.length_replicate,
    At_cons_sep _ _ _ (by simp; omega),
    show BitVec.ofNat w 3 = BitVec.ofInt w 3 by obtain rfl | rfl := hw <;> decide,
    sep_comm_l, sep_assoc] at hm1
  have hld := load?_sep (sz := .one) hm1 rfl Nat.one_le_two_pow
  refine ⟨_, putManyZip_nil _, Exec.set_cps (by simpa [Expr.eval, interpBinop] using hld) ?_⟩
  exact ⟨m, _, ⟨_, rfl, List.length_replicate, h16le⟩, hsplit1,
    [.ofInt w (Int.ofBytes [x.toNat.toUInt8])], by simp [getMany, stackalloc_set_bytes], rfl, rfl,
    by rw [ofInt_ofBytes_byte (by omega)]⟩

#guard (cModuleForWidth 32 [stackalloc_set_bytes, set_bytes] []).isOk
#guard (cModuleForWidth 64 [stackalloc_set_bytes, set_bytes] []).isOk

end Kraken.Bedrock2.Test.Examples
