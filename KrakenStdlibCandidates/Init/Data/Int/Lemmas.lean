prelude
import KrakenStdlibCandidates.Init.GrindInternHooks
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Int.Pow

/-!
# Grind homomorphisms for Int casts and relations with Nat.
-/

set_option autoImplicit true

attribute [grind_homo] Int.natCast_add Int.natCast_mul Int.natCast_pow Int.natCast_shiftLeft
attribute [grind_homo_pred] Int.natCast_inj Int.ofNat_le Int.ofNat_lt
