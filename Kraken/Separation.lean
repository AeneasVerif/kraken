import Std

namespace Std.ExtHashMap
local notation "map" => Std.ExtHashMap

abbrev SepPred (key value : Type) [BEq key] [Hashable key] := ExtHashMap key value → Prop

variable {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key]

instance : Coe (ExtHashMap key value) (SepPred key value) where coe := Eq

def sep (p q : SepPred key value) (m : ExtHashMap key value) : Prop :=
  ∃ a b, a.union b = m ∧ a.inter b = ∅ ∧ p a ∧ q b

infixl:60 " ⋆ " => sep
notation:70 m " =⋆ " P => ((P : SepPred _ _) m : Prop)
end Std.ExtHashMap
