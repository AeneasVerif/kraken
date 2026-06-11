import Std
namespace Std.ExtHashMap
local notation "map" => Std.ExtHashMap

variable {key value : Type} [BEq key] [EquivBEq key] [Hashable key] [LawfulHashable key]

instance : CoeFun (map key value) (fun _ => map key value → Prop) where coe := Eq

def sep (p q : map key value → Prop) (m : map key value) : Prop :=
  ∃ a b, a.union b = m ∧ a.inter b = ∅ ∧ p a ∧ q b

infixl:60 " ⋆ " => sep
notation:70 m " =⋆ " P => ((P : ExtHashMap _ _ → Prop) m : Prop)
end Std.ExtHashMap
