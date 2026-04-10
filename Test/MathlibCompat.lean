-- This file demonstrates that importing both Kraken.Semantics and Mathlib
-- causes a compilation failure due to conflicting `List.scanl` definitions.
import Kraken.Semantics
import Mathlib.Data.List.Defs

#check List.scanl
