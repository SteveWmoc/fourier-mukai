import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Category.Ring.Basic

-- Define a field k as a global variable for algebraic geometry
variable (k : Type) [Field k]

-- Define a type for commutative rings using Sigma
def CommRingType := Σ R : Type, CommRing R
