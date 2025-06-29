/-
Copyright (c) 2025 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/
/-
  FourierMukai.lean
  Main entry point for the Fourier–Mukai formalization project.
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.WeierstrassCurve

section BaseField

variable (k : Type*) [Field k] [IsAlgClosed k]
variable (E : AlgebraicGeometry.WeierstrassCurve k) [E.IsElliptic]

/-
  Now E is an elliptic curve over k in the Mathlib4 sense.

  Next steps:
    - Define Coh(E): the abelian category of coherent sheaves on E
    - Define the bounded derived category D^b(Coh(E))
    - Define the Poincaré bundle on E × E
    - State and eventually prove the Fourier–Mukai equivalence theorem
-/

end BaseField
