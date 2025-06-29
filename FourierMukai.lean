/-
Copyright (c) 2025 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/
/-
  FourierMukai.lean
  Main entry point for the Fourier–Mukai formalization project.

  States the Fourier–Mukai equivalence theorem for derived categories of coherent sheaves on an elliptic curve.
-/

-- Base field: algebraically closed
import Mathlib.Algebra.Field.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic

-- Elliptic curve (Weierstrass form)
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

open AlgebraicGeometry -- so WeierstrassCurve is in scope

section BaseField

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- An elliptic curve over `k` (Weierstrass model with nonzero discriminant). -/
structure EllipticCurveOver where
  curve : WeierstrassCurve k
  non_singular : curve.discriminant ≠ 0

variable {k} (E : EllipticCurveOver k)

end BaseField

/-
  TODO:
  - Define the abelian category of coherent sheaves on E, `Coh(E)`
  - Define the bounded derived category, `D^b(Coh(E))`
  - Define the Poincaré bundle on E × E
  - State and prove the Fourier–Mukai equivalence theorem
-/
