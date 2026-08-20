import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Relative products of schemes

This file provides the thinnest project-level interface around Mathlib's scheme pullbacks.
For morphisms `f : X ⟶ S` and `g : Y ⟶ S`, the object `X ×[S] Y` is represented by the
categorical pullback, with projections `p₁` and `p₂`.

The point of this file is not to replace Mathlib's pullback API. It gives the Fourier–Mukai
project stable names for the product geometry that will later support the two projections
appearing in an integral transform.
-/

namespace FourierMukai

open CategoryTheory Limits AlgebraicGeometry

universe u

noncomputable section

namespace RelativeProduct

variable {S X Y T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The relative product `X ×[S] Y`. -/
abbrev obj : Scheme.{u} := pullback f g

/-- The first projection `X ×[S] Y ⟶ X`. -/
abbrev p₁ : obj f g ⟶ X := pullback.fst f g

/-- The second projection `X ×[S] Y ⟶ Y`. -/
abbrev p₂ : obj f g ⟶ Y := pullback.snd f g

/-- The defining commutative square of the relative product. -/
@[reassoc]
lemma condition : p₁ f g ≫ f = p₂ f g ≫ g := pullback.condition

/-- The universal map into a relative product. -/
def lift (a : T ⟶ X) (b : T ⟶ Y) (h : a ≫ f = b ≫ g) : T ⟶ obj f g :=
  pullback.lift a b h

@[simp, reassoc]
lemma lift_p₁ (a : T ⟶ X) (b : T ⟶ Y) (h : a ≫ f = b ≫ g) :
    lift f g a b h ≫ p₁ f g = a := by
  simp [lift]

@[simp, reassoc]
lemma lift_p₂ (a : T ⟶ X) (b : T ⟶ Y) (h : a ≫ f = b ≫ g) :
    lift f g a b h ≫ p₂ f g = b := by
  simp [lift]

/-- Maps into a relative product are determined by their composites with the two projections. -/
@[ext]
lemma hom_ext {a b : T ⟶ obj f g}
    (h₁ : a ≫ p₁ f g = b ≫ p₁ f g)
    (h₂ : a ≫ p₂ f g = b ≫ p₂ f g) : a = b := by
  apply pullback.hom_ext
  · exact h₁
  · exact h₂

end RelativeProduct

end

end FourierMukai
