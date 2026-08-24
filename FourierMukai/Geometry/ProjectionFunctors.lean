import FourierMukai.Geometry.RelativeProduct
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Module functors along relative-product projections

For a relative product `X ×[S] Y`, this file gives stable project-level names to the
pullback and pushforward functors attached to the two projections. These are the functorial
ingredients appearing in an underived integral transform:

`F ↦ p₂* (p₁^* F ⊗ K)`.

Tensoring with a kernel is deliberately left to a later layer.
-/

namespace FourierMukai

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace RelativeProduct

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Pullback of sheaves of modules along the first projection. -/
def pullback₁ : X.Modules ⥤ (obj f g).Modules :=
  Scheme.Modules.pullback (p₁ f g)

/-- Pushforward of sheaves of modules along the first projection. -/
def pushforward₁ : (obj f g).Modules ⥤ X.Modules :=
  Scheme.Modules.pushforward (p₁ f g)

/-- Pullback of sheaves of modules along the second projection. -/
def pullback₂ : Y.Modules ⥤ (obj f g).Modules :=
  Scheme.Modules.pullback (p₂ f g)

/-- Pushforward of sheaves of modules along the second projection. -/
def pushforward₂ : (obj f g).Modules ⥤ Y.Modules :=
  Scheme.Modules.pushforward (p₂ f g)

/-- Pullback along the first projection is left adjoint to pushforward. -/
def pullback₁Pushforward₁Adjunction : pullback₁ f g ⊣ pushforward₁ f g :=
  Scheme.Modules.pullbackPushforwardAdjunction (p₁ f g)

/-- Pullback along the second projection is left adjoint to pushforward. -/
def pullback₂Pushforward₂Adjunction : pullback₂ f g ⊣ pushforward₂ f g :=
  Scheme.Modules.pullbackPushforwardAdjunction (p₂ f g)

instance : (pullback₁ f g).IsLeftAdjoint :=
  (pullback₁Pushforward₁Adjunction f g).isLeftAdjoint

instance : (pushforward₁ f g).IsRightAdjoint :=
  (pullback₁Pushforward₁Adjunction f g).isRightAdjoint

instance : (pullback₂ f g).IsLeftAdjoint :=
  (pullback₂Pushforward₂Adjunction f g).isLeftAdjoint

instance : (pushforward₂ f g).IsRightAdjoint :=
  (pullback₂Pushforward₂Adjunction f g).isRightAdjoint

instance : (pullback₁ f g).Additive := by
  dsimp [pullback₁]
  infer_instance

instance : (pushforward₁ f g).Additive := by
  dsimp [pushforward₁]
  infer_instance

instance : (pullback₂ f g).Additive := by
  dsimp [pullback₂]
  infer_instance

instance : (pushforward₂ f g).Additive := by
  dsimp [pushforward₂]
  infer_instance

end RelativeProduct

end

end FourierMukai
