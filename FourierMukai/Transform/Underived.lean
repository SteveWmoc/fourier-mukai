import FourierMukai.Geometry.ProjectionFunctors
import FourierMukai.Sheaves.Tensor

/-!
# Underived integral transforms

Given `X ⟶ S`, `Y ⟶ S`, and a kernel `K` on `X ×[S] Y`, this file constructs the functor

`M ↦ p₂* (p₁^* M ⊗ K)`.

This is the complete underived categorical pipeline. The later derived transform will replace
the relevant operations by derived functors and prove the exactness hypotheses that allow the
remaining operations to pass to derived categories.
-/

namespace FourierMukai

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace IntegralTransform

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Pull back along `p₁` and tensor with the kernel `K`. -/
def pullTensor (K : (RelativeProduct.obj f g).Modules) :
    X.Modules ⥤ (RelativeProduct.obj f g).Modules :=
  RelativeProduct.pullback₁ f g ⋙ Sheaves.tensorBy (RelativeProduct.obj f g) K

/-- The underived integral transform with kernel `K`. -/
def underived (K : (RelativeProduct.obj f g).Modules) : X.Modules ⥤ Y.Modules :=
  pullTensor f g K ⋙ RelativeProduct.pushforward₂ f g

instance (K : (RelativeProduct.obj f g).Modules) : (pullTensor f g K).Additive := by
  dsimp [pullTensor]
  infer_instance

instance (K : (RelativeProduct.obj f g).Modules) : (underived f g K).Additive := by
  dsimp [underived]
  infer_instance

@[simp]
lemma pullTensor_obj (K : (RelativeProduct.obj f g).Modules) (M : X.Modules) :
    (pullTensor f g K).obj M =
      (Sheaves.tensorBy (RelativeProduct.obj f g) K).obj
        ((RelativeProduct.pullback₁ f g).obj M) :=
  rfl

@[simp]
lemma pullTensor_map (K : (RelativeProduct.obj f g).Modules) {M N : X.Modules}
    (φ : M ⟶ N) :
    (pullTensor f g K).map φ =
      (Sheaves.tensorBy (RelativeProduct.obj f g) K).map
        ((RelativeProduct.pullback₁ f g).map φ) :=
  rfl

@[simp]
lemma underived_obj (K : (RelativeProduct.obj f g).Modules) (M : X.Modules) :
    (underived f g K).obj M =
      (RelativeProduct.pushforward₂ f g).obj
        ((Sheaves.tensorBy (RelativeProduct.obj f g) K).obj
          ((RelativeProduct.pullback₁ f g).obj M)) :=
  rfl

@[simp]
lemma underived_map (K : (RelativeProduct.obj f g).Modules) {M N : X.Modules}
    (φ : M ⟶ N) :
    (underived f g K).map φ =
      (RelativeProduct.pushforward₂ f g).map
        ((Sheaves.tensorBy (RelativeProduct.obj f g) K).map
          ((RelativeProduct.pullback₁ f g).map φ)) :=
  rfl

end IntegralTransform

end

end FourierMukai
