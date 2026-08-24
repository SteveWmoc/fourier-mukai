import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Tensoring sheaves of modules

Mathlib equips presheaves of modules over a presheaf of commutative rings with a symmetric
monoidal structure. This file supplies the small adapter needed by this project: tensor the
underlying presheaves of two sheaves of modules and then sheafify.

We package only the one-variable functor needed for an integral transform. A full monoidal
category structure on sheaves, together with its coherence theory, is intentionally outside
the scope of this file.
-/

namespace FourierMukai

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

universe u

noncomputable section

namespace Sheaves

variable (X : Scheme.{u})

/-!
`Scheme.PresheafOfModules` deliberately exposes the structure sheaf only as a presheaf of
rings. The pointwise tensor instance needs the definitionally equal presentation coming from
the presheaf of commutative rings, which this abbreviation records.
-/

/-- Presheaves of modules with the commutative-ring presentation needed by Mathlib's tensor. -/
abbrev MonoidalPresheaves :=
  PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)

/-- The pointwise tensor structure on presheaves of modules over a scheme. -/
local instance monoidalCategoryStructPresheafOfModules :
    MonoidalCategoryStruct X.PresheafOfModules :=
  PresheafOfModules.monoidalCategoryStruct (R := X.sheaf.obj)

/-- The pointwise monoidal category structure on presheaves of modules over a scheme. -/
local instance monoidalCategoryPresheafOfModules : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.sheaf.obj)

/-- Pointwise tensoring of presheaves of modules by a fixed presheaf. -/
def presheafTensorBy (K : X.PresheafOfModules) :
    X.PresheafOfModules ⥤ X.PresheafOfModules :=
  tensorRight K

/-- Sheafification of presheaves of modules on a scheme. -/
def associatedSheaf : X.PresheafOfModules ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

instance : (associatedSheaf X).IsLeftAdjoint := by
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).isLeftAdjoint

/-- Tensor a sheaf of modules on the right by `K`, sheafifying the pointwise presheaf tensor. -/
def tensorBy (K : X.Modules) : X.Modules ⥤ X.Modules :=
  Scheme.Modules.toPresheafOfModules X ⋙
    presheafTensorBy X ((Scheme.Modules.toPresheafOfModules X).obj K) ⋙
      associatedSheaf X

section Additive

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

instance : (associatedSheaf X).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

instance : (Scheme.Modules.toPresheafOfModules X).Additive where
  map_add := by
    intros
    rfl

instance (K : X.PresheafOfModules) : (presheafTensorBy X K).Additive := by
  change (tensorRight (show MonoidalPresheaves X from K)).Additive
  exact Functor.additive_of_preservesBinaryBiproducts _

instance (K : X.Modules) : (tensorBy X K).Additive := by
  dsimp [tensorBy]
  infer_instance

end Additive

@[simp]
lemma presheafTensorBy_obj (K M : X.PresheafOfModules) :
    (presheafTensorBy X K).obj M = PresheafOfModules.Monoidal.tensorObj M K :=
  rfl

@[simp]
lemma presheafTensorBy_map (K : X.PresheafOfModules) {M N : X.PresheafOfModules}
    (φ : M ⟶ N) :
    (presheafTensorBy X K).map φ =
      PresheafOfModules.Monoidal.tensorHom φ (𝟙 K) :=
  rfl

@[simp]
lemma tensorBy_obj (K M : X.Modules) :
    (tensorBy X K).obj M =
      (associatedSheaf X).obj
        (PresheafOfModules.Monoidal.tensorObj
          ((Scheme.Modules.toPresheafOfModules X).obj M)
          ((Scheme.Modules.toPresheafOfModules X).obj K)) :=
  rfl

@[simp]
lemma tensorBy_map (K : X.Modules) {M N : X.Modules} (φ : M ⟶ N) :
    (tensorBy X K).map φ =
      (associatedSheaf X).map
        (PresheafOfModules.Monoidal.tensorHom
          ((Scheme.Modules.toPresheafOfModules X).map φ)
          (𝟙 ((Scheme.Modules.toPresheafOfModules X).obj K))) :=
  rfl

end Sheaves

end

end FourierMukai
