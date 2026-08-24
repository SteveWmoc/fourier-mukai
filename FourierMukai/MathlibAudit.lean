import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Mathlib capability audit

This file is intentionally small. Its purpose is to make the project's first architectural
assumptions executable: if one of these interfaces moves or disappears, CI should tell us
before project-specific Fourier–Mukai code is built on top of it.
-/

namespace FourierMukai.MathlibAudit

#check DerivedCategory
#check DerivedCategory.Q
#check AlgebraicGeometry.Scheme
#check CategoryTheory.Limits.pullback
#check CategoryTheory.Limits.pullback.fst
#check CategoryTheory.Limits.pullback.snd
#check SheafOfModules
#check SheafOfModules.pullback
#check PresheafOfModules.sheafification
#check PresheafOfModules.Monoidal.tensorObj
#check CategoryTheory.Functor.rightDerivedFunctorPlus

end FourierMukai.MathlibAudit
