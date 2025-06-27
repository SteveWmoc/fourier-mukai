/-
Copyright (c) 2025 Steven Sabean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Sabean
-/
/-
  CategoryTheory.lean
  This file collects and tests imports from Mathlib4 that are foundational for categorical work in the Fourier–Mukai project.
  It also serves as a reference for contributors to locate relevant structures, classes, and definitions.
  Update and expand as project needs evolve.
-/

import Mathlib.CategoryTheory.Category.Basic    -- Category, Epi, Mono, etc.
import Mathlib.CategoryTheory.Functor.Basic     -- Functor
import Mathlib.CategoryTheory.NatTrans          -- Natural transformation
import Mathlib.CategoryTheory.Equivalence       -- Equivalence, Functor.IsEquivalence
import Mathlib.CategoryTheory.Preadditive.Basic -- Preadditive
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor -- Functor.Additive
import Mathlib.CategoryTheory.Abelian.Basic     -- Abelian
import Mathlib.CategoryTheory.Limits.Shapes.Kernels -- kernel, cokernel
import Mathlib.Algebra.Homology.ShortComplex.Basic    -- ShortComplex
import Mathlib.Algebra.Homology.ShortComplex.Exact -- ShortComplex.Exact

/-!
# Foundational Category Theory for Fourier–Mukai

This module is a checklist and summary of the categorical structures needed for the formalization project.

## Contents
* Categories, functors, natural transformations, equivalences
* (Pre)additive and abelian categories
* Kernels and cokernels
* Short exact sequences (as exact complexes)
-/

open CategoryTheory

section checks

-- Category, morphisms, Epi, Mono
#check Category
#check Epi
#check Mono

-- Functors, natural transformations, equivalence
#check Functor
#check NatTrans
#check Equivalence
#check Functor.IsEquivalence

-- Preadditive (additive structure on Hom-sets)
#check Preadditive

-- Abelian categories
#check Abelian

-- Additive functors
#check Functor.Additive

-- Kernel and cokernel (limits)
#check kernel
#check cokernel

-- Short complexes and exactness (for "short exact sequence")
#check ShortComplex
#check ShortComplex.Exact

end checks

/-!
## What’s here, what’s missing?

- `Category`, `Epi`, `Mono`, `Functor`, `NatTrans`, `Equivalence`, `Preadditive`, `Abelian`, and (co)kernels are available as of this writing.
- There is no dedicated `Additive` class (but see `Preadditive` and `Functor.Additive`).
- Short exact sequences are represented as exact `ShortComplex`s, not as a separate `ShortExactSequence` structure.
- Triangulated categories and derived functors may require further exploration or extensions as the project progresses.

## Next steps

- Confirm that all imports compile.
- For additional category-theoretic needs, consult the [Mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/CategoryTheory.html).
- Expand this file as deeper properties (like projectives/injectives, or more homological algebra) are needed.
- Upstream any general improvements to Mathlib4 where appropriate.

-/
