# Blueprint: Formalizing the Fourier–Mukai Transform in Lean 4

## Project Goal

To formalize the **Fourier–Mukai transform** in Lean 4, beginning with the case of elliptic curves, and ultimately prove the equivalence of derived categories of abelian varieties and their duals via the Fourier–Mukai functor.

---

## 0. Foundation

- [ ] **Categories and Abelian Categories**
  - [ ] Ensure Mathlib4 category theory and abelian category API is sufficient
  - [ ] Add missing lemmas or instances as needed

---

## 1. Homological Algebra

- [ ] **Chain Complexes & Derived Categories**
  - [ ] Review Mathlib4's existing formalization
  - [ ] Adapt or extend bounded derived categories if needed
  - [ ] Add derived functors: Rf_*, Lf^*, derived tensor product

---

## 2. Algebraic Geometry Basics

- [ ] **Elliptic Curves**
  - [ ] Define an elliptic curve (using or adapting Mathlib4)
  - [ ] Prove basic properties: smoothness, group law, etc.

- [ ] **Sheaves and Coherent Sheaves**
  - [ ] Formalize coherent sheaves for elliptic curves
  - [ ] (Optional, for abelian varieties) Extend to general varieties

- [ ] **Line Bundles and Poincaré Bundle**
  - [ ] Define line bundles on E, E \times E
  - [ ] Formalize/axiomatize the Poincaré bundle and its universal property

---

## 3. Fourier–Mukai for Elliptic Curves

- [ ] **Define the Fourier–Mukai Functor**
  - [ ] Construction via kernel (Poincaré bundle)
  - [ ] Derived pushforward and pullback

- [ ] **Prove Equivalence**
  - [ ] Prove fully faithful
  - [ ] Prove essentially surjective
  - [ ] Summarize strategy and obstacles

---

## 4. Generalization to Abelian Varieties

- [ ] **Abelian Variety & Dual**
  - [ ] Formalize abelian varieties and duals
  - [ ] Universal property and duality

- [ ] **General Fourier–Mukai Functor**
  - [ ] Definition for general abelian variety

- [ ] **Prove General Equivalence**
  - [ ] Fully faithful
  - [ ] Essentially surjective
  - [ ] Main theorem: FM is an equivalence

---

## Meta and Infrastructure

- [ ] **Mathlib4 Extensions**
  - [ ] List gaps and targets for upstream contributions
- [ ] **Testing and CI**
  - [ ] CI checks for sorried proofs
- [ ] **Documentation**
  - [ ] Docstrings for all public definitions/theorems
  - [ ] Update this blueprint as steps are completed

---

## How to Use This Blueprint

- Each checklist item can be an issue/milestone.
- When a result is fully formalized, check it off.
- Use this as an onboarding doc for new contributors.
- Keep this in sync with actual code and GitHub Projects.

---

**Legend:**  
- [ ] = To do  
- [x] = Done  
- [~] = In progress
