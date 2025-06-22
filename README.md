# Fourier–Mukai in Lean 4

[![Lean CI](https://github.com/SteveWmoc/fourier-mukai/actions/workflows/ci.yml/badge.svg)](https://github.com/SteveWmoc/fourier-mukai/actions)

This project aims to formalize the Fourier–Mukai transform — a fundamental equivalence in derived algebraic geometry — in Lean 4 using [mathlib4](https://github.com/leanprover-community/mathlib4). It is the first step in a broader plan to explore aspects of the Geometric Langlands Program in a formalized, verifiable way.

---

## Project Goals

- Set up a Lean 4 + mathlib4 project with continuous integration (done)
- Formalize concrete geometric examples: affine and projective lines, line bundles
- Build infrastructure for derived functors, kernels, and integral transforms
- Formalize the Fourier–Mukai equivalence on abelian varieties (starting with elliptic curves)
- Lay groundwork for selected cases of the Geometric Langlands Conjecture

---

## Directory Structure

FourierMukai/ ├── Basic.lean              -- Common definitions ├── SchemeBasics.lean       -- Affine, projective, and quasi-coherent sheaves ├── LineBundles.lean        -- Construction and properties of ??(n) ├── IntegralTransform.lean  -- Functorial formalization of Fourier–Mukai (planned)

---

## How to Build

Make sure you have [elan](https://leanprover-community.github.io/get_started.html) and [lake](https://github.com/leanprover/lake) installed.

Then run:

lake build

To fetch `mathlib4`:

lake update

---

## Contributing

This project is experimental, but contributions and collaboration are welcome. If you're interested in derived geometry, category theory, or the Langlands program and want to help formalize advanced mathematics in Lean, please get in touch.

---

## License

[MIT](./LICENSE)

---

## Acknowledgments

- [mathlib4](https://github.com/leanprover-community/mathlib4)
- Jacob Lurie, Alexander Grothendieck, and the Langlands community
- Dennis Gaitsgory and collaborators for their work on Geometric Langlands
