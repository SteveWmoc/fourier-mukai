# Fourier–Mukai

A Lean 4 formalization project aimed at Fourier–Mukai theory, beginning with integral transforms and the elliptic-curve case.

## Strategy

The project is deliberately incremental. Before introducing project-specific abstractions, we compile-test the Mathlib interfaces we expect to need: derived categories, fiber products of schemes, sheaves of modules, quasi-coherence, and pullback/pushforward machinery.

The guiding formula is

\[
\Phi_{\mathcal P}(-) = R p_{2*}\bigl(p_1^*(-) \otimes \mathcal P\bigr).
\]

The first long-term target is the Fourier–Mukai transform for elliptic curves. Generic infrastructure should be introduced only when a concrete theorem requires it.

## Current milestone

Establish the minimal Mathlib interface required for an integral transform. See Issue #1.

## Build

```sh
lake update
lake exe cache get
lake build
```

The project pins a stable Mathlib release so that CI and local development use the same Lean/Mathlib pair.
