# Fourier–Mukai

A Lean 4 formalization project aimed at Fourier–Mukai theory, beginning with integral transforms and the elliptic-curve case.

## Strategy

The project is deliberately incremental. Before introducing project-specific abstractions, we compile-test the Mathlib interfaces we expect to need: derived categories, fiber products of schemes, sheaves of modules, quasi-coherence, and pullback/pushforward machinery.

The guiding formula is

$$
\Phi_{\mathcal P}(-) = R p_{2*}\bigl(p_1^*(-) \otimes \mathcal P\bigr).
$$

The first long-term target is the Fourier–Mukai transform for elliptic curves. Generic infrastructure should be introduced only when a concrete theorem requires it.

## Current status

The repository now has a compile-tested relative product `X ×[S] Y`, its projections,
pullback and pushforward on sheaves of modules, sheafified tensoring by a fixed kernel, and the
generic underived transform

$$
M \longmapsto p_{2*}\bigl(p_1^*M \otimes K\bigr).
$$

The next milestone is the derived upgrade: isolate the exactness and quasi-coherence hypotheses
needed to construct `R p₂* (L p₁* (-) ⊗ᴸ K)`. See
[`docs/CAPABILITY_MAP.md`](docs/CAPABILITY_MAP.md) for the live boundary map.

## Build

```sh
lake update
lake exe cache get
lake build
lake lint
```

The project pins a stable Mathlib release so that CI and local development use the same Lean/Mathlib pair.
