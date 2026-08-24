# Integral-transform capability map

This map records what has been compile-tested against the pinned Mathlib release and what
still requires project code. It is a working boundary map, not a long-range blueprint.

## Available in Mathlib

| Capability | Interface used here | Status |
| --- | --- | --- |
| Derived categories | `DerivedCategory` and `DerivedCategory.Q` | Available; basic construction audited |
| Relative products | categorical pullbacks in `Scheme` | Available; wrapped by `RelativeProduct` |
| Projection morphisms | `pullback.fst` and `pullback.snd` | Available; exposed as `p₁` and `p₂` |
| Sheaves of modules | `Scheme.Modules` | Available and abelian |
| Pullback and pushforward | `Scheme.Modules.pullback` / `pushforward` | Available; projection adapters added |
| Pullback–pushforward adjunction | `Scheme.Modules.pullbackPushforwardAdjunction` | Available for both projections |
| Quasi-coherence | `SheafOfModules.IsQuasicoherent` | Available; preservation hypotheses still need auditing |
| Presheaf tensor products | symmetric monoidal structure on `PresheafOfModules` | Available |
| Sheafification of modules | `PresheafOfModules.sheafification` | Available |
| Bounded-below right-derived functors | `Functor.rightDerivedFunctorPlus` | Available given enough injectives |

## Project adapters

| Adapter | Purpose |
| --- | --- |
| `RelativeProduct` | Stable names for `X ×[S] Y`, `p₁`, `p₂`, lifts, and extensionality |
| `RelativeProduct.pullback₁` / `pushforward₂` | The projection functors occurring in an integral transform |
| `Sheaves.tensorBy` | Tensor underlying presheaves with a fixed kernel and sheafify |
| `IntegralTransform.underived` | The functor `M ↦ p₂* (p₁* M ⊗ K)` |

## Remaining derived boundary

The underived pipeline is now explicit. The next stage must establish, rather than assume:

1. preservation of quasi-coherence by each operation under appropriate geometric hypotheses;
2. exactness of tensoring by a locally free rank-one kernel;
3. exactness of pullback along a flat first projection;
4. a scheme-module specialization of right-derived pushforward;
5. comparison between the derived composite and the intended formula
   `R p₂* (L p₁* (-) ⊗ᴸ K)`.

The elliptic-curve specialization additionally needs a scheme-theoretic elliptic curve, its
dual, and a Poincaré line bundle. These are genuine later mathematical layers, not prerequisites
for defining the generic underived transform.
