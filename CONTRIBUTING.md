# Contributing to Fourier-Mukai Transform in Lean 4

Thank you for your interest in contributing to the formalization of the Fourier-Mukai transform! This project welcomes contributions from mathematicians, Lean 4 users, and anyone interested in formal verification of advanced mathematics.

## Table of Contents

- [Getting Started](#getting-started)
- [Types of Contributions](#types-of-contributions)
- [Mathematical Guidelines](#mathematical-guidelines)
- [Code Style and Standards](#code-style-and-standards)
- [Development Workflow](#development-workflow)
- [Documentation Requirements](#documentation-requirements)
- [Testing and Verification](#testing-and-verification)
- [Community Guidelines](#community-guidelines)
- [Getting Help](#getting-help)

## Getting Started

### Prerequisites

Before contributing, ensure you have:
- **Mathematical Background**: Familiarity with algebraic geometry, category theory, or homological algebra
- **Lean 4 Experience**: Basic understanding of Lean 4 syntax and mathlib4 conventions
- **Development Setup**: Working Lean 4 installation with VS Code extension

### First Steps

1. **Explore the codebase**: Familiarize yourself with the existing structure
2. **Check open issues**: Look for issues labeled `good first issue` or `help wanted`
3. **Join the community**: Connect with us on [Lean Zulip](https://leanprover.zulipchat.com/)
4. **Read the roadmap**: Understand our current priorities and planned development

## Types of Contributions

### 🧮 Mathematical Formalization
- **Core theory**: Definitions, theorems, and proofs related to Fourier-Mukai transforms
- **Examples**: Concrete instances (elliptic curves, projective spaces, etc.)
- **Infrastructure**: Categorical foundations, derived categories, sheaf theory

### 📚 Documentation
- **Mathematical exposition**: Explaining concepts for different audiences
- **Code documentation**: Docstrings, comments, and usage examples  
- **Tutorials**: Step-by-step guides for using the library

### 🔧 Infrastructure
- **Build system**: Lake configuration, CI/CD improvements
- **Testing**: Property-based tests, example verification
- **Tooling**: Scripts, utilities, development aids

### 🐛 Bug Fixes and Improvements
- **Code quality**: Refactoring, performance improvements
- **Error handling**: Better error messages and diagnostics
- **Compatibility**: Keeping up with mathlib4 updates

## Mathematical Guidelines

### Scope and Priorities

**High Priority:**
- Line bundles on projective spaces
- Basic derived category operations
- Integral transforms and their properties
- Concrete Fourier-Mukai equivalences

**Medium Priority:**
- Abelian varieties and their geometry
- Moduli spaces of sheaves
- Stability conditions

**Future Goals:**
- Geometric Langlands connections
- Mirror symmetry applications

### Mathematical Standards

1. **Correctness First**: All mathematical content must be mathematically sound
2. **Reference Literature**: Cite relevant papers and textbooks in comments
3. **Generality vs. Concreteness**: Balance abstract theory with concrete examples
4. **Dependencies**: Minimize dependencies on unproven results when possible

### Suggested Mathematical Structure

When formalizing new concepts:

```lean
-- 1. Import necessary dependencies
import Mathlib.AlgebraicGeometry.Scheme
import FourierMukai.Basic

-- 2. Set up namespace
namespace FourierMukai

-- 3. State definitions clearly
/-- 
A Fourier-Mukai kernel is a coherent sheaf on the product of two varieties
that induces an integral transform between their derived categories.
-/
structure FMKernel (X Y : Scheme) where
  kernel : CoherentSheaf (X ×ₛ Y)
  -- Additional structure...

-- 4. Provide basic properties
lemma FMKernel.basic_property (K : FMKernel X Y) : 
  -- State and prove fundamental properties
  sorry

-- 5. Build up to main theorems
theorem fourier_mukai_equivalence (X Y : AbelianVariety) (P : FMKernel X Y) 
  (h : IsFMEquivalence P) : 
  IsEquivalence (FMTransform P) := by
  sorry

end FourierMukai
```

## Code Style and Standards

### Lean 4 Conventions

Follow [mathlib4 style guidelines](https://leanprover-community.github.io/contribute/style.html):

#### Naming Conventions
- **Types**: `PascalCase` (e.g., `FourierMukaiKernel`)
- **Functions/theorems**: `snake_case` (e.g., `fourier_mukai_transform`)
- **Instances**: `PascalCase` (e.g., `FMKernel.HasFunctor`)
- **Namespaces**: `PascalCase` (e.g., `FourierMukai.LineBundles`)

#### Code Organization
```lean
-- File header with brief description
/-
Copyright (c) 2025 Steve Wmoc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steve Wmoc, [Your Name]

# Fourier-Mukai Kernels

This file defines the basic theory of Fourier-Mukai kernels and their properties.

## Main definitions

* `FMKernel X Y`: A kernel object on X × Y
* `FMTransform`: The associated integral transform

## Main results

* `fourier_mukai_equivalence`: Conditions for FM transforms to be equivalences
-/

-- Imports (grouped logically)
import Mathlib.CategoryTheory.Equivalence
import Mathlib.AlgebraicGeometry.Scheme
import FourierMukai.Basic

-- Namespace
namespace FourierMukai

-- Definitions, then lemmas, then theorems
-- Each with appropriate documentation
```

#### Documentation Standards
- **All public definitions** must have docstrings
- **Complex proofs** should include proof sketches
- **Examples** should accompany abstract definitions
- **Mathematical context** should be provided where helpful

### Code Quality
- **No `sorry`s** in main branch (use `sorry` only in development branches)
- **Minimal assumptions**: Use the weakest reasonable hypotheses
- **Readable proofs**: Prefer structured proofs over tactic soups
- **Performance**: Avoid unnecessary computations in proofs

## Development Workflow

### Branch Strategy
- **`main`**: Stable, building code only  
- **`develop`**: Integration branch for new features
- **Feature branches**: `feature/kernel-theory`, `feature/elliptic-examples`, etc.
- **Fix branches**: `fix/typo-in-docs`, `fix/build-error`, etc.

### Pull Request Process

1. **Create Feature Branch**
   ```bash
   git checkout -b feature/your-contribution
   ```

2. **Make Changes**
   - Write code following style guidelines
   - Add appropriate tests and documentation
   - Ensure code builds: `lake build`

3. **Commit Changes**
   ```bash
   git add .
   git commit -m "feat: add Fourier-Mukai kernel theory
   
   - Define FMKernel structure
   - Prove basic properties
   - Add examples for line bundles"
   ```

4. **Push and Create PR**
   ```bash
   git push origin feature/your-contribution
   ```

5. **PR Requirements**
   - [ ] Code builds successfully (`lake build`)
   - [ ] All new definitions have docstrings
   - [ ] Examples demonstrate usage
   - [ ] Mathematical correctness verified
   - [ ] Follows style guidelines

### Commit Message Format
```
<type>: <brief description>

<optional longer description>

<optional mathematical context or references>
```

**Types**: `feat`, `fix`, `docs`, `style`, `refactor`, `test`, `chore`

## Documentation Requirements

### Docstring Format
```lean
/--
Brief one-line description.

Longer description if needed, explaining mathematical context
and motivation.

## Examples
```lean
example : FMKernel (ProjectiveSpace 1) (ProjectiveSpace 1) :=
  poincare_bundle
```

## References
- [Huybrechts] Fourier-Mukai transforms in algebraic geometry, Chapter 5
-/
def MyDefinition : Type := sorry
```

### Mathematical Documentation
- **Explain motivation**: Why is this definition/theorem important?
- **Provide context**: How does it fit into the broader theory?
- **Give intuition**: What does this mean geometrically or categorically?
- **Reference literature**: Standard sources for the mathematics

## Testing and Verification

### Types of Tests
1. **Compilation tests**: Ensure all code builds
2. **Example verification**: Concrete instances work as expected  
3. **Property tests**: Key mathematical properties hold
4. **Integration tests**: Components work together

### Test Organization
```
test/
├── unit/           -- Individual component tests
├── integration/    -- Cross-component tests  
├── examples/       -- Worked examples
└── performance/    -- Performance benchmarks
```

### Continuous Integration
All pull requests must:
- [ ] Build successfully on CI
- [ ] Pass all existing tests
- [ ] Not introduce performance regressions
- [ ] Meet code coverage requirements (when implemented)

## Community Guidelines

### Communication
- **Be respectful**: We welcome contributors of all backgrounds and experience levels
- **Be patient**: Mathematical formalization can be challenging and time-consuming
- **Be collaborative**: Help others learn and contribute
- **Be constructive**: Provide helpful feedback in reviews

### Code Reviews
- **Focus on correctness**: Mathematical accuracy is paramount
- **Suggest improvements**: Help make code clearer and more maintainable
- **Explain reasoning**: Help others understand your perspective
- **Learn from others**: Code review is a learning opportunity for everyone

### Attribution
- **Credit contributions**: Add yourself to author lists for significant contributions
- **Acknowledge help**: Mention those who provided assistance
- **Respect licenses**: Ensure all contributions are compatible with Apache 2.0

## Getting Help

### Resources
- **[Lean Zulip](https://leanprover.zulipchat.com/)**: `#mathlib4`, `#new members`, `#Is there code for X?`
- **[mathlib4 docs](https://leanprover-community.github.io/mathlib4_docs/)**: API reference
- **[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)**: Tutorial
- **This repository's issues**: Ask project-specific questions

### Getting Mathematical Help
- **Literature**: Consult Huybrechts, Hartshorne, or other standard references
- **Zulip `#algebraic-geometry`**: Ask about mathematical content
- **Issues**: Open issues for mathematical questions or design decisions

### Getting Technical Help
- **Zulip `#new members`**: Basic Lean 4 questions
- **Zulip `#lean4`**: Advanced technical questions
- **Issues**: Report bugs or build problems

## Recognition

Contributors will be:
- **Listed as authors** on files they significantly contribute to
- **Acknowledged** in project documentation and publications
- **Invited** to co-author papers based on this formalization (as appropriate)

Thank you for contributing to the advancement of formal mathematics! Your work helps make advanced algebraic geometry more accessible and verifiable.

---

*For questions about these guidelines or suggestions for improvement, please open an issue or reach out on Zulip.*
