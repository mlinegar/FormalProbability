/-!
# CLT Module: Central Limit Theorem

## Overview

This module formalizes the **Central Limit Theorem** and supporting probability theory.
It provides the measure-theoretic foundations for asymptotic analysis.

## Prior Work and Attribution

This CLT development comes after and is independent of earlier formalizations.
We give full credit to those efforts and make the sources explicit.

- Remy Degenne's Lean formalization (https://github.com/RemyDegenne/CLT) significantly predates
  this work.
- The Isabelle/HOL formalization in 2014 (Jeremy Avigad, Johannes Hoelzl, Luke Serafin,
  "A formally verified proof of the Central Limit Theorem", arXiv:1405.7012v4) was explicitly
  provided to the AI assistants used to draft parts of this development.

## Main Results

| Theorem | File | Statement |
|---------|------|-----------|
| Helly Selection | HellySelection | Tight sequences have convergent subsequences |
| Lévy Continuity | LevyContinuity | Characteristic function convergence ⟹ distribution convergence |
| CLT | CLT | i.i.d. CLT under finite variance (`central_limit_theorem_iid_finite_variance`) |

## File Structure

```
CLT/
├── Core.lean           # Basic probability definitions
├── ProbabilityLaws.lean # Laws, transfer theorem, total probability
├── Distributions.lean  # Binomial/Geometric/Poisson/Uniform/Exponential/Gaussian
├── GeneratingFunctions.lean # PGF and sums of independent RVs
├── WeakLaw.lean        # Weak law of large numbers
├── Normal.lean         # Normal distribution properties
├── HellySelection.lean # Helly's selection theorem (tightness)
├── LevyContinuity.lean # Lévy's continuity theorem
└── CLT.lean            # Central Limit Theorem
```

## Key Concepts

### Tightness

A sequence of probability measures {μ_n} is **tight** if:
```
∀ε > 0, ∃K compact: μ_n(K) > 1 - ε for all n
```

### Characteristic Functions

The characteristic function of μ is:
```
φ_μ(t) = E[exp(itX)] = ∫ exp(itx) dμ(x)
```

### Lévy Continuity Theorem

Formalized form (`tendsto_probabilityMeasure_of_tendsto_charFun`): if φ_{μ_n} → φ_μ
pointwise for a probability measure μ, then μ_n ⟹ μ (weak convergence). The stronger form,
where the limit φ is only assumed continuous at 0 and is shown to be a characteristic
function, is not formalized here.

### Central Limit Theorem

For i.i.d. X_i with E[X_0] = 0 and E[X_0^2] = σ² (`CLTAssumptions`):
```
(1/√n) Σ_{i<n} X_i ⟹ N(0, σ²)
```
The Lindeberg-Feller CLT for triangular arrays is not formalized here.

## Axioms Used

This module uses no axioms beyond Mathlib foundations.

## References

- Avigad, J., Hoelzl, J., Serafin, L. (2014). A formally verified proof of the Central Limit Theorem.
  arXiv:1405.7012v4.
- Billingsley, P. (1995). Probability and Measure, 3rd ed.
- Dudley, R.M. (2002). Real Analysis and Probability
- Degenne, R. Lean CLT formalization (GitHub repository: https://github.com/RemyDegenne/CLT).
-/
