/-!
# CLT: probability foundations and the central limit theorem

## Overview

This area builds, on top of Mathlib, the probability needed for a proof of the classical
i.i.d. central limit theorem by characteristic functions. `Core` also provides the shared
probability vocabulary (expectation, i.i.d. sequences, sample means, modes of convergence)
used by the econometrics, DSL, and ML areas.

## Main results

| Result | File | Declaration |
|--------|------|-------------|
| Helly selection | HellySelection | `exists_subseq_tendsto_cdf_rat` |
| Lévy continuity (limit given as a probability measure) | LevyContinuity | `tendsto_probabilityMeasure_of_tendsto_charFun` |
| Weak law of large numbers | WeakLaw | `weak_law_of_large_numbers` |
| i.i.d. CLT with finite variance | CLT | `central_limit_theorem_iid_finite_variance` |

## File structure

```
CLT/
├── Core.lean                # expectation, i.i.d., sample means, convergence notions
├── ProbabilityLaws.lean     # laws, transfer theorem, total probability
├── Distributions.lean       # binomial, geometric, Poisson, uniform, exponential, Gaussian
├── GeneratingFunctions.lean # probability generating functions and independent sums
├── WeakLaw.lean             # weak law of large numbers
├── Normal.lean              # standard normal and its characteristic function
├── HellySelection.lean      # Helly's selection theorem
├── LevyContinuity.lean      # Lévy's continuity theorem
└── CLT.lean                 # central limit theorem
```

## Key concepts

The characteristic function of a probability measure μ is φ_μ(t) = ∫ exp(itx) dμ(x).
`tendsto_probabilityMeasure_of_tendsto_charFun` shows that if φ_{μ_n} → φ_μ pointwise for a
probability measure μ, then μ_n converges weakly to μ. The stronger form, in which the
limit is only assumed continuous at 0, is not formalized here.

For i.i.d. X_i with E[X_0] = 0 and E[X_0²] = σ² (`CLTAssumptions`), the CLT states that the
law of (1/√n) Σ_{i<n} X_i converges weakly to N(0, σ²). The Lindeberg-Feller CLT for
triangular arrays is not formalized here.

## References

- Avigad, J., Hölzl, J., Serafin, L. A formally verified proof of the Central Limit
  Theorem. arXiv:1405.7012.
- Degenne, R. Lean CLT formalization, https://github.com/RemyDegenne/CLT.
- Billingsley, P. (1995). Probability and Measure, 3rd ed.
- Dudley, R. M. (2002). Real Analysis and Probability.
-/
