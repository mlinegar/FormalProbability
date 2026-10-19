/-!
# Econometrics/OLS: finite-sample ordinary least squares

## Overview

Linear regression under the classical assumptions with a fixed design matrix.

| Result | File | Declarations |
|--------|------|--------------|
| Unbiasedness and variance | GaussMarkov | `ols_unbiased`, `ols_variance_formula` |
| Gauss-Markov (BLUE) | GaussMarkov | `gauss_markov_matrix`, `gauss_markov` |
| Sum-of-squares decomposition | RSquared | `tss_decomposition` |
| R-squared | RSquared | `rsquared_bounds`, `rsquared_is_squared_correlation` |

## File structure

```
OLS/
├── GaussMarkov.lean   # classical assumptions, unbiasedness, variance, BLUE
├── RSquared.lean      # TSS/ESS/RSS, R-squared, adjusted and partial R-squared
└── README.lean        # this file
```

OLS inference (t and F statistics) and asymptotic OLS are drafts in
`FormalProbability/WIP/Econometrics/OLS`.
-/
