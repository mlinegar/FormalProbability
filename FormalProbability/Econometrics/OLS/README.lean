/-!
# Econometrics/OLS: Ordinary Least Squares

## Overview

This submodule formalizes linear regression via OLS, covering classical
assumptions, finite-sample properties, inference, and asymptotic results.

## Main Results

| Result | File | Notes |
|--------|------|-------|
| Gauss-Markov (BLUE) | GaussMarkov | Classical assumptions and unbiasedness |
| Inference | Inference | t-tests, F-tests, and confidence intervals |
| Asymptotic OLS | AsymptoticOLS | Consistency and asymptotic normality |
| Goodness of fit | RSquared | TSS/ESS/RSS and R-squared |

## File Structure

```
OLS/
├── GaussMarkov.lean   # Classical OLS assumptions and BLUE
├── Inference.lean     # t-tests, F-tests, confidence intervals
├── AsymptoticOLS.lean # Consistency and asymptotic normality
├── RSquared.lean      # Goodness-of-fit measures
└── README.lean        # This file
```

## Key Concepts

### Classical Linear Model
MLR.1-MLR.5 assumptions for unbiasedness and variance formulas.

### Asymptotic Theory
Weak exogeneity and moment conditions that connect to the CLT module.

### Fit Metrics
R-squared decompositions built from TSS, ESS, and RSS.
-/
