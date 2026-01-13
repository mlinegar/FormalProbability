/-!
# Econometrics/Panel: Panel Data

## Overview

This submodule covers panel data models and estimators, including fixed effects,
random effects, and the Hausman specification test.

## Main Results

| Result | File | Notes |
|--------|------|-------|
| Fixed effects | FixedEffects | Within transformation and FE setup |
| Random effects | RandomEffects | RE model and GLS transformation |
| Hausman test | Hausman | FE vs RE specification test |

## File Structure

```
Panel/
├── FixedEffects.lean  # Fixed effects model and estimators
├── RandomEffects.lean # Random effects model and GLS
├── Hausman.lean       # Hausman specification test
└── README.lean        # This file
```

## Key Concepts

### Fixed Effects
Eliminates time-invariant unobserved heterogeneity via within transformation.

### Random Effects
Treats individual effects as random and uncorrelated with regressors.

### Hausman Test
Compares FE and RE estimates to detect correlation between regressors and effects.
-/
