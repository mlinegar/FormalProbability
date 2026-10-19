/-!
# WIP/Econometrics/Diagnostics: Model Diagnostics (work in progress)

## Overview

Work in progress: these modules are not imported by the root module, and many of their
statements are still placeholders.

This submodule is intended to collect regression diagnostics and specification checks,
including omitted variable bias, heteroskedasticity, and functional form issues.

## Planned Scope

| Topic | File | Notes |
|-------|------|-------|
| Omitted variable bias | OmittedVariableBias | Bias formulas under misspecification |
| Heteroskedasticity | Heteroskedasticity | Robust inference and tests |
| Functional form | FunctionalForm | Transformations and marginal effects |

## File Structure

```
Diagnostics/
├── OmittedVariableBias.lean # OVB setup and bias formulas
├── Heteroskedasticity.lean  # Heteroskedasticity tests and robust SEs
├── FunctionalForm.lean      # Functional form and transformations
└── README.lean              # This file
```

## Key Concepts

### Omitted Variable Bias
Misspecification bias from leaving out correlated regressors.

### Heteroskedasticity
Variance of errors depends on covariates, invalidating classical SEs.

### Functional Form
Interpretation of log, polynomial, and interaction models.
-/
