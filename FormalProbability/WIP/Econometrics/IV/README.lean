/-!
# WIP/Econometrics/IV: Instrumental Variables (work in progress)

## Overview

Work in progress: these modules are not imported by the root module, and many of their
statements are still placeholders.

This submodule is intended to formalize instrumental variables estimation, including 2SLS,
identification conditions, and weak instrument diagnostics.

## Planned Scope

| Result | File | Notes |
|--------|------|-------|
| Two-stage least squares | TwoSLS | 2SLS setup and formulas |
| Identification | Identification | Order and rank conditions |
| Weak instruments | WeakInstruments | Bias and robustness issues |

## File Structure

```
IV/
├── TwoSLS.lean          # Two-stage least squares
├── Identification.lean  # Order/rank identification conditions
├── WeakInstruments.lean # Weak instrument diagnostics
└── README.lean          # This file
```

## Key Concepts

### Instrument Validity
Instruments must be relevant (correlated with endogenous regressors) and exogenous.

### Identification
Order and rank conditions ensure parameters are uniquely identified.

### Weak Instruments
Low first-stage strength leads to bias and unreliable inference.
-/
