/-!
# Econometrics/IV: Instrumental Variables

## Overview

This submodule formalizes instrumental variables estimation, including 2SLS,
identification conditions, and weak instrument diagnostics.

## Main Results

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
