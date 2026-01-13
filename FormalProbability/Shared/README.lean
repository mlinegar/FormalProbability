/-!
# Shared Module: Common Infrastructure

## Overview

Shared definitions and configuration used across the FormalProbability modules.
This directory keeps cross-cutting utilities in one place to avoid duplication.

## File Structure

```
Shared/
├── Config.lean             # Project-wide Lean options and lint settings
├── BoundedMetricSpace.lean # Bounded (pseudo)metric typeclasses and helpers
└── README.lean             # This file
```

## Key Concepts

### BoundedPseudoMetricSpace
A pseudo metric space with a global distance bound, used to justify summability
and boundedness assumptions in probability and learning results.

### UnitBoundedPseudoMetricSpace
A specialization where the diameter bound is exactly 1, convenient for
normalized losses and indicator-style metrics.

### BoundedMetricSpace
The metric-space variant with the same boundedness guarantees when equality
from zero distance is needed.

## Notes

- Shared configuration is centralized in `Config.lean` and imported as needed.
-/
