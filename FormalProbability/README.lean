/-!
# FormalProbability: Module Index

## Overview

This directory contains the Lean modules for probability, econometrics, DSL, and ML.
Each subdirectory includes a README.lean blueprint with scope, results, and file maps.

## Module Layout

```
FormalProbability/
├── CLT/              # Central Limit Theorem development
├── DSL/              # Design-based supervised learning (Egami et al.)
├── Econometrics/     # Econometrics foundations and submodules
├── ML/               # Supervised learning foundations
├── Shared/           # Shared configuration and typeclasses
├── CLT.lean          # CLT module entry point
├── DSL.lean          # DSL module entry point
├── Econometrics.lean # Econometrics module entry point
├── ML.lean           # ML module entry point
└── README.lean       # This file
```

## Notes

- Shared Lean options live in `Shared/Config.lean`.
- Subdirectories document their own scope and results.
-/
