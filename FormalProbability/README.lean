/-!
# FormalProbability: module index

Lean modules for probability, econometrics, design-based supervised learning, and basic
machine learning. Each area has an entry-point module that imports all of its built files,
and each directory has a `README.lean` (and usually a `README.md`) describing its scope.

```
FormalProbability/
├── CLT/              # probability foundations and the central limit theorem
├── Econometrics/     # potential outcomes, IPW identification, finite-sample OLS
├── DSL/              # design-based supervised learning; IPW, clustered variance, judges
├── ML/               # risk, ERM, decision trees
├── Shared/           # bounded metric space typeclasses
├── WIP/              # work in progress, not imported by the root module
├── CLT.lean          # area entry points
├── Econometrics.lean
├── DSL.lean
├── ML.lean
└── README.lean       # this file
```

Project-wide Lean options are set in `lakefile.toml`.
-/
