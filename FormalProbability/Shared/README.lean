/-!
# Shared: utilities not tied to one area

```
Shared/
├── BoundedMetricSpace.lean # bounded (pseudo)metric space typeclasses
└── README.lean             # this file
```

`BoundedPseudoMetricSpace` is a pseudometric space with a global bound on distances, which
makes boundedness and summability arguments over the space automatic.
`UnitBoundedPseudoMetricSpace` fixes the bound at 1, convenient for normalized losses, and
`BoundedMetricSpace` is the metric-space variant.
-/
