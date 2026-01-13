# FormalProbability (Lean 4)

Standalone Lean formalizations for probability, econometrics, DSL, and ML modules.
The `FormalProbability/CLT` subtree includes a CLT development via characteristic functions
and Lévy continuity.

## Prior Work and Attribution

- Remy Degenne's Lean CLT development (https://github.com/RemyDegenne/CLT) significantly predates
  this effort; this project is later and gives full credit to that earlier work.
- The first formalized CLT (Isabelle/HOL, 2014) is Jeremy Avigad, Johannes Hoelzl, and Luke Serafin,
  "A formally verified proof of the Central Limit Theorem" (arXiv:1405.7012v4). That paper was
  explicitly provided to the AI assistants used to draft parts of this development.

## Build

```bash
lake build FormalProbability
```

## CLT Status

- Bounded and finite-variance i.i.d. CLT are formalized.
- User-facing theorems live in `FormalProbability/CLT/CLT.lean`:
  - `central_limit_theorem_iid_finite_variance`
  - `central_limit_theorem_iid_abs_pow3`
  - `central_limit_theorem_iid_bounded`
  - `central_limit_theorem_cdf_iid_bounded`
  - `central_limit_theorem_iid_of_charFunScale`
  - `CharFunCLTScale_of_integrable_sq`
  - `CharFunCLTScale_of_integrable_abs_pow3`
- Analytic infrastructure is in `FormalProbability/CLT/LevyContinuity.lean`.
