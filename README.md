# FormalProbability (Lean 4)

Standalone Lean formalizations for probability, econometrics, DSL, and ML modules.
The `FormalProbability/CLT` subtree includes a CLT development via characteristic functions
and Lévy continuity.

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
