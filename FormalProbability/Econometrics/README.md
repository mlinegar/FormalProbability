# Econometrics: potential outcomes, IPW identification, and an OLS/IV/panel scaffold

**Built.** `Econometrics.lean` imports four modules, and all four are fully proved.

- `Core`: treatment, potential outcomes, observed outcome, ATE.
- `Assumptions`: consistency, unconfoundedness as conditional mean independence,
  positivity.
- `PropensityScore`: e(X) = E[D | X], with Doob-Dynkin factorization.
- `IPWIdentification`: `ipw_identifies_ATE`.

**Not built.** The subdirectories `OLS/`, `IV/`, `Panel/`, and `Diagnostics/` are not
imported by `Econometrics.lean` or by the root module, so `lake build` does not check them.

- They are an early scaffold. Of their 125 theorems, 74 are placeholders: the conclusion is
  `True`, or the proof returns an identical hypothesis.
- Another 9, in `OLS/AsymptoticOLS`, are conditional on `OLSAsymptoticAxioms`.
- `OLS/GaussMarkov` contains real proofs (`ols_unbiased`, `ols_variance_formula`,
  `gauss_markov`), and so does part of `OLS/RSquared` (`tss_decomposition`).

For per-module results and status, see the
[module map](../../README.md#causal-inference-and-econometrics-econometrics). The import
graph and the list of placeholder theorems are in
[docs/OVERVIEW.md](../../docs/OVERVIEW.md).
