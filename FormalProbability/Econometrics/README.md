# Econometrics: potential outcomes, IPW identification, and OLS

- **Potential outcomes and IPW.** `Core` sets up binary treatment, potential outcomes, the
  observed outcome, and the average treatment effect. `Assumptions` states consistency,
  unconfoundedness (as conditional mean independence), and positivity. `PropensityScore`
  constructs e(X) = E[D | X] as a measurable function of the covariates via Doob-Dynkin
  factorization. `IPWIdentification` proves that, under these assumptions and
  integrability, inverse probability weighting identifies the average treatment effect
  (`ipw_identifies_ATE`).
- **Finite-sample OLS.** `OLS/GaussMarkov` proves that OLS is unbiased under a fixed
  design with mean-zero errors, derives its variance under homoskedasticity, and proves
  the Gauss-Markov theorem (`ols_unbiased`, `ols_variance_formula`, `gauss_markov`).
  `OLS/RSquared` proves the sum-of-squares decomposition and the usual facts about
  R-squared (`tss_decomposition`, `rsquared_bounds`, `rsquared_is_squared_correlation`).

Drafts for OLS inference and asymptotics, instrumental variables, panel data, and
regression diagnostics live in [`../WIP/Econometrics`](../WIP/Econometrics) and are not
part of the default build.
